/- Auxiliary Definitions -/
namespace aux
  universes u v

  /- Definitions for counting the number of elements in lists of lists
  -- The order of the following definitions is important -/
  class has_count (α : Type u) := (default : α → ℕ)
  instance default_count (α : Type u) : has_count α := ⟨ (λx, 1) ⟩
  -- First the count method checks if it has been given a list, and if not it falls to its default case
  def count {α : Type u} [hcα : has_count α] : α → ℕ := has_count.default
  def list_count {α : Type u} [hcα : has_count α] : list α → ℕ
  | [] := 0
  | (h::l) := count h + list_count l
  instance has_list_count (α : Type u) [hcα : has_count α] : has_count (list α) := ⟨list_count⟩

  /- Defining what being exponential means in this proof's context -/
  def exp_constraints : ℕ → ℕ → ℕ → Prop
  | p1 p2 q := ( 0 < p1 ) ∧ ( p1 < p2 ) ∧ ( 0 < q )
  def exp_number : ℕ → ℕ → ℕ → ℕ → ℕ
  | exp p1 p2 q := ( p2 ^ exp ^ q ) / ( p1 ^ exp ^ q )
  def list_expoential {α : Type u} [hcα : has_count α] : list α → ℕ → ℕ → ℕ → ℕ → Prop
  | la exp p1 p2 q := ( exp_constraints p1 p2 q ) ∧ ( exp_number exp p1 p2 q < list_count la )

  /- Combinatory postulate about exponentials -/
  constant Main_Combinatory {α : Type} [hcα : aux.has_count α] :
    ∀(lla : list (list α))(exp p1 p2 q : ℕ),
    ( list.length lla ≤ exp ) →
    ( aux.list_expoential lla exp p1 p2 q ) →
    ---------------------------------
    ( ∃(la : list α), la ∈ lla ∧ aux.list_expoential la exp p1 p2 q )

  /- Proving the distributive property of "IF-THEN-ELSE" -/
  lemma ITE_Distribution
    {α : Type u}{β : Type v}
    {IF : Prop}{THEN ELSE : α}
    [decIF : decidable IF]
    :
    ∀(f : α → β),
    ---------------------------
    ( f (ite IF THEN ELSE) = ite IF (f THEN) (f ELSE) )
  := begin
    with_cases { by_cases IFs : IF },
    case pos { simp [IFs] },
    case neg { simp [IFs] }
  end

  /- Useful properties regarding Products -/
  lemma EQ_Prod_iff_EQ_and_EQ
    {α : Type u} {β : Type v}
    :
    ∀{a1 a2 : α}{b1 b2 : β},
    ---------------------------
    ( (a1,b1) = (a2,b2) ) ↔ ( (a1 = a2) ∧ (b1 = b2) )
  | a1 a2 b1 b2 := begin
    have case_to : ∀{a1 a2 : α}{b1 b2 : β}, (a1,b1) = (a2,b2) → (a1 = a2) ∧ (b1 = b2),
    from begin
      assume a1 a2 b1 b2 eq_prod,
      from prod.mk.inj eq_prod
    end,
    have case_from : ∀{a1 a2 : α}{b1 b2 : β}, (a1 = a2) ∧ (b1 = b2) → (a1,b1) = (a2,b2),
    from begin
      assume a1 a2 b1 b2 and_eq,
      simp [and_eq]
    end,
    from iff.intro case_to case_from
  end

  /- Useful properties regarding Lists -/
  lemma Mem_Append
    {α : Type u}
    :
    ∀{a : α}{l1 l2 : list α},
    ---------------------------
    ( list.mem a (l1++l2) ) ↔ ( (list.mem a l1) ∨ (list.mem a l2) )
  | a l1 l2 := by from list.mem_append

  /- Useful properties regarding Natural Numbers -/
  lemma LE_Refl :
    ∀{a : ℕ},
    ---------------------------
    ( a ≤ a )
  | a := by from nat.le_refl a
  lemma LE_SUCC_of_LE :
    ∀{n m : ℕ},
    ( n ≤ m ) →
    ---------------------------
    ( n ≤ nat.succ m )
  | n m := by from nat.le_succ_of_le
  lemma Not_LT_ZERO :
    ∀{a : ℕ},
    ---------------------------
    ¬ ( a < 0 )
  | a := by from nat.not_lt_zero a
  lemma LT_of_LT_of_LE :
    ∀{n m k : ℕ},
    ( n < m ) →
    ( m ≤ k ) →
    ---------------------------
    ( n < k )
  | n m k := by from nat.lt_of_lt_of_le
  lemma EQ_or_SUCC_LE_iff_LE :
    ∀{a b : ℕ},
    ---------------------------
    ( a ≤ b ) ↔ ( (a = b) ∨ (a+1 ≤ b) )
  | a b := begin
    have case_to : ∀{a b : ℕ}, a ≤ b → (a = b) ∨ (a+1 ≤ b),
    from begin
      assume a b le_a_b,
      from nat.eq_or_lt_of_le le_a_b
    end,
    have case_from : ∀{a b : ℕ}, (a = b) ∨ (a+1 ≤ b) → a ≤ b,
    from begin
      assume a b eq_or_succ_le_a_b,
      cases eq_or_succ_le_a_b with eq_a_b succ_le_a_b,
      case or.inl { simp [eq_a_b] },
      case or.inr { from nat.le_of_succ_le succ_le_a_b }
    end,
    from iff.intro case_to case_from
  end
  -- Notice that the other way does not hold true, since 0 = 0 - 1
  lemma EQ_PRED_of_SUCC_EQ :
    ∀{a b : ℕ},
    ( a+1 = b ) →
    ---------------------------------
    ( a = b-1 )
  | a b := begin
    assume eq_succ_a_b,
    rewrite [←eq_succ_a_b, eq_comm],
    from nat.add_sub_cancel a 1
  end
  lemma Not_SUCC_LE_of_ZERO_EQ_SUB :
    ∀{a b : ℕ},
    ( 0 = a-b ) →
    ---------------------------------
    ¬ ( b+1 ≤ a )
  | a b := begin
    assume zero_eq_sub succ_le,
    rewrite [eq_comm] at zero_eq_sub,
    have le_a_b, from nat.le_of_sub_eq_zero zero_eq_sub,
    have le_succ_b_b, from nat.le_trans succ_le le_a_b,
    simp [nat.not_succ_le_self] at le_succ_b_b,
    from le_succ_b_b
  end
  lemma Not_EQ_of_SUCC_EQ_SUB :
    ∀{a b c : ℕ},
    ( c+1 = a-b ) →
    ---------------------------------
    ¬ ( b = a )
  | a b c := begin
    assume succ_eq_sub eq_a_b,
    rewrite [eq_a_b] at succ_eq_sub,
    rewrite [nat.sub_self] at succ_eq_sub,
    simp [nat.add_one_ne_zero] at succ_eq_sub,
    from succ_eq_sub
  end
end aux

/- Leveled/Labeled Ordered Trees -/
namespace llot
  /- Inductive Types -/
  inductive node_option
  | leaf : node_option
  | u_node : node_option
  | lr_node : node_option
  export node_option (leaf u_node lr_node)
  inductive tree
  | leaf (LVL LBL : ℕ) : tree
  | u_node (LVL LBL : ℕ) : tree → tree
  | lr_node (LVL LBL : ℕ) : tree → tree → tree
  export tree (leaf u_node lr_node)
  inductive branch
  | leaf (LVL LBL : ℕ) : branch
  | u_branch (LVL LBL : ℕ) : branch → branch
  | lr_branch (LVL LBL : ℕ) : branch → branch
  export branch (leaf u_branch lr_branch)
  inductive path
  | root : path
  | u_path (LVL LBL : ℕ) : path → path
  | lr_path (LVL LBL : ℕ) : path → path
  export path (root u_path lr_path)

  /- Representation(Message Output) -/
  def tree_repr : tree → string
  | (leaf LVL LBL) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ "⟩"
  | (u_node LVL LBL _) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ ";U⟩"
  | (lr_node LVL LBL _ _) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ ";LR⟩"
  instance has_tree_repr : has_repr (tree) := ⟨tree_repr⟩
  def branch_repr : branch → string
  | (leaf LVL LBL) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ "⟩"
  | (u_branch LVL LBL _) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ ";U⟩"
  | (lr_branch LVL LBL _) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ ";LR⟩"
  instance has_branch_repr : has_repr (branch) := ⟨branch_repr⟩
  def path_repr : path → string
  | (root) := "⟨ROOT⟩"
  | (u_path LVL LBL _) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ ";U⟩"
  | (lr_path LVL LBL _) := "⟨" ++ repr LVL ++ ";" ++ repr LBL ++ ";LR⟩"
  instance has_path_repr : has_repr (path) := ⟨path_repr⟩

  /- Get Methods -/
  def tree_option : tree → node_option
  | (leaf _ _) := leaf
  | (u_node _ _ _) := u_node
  | (lr_node _ _ _ _) := lr_node
  def tree_level : tree → ℕ
  | (leaf LVL _) := LVL
  | (u_node LVL _ _) := LVL
  | (lr_node LVL _ _ _) := LVL
  def tree_label : tree → ℕ
  | (leaf _ LBL) := LBL
  | (u_node _ LBL _) := LBL
  | (lr_node _ LBL _ _) := LBL

  /- Tree Height and Biggest Label -/
  def max_level : tree → ℕ
  | (leaf LVL _) := LVL
  | (u_node LVL _ U) := max LVL (max_level U)
  | (lr_node LVL _ L R) := max LVL ( max (max_level L) (max_level R) )
  def max_label : tree → ℕ
  | (leaf _ LBL) := LBL
  | (u_node _ LBL U) := max LBL (max_label U)
  | (lr_node _ LBL L R) := max LBL ( max (max_label L) (max_label R) )

  /- Defining a way to filter a list of trees by branch, such that only trees with said branch are accepted
  -- For a tree to have a branch, said branch must occur on the tree exactly as is -/
  def is_branch : branch → tree → Prop
  | (leaf BLVL BLBL) (leaf TLVL TLBL) := (BLVL = TLVL ∧ BLBL = TLBL)
  | (u_branch BLVL BLBL BU) (u_node TLVL TLBL TU) := (BLVL = TLVL ∧ BLBL = TLBL) ∧ (is_branch BU TU)
  | (lr_branch BLVL BLBL BLR) (lr_node TLVL TLBL TL TR) := (BLVL = TLVL ∧ BLBL = TLBL) ∧ (is_branch BLR TL ∨ is_branch BLR TR)
  | _ _ := false
  -- Using is_branch as the if clause for list_branch demands a proof that that is_branch is decidable
  instance decidable_is_branch :
    ∀(b : branch)(t : tree),
    ---------------------------------
    decidable (is_branch b t)
  | (leaf BLVL BLBL) (leaf TLVL TLBL) := begin
    simp [is_branch],
    from @and.decidable (BLVL = TLVL) (BLBL = TLBL) (@nat.decidable_eq BLVL TLVL) (@nat.decidable_eq BLBL TLBL)
  end
  | (leaf _ _) (u_node _ _ _) := is_false not_false
  | (leaf _ _) (lr_node _ _ _ _) := is_false not_false
  | (u_branch _ _ _) (leaf _ _) := is_false not_false
  | (u_branch BLVL BLBL BU) (u_node TLVL TLBL TU) := begin
    simp [is_branch],
    have dec_and, from @and.decidable (BLVL = TLVL) (BLBL = TLBL) (@nat.decidable_eq BLVL TLVL) (@nat.decidable_eq BLBL TLBL),
    from @and.decidable (BLVL = TLVL ∧ BLBL = TLBL) (is_branch BU TU) dec_and (decidable_is_branch BU TU)
  end
  | (u_branch _ _ _) (lr_node _ _ _ _) := is_false not_false
  | (lr_branch _ _ _) (leaf _ _) := is_false not_false
  | (lr_branch _ _ _) (u_node _ _ _) := is_false not_false
  | (lr_branch BLVL BLBL BLR) (lr_node TLVL TLBL TL TR) := begin
    simp [is_branch],
    have dec_and, from @and.decidable (BLVL = TLVL) (BLBL = TLBL) (@nat.decidable_eq BLVL TLVL) (@nat.decidable_eq BLBL TLBL),
    have dec_or, from @or.decidable (is_branch BLR TL) (is_branch BLR TR) (decidable_is_branch BLR TL) (decidable_is_branch BLR TR),
    from @and.decidable (BLVL = TLVL ∧ BLBL = TLBL) (is_branch BLR TL ∨ is_branch BLR TR) dec_and dec_or
  end
  def list_branch : branch → list (path × tree) → list (path × tree)
  | _ [] := []
  | b (⟨hp,ht⟩::lpt) := if is_branch b ht then [⟨hp,ht⟩] ++ list_branch b lpt else list_branch b lpt

  /- Defining a way to select nodes by path, such that only the nodes resulting from said path are chosen
  -- For a node to result from a given path, it must be connected to one of its ancestors by said path -/
  def is_path : path → path → Prop
  | root _ := true
  | (u_path XLVL XLBL XPTH) (u_path YLVL YLBL YPTH) := (XLVL = YLVL ∧ XLBL = YLBL) ∧ (is_path XPTH YPTH)
  | (lr_path XLVL XLBL XPTH) (lr_path YLVL YLBL YPTH) := (XLVL = YLVL ∧ XLBL = YLBL) ∧ (is_path XPTH YPTH)
  | _ _ := false
  -- Using is_path as the if clause for list_path_tree demands a proof that that is_path is decidable
  instance decidable_is_path :
    ∀(xp yp : path),
    ---------------------------------
    decidable (is_path xp yp)
  | root root := is_true trivial
  | root (u_path _ _ _) := is_true trivial
  | root (lr_path _ _ _) := is_true trivial
  | (u_path _ _ _) root := is_false not_false
  | (u_path XLVL XLBL XPTH) (u_path YLVL YLBL YPTH) := begin
    simp [is_path],
    have dec_and, from @and.decidable (XLVL = YLVL) (XLBL = YLBL) (@nat.decidable_eq XLVL YLVL) (@nat.decidable_eq XLBL YLBL),
    from @and.decidable (XLVL = YLVL ∧ XLBL = YLBL) (is_path XPTH YPTH) dec_and (decidable_is_path XPTH YPTH)
  end
  | (u_path _ _ _) (lr_path _ _ _) := is_false not_false
  | (lr_path _ _ _) root := is_false not_false
  | (lr_path _ _ _) (u_path _ _ _) := is_false not_false
  | (lr_path XLVL XLBL XPTH) (lr_path YLVL YLBL YPTH) := begin
    simp [is_path],
    have dec_and, from @and.decidable (XLVL = YLVL) (XLBL = YLBL) (@nat.decidable_eq XLVL YLVL) (@nat.decidable_eq XLBL YLBL),
    from @and.decidable (XLVL = YLVL ∧ XLBL = YLBL) (is_path XPTH YPTH) dec_and (decidable_is_path XPTH YPTH)
  end
  def list_path_tree : path → path → tree → list (path × tree)
  | pth PTH (leaf LVL LBL) :=
    if is_path pth PTH
    then [⟨pth,leaf LVL LBL⟩]
    else []
  | pth PTH (u_node LVL LBL U) :=
    if is_path pth PTH
    then [⟨pth,u_node LVL LBL U⟩]
    else []
  | pth PTH (lr_node LVL LBL L R) :=
    if is_path pth PTH
    then [⟨pth,lr_node LVL LBL L R⟩]
    else []

  /- For this proof, trees are viewed as lists of nodes(which are also trees)
  -- The lists are arranged in an orderly fashion, splitting the tree by levels, labels, and types of node
  -- It is also possible to register a path between nodes, representing how the lists are connected
  -- This is done through building a path from the root of the tree to each of its nodes during the loop -/
  -- Returns all the nodes in the tree, at a given level, with a specific label, and of a certain type
  def loop_tree_level_label_option : tree → path → path → ℕ → ℕ → node_option → list (path × tree)
  -- Matched node_option with the type of tree constructor
  | (leaf LVL LBL) pth PTH lvl lbl leaf :=
    if (LVL=lvl ∧ LBL=lbl)
    then list_path_tree pth PTH (leaf LVL LBL) --[⟨pth,leaf LVL LBL⟩]
    else []
  | (u_node LVL LBL U) pth PTH lvl lbl u_node :=
    if (LVL=lvl ∧ LBL=lbl)
    then list_path_tree pth PTH (u_node LVL LBL U) --[⟨pth,u_node LVL LBL U⟩]
    else loop_tree_level_label_option U pth (u_path LVL LBL PTH) lvl lbl u_node
  | (lr_node LVL LBL L R) pth PTH lvl lbl lr_node :=
    if (LVL=lvl ∧ LBL=lbl)
    then list_path_tree pth PTH (lr_node LVL LBL L R) --[⟨pth,lr_node LVL LBL L R⟩]
    else loop_tree_level_label_option L pth (lr_path LVL LBL PTH) lvl lbl lr_node
      ++ loop_tree_level_label_option R pth (lr_path LVL LBL PTH) lvl lbl lr_node
  -- Mismatched node_option with the type of tree constructor
  | (leaf _ _) _ _ _ _ _ := []
  | (u_node LVL LBL U) pth PTH lvl lbl opt := loop_tree_level_label_option U pth (u_path LVL LBL PTH) lvl lbl opt
  | (lr_node LVL LBL L R) pth PTH lvl lbl opt := loop_tree_level_label_option L pth (lr_path LVL LBL PTH) lvl lbl opt
                                              ++ loop_tree_level_label_option R pth (lr_path LVL LBL PTH) lvl lbl opt
  def list_tree_level_label_option : tree → path → ℕ → ℕ → node_option → list (path × tree)
  | t pth lvl lbl opt := loop_tree_level_label_option t pth root lvl lbl opt
  -- Returns all the nodes in the tree, at a given level, and with a specific label
  def list_tree_level_label : tree → path → ℕ → ℕ → list (list (path × tree))
  | t pth lvl lbl := [list_tree_level_label_option t pth lvl lbl leaf]
                  ++ [list_tree_level_label_option t pth lvl lbl u_node]
                  ++ [list_tree_level_label_option t pth lvl lbl lr_node]
  -- Returns all the nodes in the tree and at a given level
  def loop_tree_level : tree → path → ℕ → ℕ → list (list (list (path × tree)))
  | t pth lvl 0 := [list_tree_level_label t pth lvl 0]
  | t pth lvl (n+1) := [list_tree_level_label t pth lvl (n+1)]
                    ++ loop_tree_level t pth lvl n
  def list_tree_level : tree → path → ℕ → list (list (list (path × tree)))
  | t pth lvl := loop_tree_level t pth lvl (max_label t)
  -- Returns all the nodes in the tree
  def loop_tree :tree → path → ℕ → list (list (list (list (path × tree))))
  | t pth 0 := [list_tree_level t pth 0]
  | t pth (n+1) := [list_tree_level t pth (n+1)]
                ++ loop_tree t pth n
  def list_tree : tree → path → list (list (list (list (path × tree))))
  | t pth := loop_tree t pth (max_level t)

  /- Restrictions Regarding Trees -/
  -- Trees must have levels, meaning that the amount of nodes at any level determines the amount of nodes at the level above it
  def is_leveled : tree → Prop
  | t := ∀(pth : path)(lvl lbl : ℕ),
         ( (lvl+1) ≤ max_level t ) →
         ( lbl ≤ max_label t ) →
         ---------------------------
         ( aux.list_count (list_tree_level_label_option t pth lvl lbl u_node)
         ≤ aux.list_count (list_tree_level t (u_path lvl lbl pth) (lvl+1)) )
       ∧ ( aux.list_count (list_tree_level_label_option t pth lvl lbl lr_node)
         ≤ aux.list_count (list_tree_level t (lr_path lvl lbl pth) (lvl+1)) )
  -- Given the former definition of levels, trees must also be connected
  -- The following definition of connected also guarantees that two instances of the same node cannot share the same parent
  def is_connected : tree → Prop
  | t := ∀(pth : path)(lvl0 lbl0 lbl1 : ℕ)(opt1 : node_option)(b : branch),
         ( (lvl0+1) ≤ max_level t ) →
         ( lbl0 ≤ max_label t ) →
         ( lbl1 ≤ max_label t ) →
         ---------------------------
         ( aux.list_count (list_branch b (list_tree_level_label_option t (u_path lvl0 lbl0 pth) (lvl0+1) lbl1 opt1)) = 0
         ∨ aux.list_count (list_tree_level_label_option t pth lvl0 lbl0 u_node) = 0
         ∨ aux.list_count (list_branch b (list_tree_level_label_option t (u_path lvl0 lbl0 pth) (lvl0+1) lbl1 opt1))
         = aux.list_count (list_branch (u_branch lvl0 lbl0 b) (list_tree_level_label_option t pth lvl0 lbl0 u_node)) )
       ∧ ( aux.list_count (list_branch b (list_tree_level_label_option t (lr_path lvl0 lbl0 pth) (lvl0+1) lbl1 opt1)) = 0
         ∨ aux.list_count (list_tree_level_label_option t pth lvl0 lbl0 lr_node) = 0
         ∨ aux.list_count (list_branch b (list_tree_level_label_option t (lr_path lvl0 lbl0 pth) (lvl0+1) lbl1 opt1))
         = aux.list_count (list_branch (lr_branch lvl0 lbl0 b) (list_tree_level_label_option t pth lvl0 lbl0 lr_node)) )
  -- Trees must be finite, meaning that there can only be leafs at the highest level of a tree
  def is_finite : tree → Prop
  | t := ∀(pth : path)(lbl : ℕ),
         ( lbl ≤ max_label t ) →
         ---------------------------
         ( aux.list_count (list_tree_level_label_option t pth (max_level t) lbl u_node) = 0 )
       ∧ ( aux.list_count (list_tree_level_label_option t pth (max_level t) lbl lr_node) = 0 )

  /- Proofs regarding the size/height of a tree -/
  lemma Length_Tree :
    ∀(t : tree)(pth : path),
    ---------------------------
    ( list.length (list_tree t pth) = (max_level t)+1 )
  | t := begin
    simp [list_tree],
    induction (max_level t),
    case nat.zero { simp [loop_tree] },
    case nat.succ { simp [loop_tree, ih] }
  end
  lemma Length_Tree_Level:
    ∀(t : tree)(pth : path)(lvl : ℕ),
    ---------------------------
    ( list.length (list_tree_level t pth lvl) = (max_label t)+1 )
  | t pth lvl := begin
    simp [list_tree_level],
    induction (max_label t),
    case nat.zero { simp [loop_tree_level] },
    case nat.succ { simp [loop_tree_level, ih] }
  end
  lemma Length_Tree_Level_Label :
    ∀(t : tree)(pth : path)(lvl lbl : ℕ),
    ---------------------------
    ( list.length (list_tree_level_label t pth lvl lbl) = 3 )
  | t pth lvl lbl := by simp [list_tree_level_label]

  lemma From_Level_Label_Option :
    ∀(mp : path)(mt : tree),
    ∀(t : tree)(pth loop : path)(lvl lbl : ℕ)(opt : node_option),
    ( (mp,mt) ∈ loop_tree_level_label_option t pth loop lvl lbl opt ) →
    ---------------------------
    ( (tree_level mt = lvl) ∧ (tree_label mt = lbl) ∧ (tree_option mt = opt) )
  -- When mem and opt are the same
  | mp mt (leaf LVL LBL) pth loop lvl lbl leaf := begin
    assume list_mem,
    -- Simplifying ∈ at the condition(list_mem)
    simp [loop_tree_level_label_option] at list_mem,
    simp [has_mem.mem] at list_mem,
    simp [aux.ITE_Distribution (list.mem (mp,mt))] at list_mem,
    -- Simplifying × at the condition(list_mem)
    simp [list_path_tree] at list_mem,
    simp [aux.ITE_Distribution (list.mem (mp,mt))] at list_mem,
    simp [list.mem] at list_mem,
    -- Cases over (LVL=lvl ∧ LBL=lbl)
    with_cases { by_cases and_eq : (LVL=lvl ∧ LBL=lbl) },
    case pos {
      simp [and_eq] at list_mem,
      -- Cases over (is_path pth)
      with_cases { by_cases is_path : (is_path pth loop) },
      case pos {
        simp [is_path] at list_mem,
        simp [aux.EQ_Prod_iff_EQ_and_EQ] at list_mem,
        simp [list_mem, tree_level, tree_label, tree_option]
      },
      -- The case where ¬(is_path pth loop) is impossible, since ¬((mp,mt) ∈ [])
      case neg { simp [is_path] at list_mem, from false.elim list_mem }
    },
    -- The case where ¬(LVL=lvl ∧ LBL=lbl) is impossible, since ¬((mp,mt) ∈ [])
    case neg { simp [and_eq] at list_mem, from false.elim list_mem }
  end
  | mp mt (u_node LVL LBL U) pth loop lvl lbl u_node := begin
    assume list_mem,
    -- Simplifying ∈ at the condition(list_mem)
    simp [loop_tree_level_label_option] at list_mem,
    simp [has_mem.mem] at list_mem,
    simp [aux.ITE_Distribution (list.mem (mp,mt))] at list_mem,
    -- Simplifying × at the condition(list_mem)
    simp [list_path_tree] at list_mem,
    simp [aux.ITE_Distribution (list.mem (mp,mt))] at list_mem,
    simp [list.mem] at list_mem,
    -- Cases over (LVL=lvl ∧ LBL=lbl)
    with_cases { by_cases and_eq : (LVL=lvl ∧ LBL=lbl) },
    case pos {
      simp [and_eq] at list_mem,
      -- Cases over (is_path pth)
      with_cases { by_cases is_path : (is_path pth loop) },
      case pos {
        simp [is_path] at list_mem,
        simp [aux.EQ_Prod_iff_EQ_and_EQ] at list_mem,
        simp [list_mem, tree_level, tree_label, tree_option]
      },
      -- The case where ¬(is_path pth loop) is impossible, since ¬((mp,mt) ∈ [])
      case neg { simp [is_path] at list_mem, from false.elim list_mem }
    },
    case neg {
      simp [and_eq] at list_mem,
      from From_Level_Label_Option mp mt U pth (u_path LVL LBL loop) lvl lbl u_node list_mem
    }
  end
  | mp mt (lr_node LVL LBL L R) pth loop lvl lbl lr_node := begin
    assume list_mem,
    -- Simplifying ∈ at the condition(list_mem)
    simp [loop_tree_level_label_option] at list_mem,
    simp [has_mem.mem] at list_mem,
    simp [aux.ITE_Distribution (list.mem (mp,mt))] at list_mem,
    -- Simplifying × at the condition(list_mem)
    simp [list_path_tree] at list_mem,
    simp [aux.ITE_Distribution (list.mem (mp,mt))] at list_mem,
    simp [list.mem] at list_mem,
    -- Cases over (LVL=lvl ∧ LBL=lbl)
    with_cases { by_cases and_eq : (LVL=lvl ∧ LBL=lbl) },
    case pos {
      simp [and_eq] at list_mem,
      -- Cases over (is_path pth)
      with_cases { by_cases is_path : (is_path pth loop) },
      case pos {
        simp [is_path] at list_mem,
        simp [aux.EQ_Prod_iff_EQ_and_EQ] at list_mem,
        simp [list_mem, tree_level, tree_label, tree_option]
      },
      -- The case where ¬(is_path pth loop) is impossible, since ¬((mp,mt) ∈ [])
      case neg { simp [is_path] at list_mem, from false.elim list_mem }
    },
    case neg {
      -- Using the relation between append[++] and or[∨] regarding item membership over lists
      simp [and_eq] at list_mem,
      rewrite [aux.Mem_Append] at list_mem,
      cases list_mem with listL_mem listR_mem,
      case or.inl { from From_Level_Label_Option mp mt L pth (lr_path LVL LBL loop) lvl lbl lr_node listL_mem },
      case or.inr { from From_Level_Label_Option mp mt R pth (lr_path LVL LBL loop) lvl lbl lr_node listR_mem }
    }
  end
  -- When mem is a leaf but opt is not
  | mp mt (leaf _ _) _ _ _ _ u_node := by simp [loop_tree_level_label_option]
  | mp mt (leaf _ _) _ _ _ _ lr_node := by simp [loop_tree_level_label_option]
  -- When mem is a u_node but opt is not
  | mp mt (u_node LVL LBL U) pth loop lvl lbl leaf := begin
    simp [loop_tree_level_label_option],
    from From_Level_Label_Option mp mt U pth (u_path LVL LBL loop) lvl lbl leaf
  end
  | mp mt (u_node LVL LBL U) pth loop lvl lbl lr_node := begin
    simp [loop_tree_level_label_option],
    from From_Level_Label_Option mp mt U pth (u_path LVL LBL loop) lvl lbl lr_node
  end
  -- When mem is a lr_node but opt is not
  | mp mt (lr_node LVL LBL L R) pth loop lvl lbl leaf := begin
    simp [loop_tree_level_label_option],
    assume list_mem, cases list_mem,
    case or.inl { from From_Level_Label_Option mp mt L pth (lr_path LVL LBL loop) lvl lbl leaf list_mem },
    case or.inr { from From_Level_Label_Option mp mt R pth (lr_path LVL LBL loop) lvl lbl leaf list_mem }
  end
  | mp mt (lr_node LVL LBL L R) pth loop lvl lbl u_node := begin
    simp [loop_tree_level_label_option],
    assume list_mem, cases list_mem,
    case or.inl { from From_Level_Label_Option mp mt L pth (lr_path LVL LBL loop) lvl lbl u_node list_mem },
    case or.inr { from From_Level_Label_Option mp mt R pth (lr_path LVL LBL loop) lvl lbl u_node list_mem }
  end
end llot
export llot.node_option (leaf u_node lr_node)

/- Proof -/
lemma Case_Level :
  ∀(t : llot.tree)(pth : llot.path)(num : ℕ),
  ∀(lllpt : list (list (list (llot.path × llot.tree)))),
  ( lllpt ∈ llot.loop_tree t pth num ) →
  ---------------------------
  ( ∃(lvl : ℕ), lvl ≤ num ∧ lllpt = llot.list_tree_level t pth lvl )
| t pth num lllpt := begin
  induction num,
  case nat.zero {
    simp [llot.loop_tree],
    assume eq_zero,
    apply exists.intro 0,
    from and.intro aux.LE_Refl eq_zero
  },
  case nat.succ {
    simp [llot.loop_tree],
    assume or_eq_mem,
    cases or_eq_mem with eq_succ list_mem,
    case or.inl {
      apply exists.intro (num_n+1),
      from and.intro aux.LE_Refl eq_succ
    },
    case or.inr {
      have case_inductive, from num_ih list_mem,
      cases case_inductive with lvl case_inductive,
      cases case_inductive with le_lvl_num eq_lllt,
      apply exists.intro lvl,
      from and.intro (aux.LE_SUCC_of_LE le_lvl_num) eq_lllt
    }
  }
end
lemma Tree_to_Level :
  ∀(t : llot.tree)(pth : llot.path),
  ∀{exp p1 p2 q : ℕ},
  ( (llot.max_level t)+1 ≤ exp ) →
  ( aux.list_expoential (llot.list_tree t pth) exp p1 p2 q ) →
  ---------------------------
  ( ∃(lvl : ℕ), lvl ≤ (llot.max_level t) ∧ aux.list_expoential (llot.list_tree_level t pth lvl) exp p1 p2 q )
| t pth exp p1 p2 q := begin
  assume le_lvl_exp huge_t,
  -- Combinatory Property
  rewrite [←llot.Length_Tree] at le_lvl_exp,
  have main_combinatory, from aux.Main_Combinatory (llot.list_tree t pth) exp p1 p2 q le_lvl_exp huge_t,
  cases main_combinatory with list_lvl main_combinatory,
  cases main_combinatory with list_mem main_combinatory,
  -- Substitution
  have case_level, from Case_Level t pth (llot.max_level t) list_lvl list_mem,
  cases case_level with lvl case_level,
  cases case_level with le_lvl_max case_level,
  rewrite [case_level] at main_combinatory,
  -- ∃-Introduction and ∧-Introduction
  apply exists.intro lvl,
  from and.intro le_lvl_max main_combinatory
end

lemma Case_Label :
  ∀(t : llot.tree)(pth : llot.path)(lvl num : ℕ),
  ∀(llpt : list (list (llot.path × llot.tree))),
  ( llpt ∈ llot.loop_tree_level t pth lvl num ) →
  ---------------------------
  ( ∃(lbl : ℕ), lbl ≤ num ∧ llpt = llot.list_tree_level_label t pth lvl lbl )
| t pth lvl num llpt := begin
  induction num,
  case nat.zero {
    simp [llot.loop_tree_level],
    assume eq_zero,
    apply exists.intro 0,
    from and.intro aux.LE_Refl eq_zero
  },
  case nat.succ {
    simp [llot.loop_tree_level],
    assume or_eq_mem,
    cases or_eq_mem with eq_succ list_mem,
    case or.inl {
      apply exists.intro (num_n+1),
      from and.intro aux.LE_Refl eq_succ
    },
    case or.inr {
      have case_inductive, from num_ih list_mem,
      cases case_inductive with lbl case_inductive,
      cases case_inductive with le_lbl_num eq_llt,
      apply exists.intro lbl,
      from and.intro (aux.LE_SUCC_of_LE le_lbl_num) eq_llt
    }
  }
end
lemma Level_to_Label :
  ∀(t : llot.tree)(pth : llot.path)(lvl : ℕ),
  ∀{exp p1 p2 q : ℕ},
  ( (llot.max_label t)+1 ≤ exp ) →
  ( aux.list_expoential (llot.list_tree_level t pth lvl) exp p1 p2 q ) →
  ---------------------------
  ( ∃(lbl : ℕ), lbl ≤ (llot.max_label t) ∧ aux.list_expoential (llot.list_tree_level_label t pth lvl lbl) exp p1 p2 q )
| t pth lvl exp p1 p2 q := begin
  assume le_lbl_exp exp_level,
  -- Combinatory Property
  rewrite [←llot.Length_Tree_Level] at le_lbl_exp,
  have main_combinatory, from aux.Main_Combinatory (llot.list_tree_level t pth lvl) exp p1 p2 q le_lbl_exp exp_level,
  cases main_combinatory with list_lbl main_combinatory,
  cases main_combinatory with list_mem main_combinatory,
  -- Substitution
  have case_lbl, from Case_Label t pth lvl (llot.max_label t) list_lbl list_mem,
  cases case_lbl with lbl case_lbl,
  cases case_lbl with le_lbl_max case_lbl,
  rewrite [case_lbl] at main_combinatory,
  -- ∃-Introduction and ∧-Introduction
  apply exists.intro lbl,
  from and.intro le_lbl_max main_combinatory
end

lemma Case_Option :
  ∀(t : llot.tree)(pth : llot.path)(lvl lbl : ℕ),
  ∀(lpt : list (llot.path × llot.tree)),
  ( lpt ∈ (llot.list_tree_level_label t pth lvl lbl) ) →
  ---------------------------
  ( ∃(opt : llot.node_option), lpt = llot.list_tree_level_label_option t pth lvl lbl opt )
| t pth lvl lbl lpt := begin
  assume or_eq,
  simp [llot.list_tree_level_label] at or_eq,
  -- ∨-Elimination
  cases or_eq with eq_leaf or_eq,
  case or.inl { from exists.intro leaf eq_leaf },
  cases or_eq with eq_u_node eq_lr_node,
  case or.inl { from exists.intro u_node eq_u_node },
  case or.inr { from exists.intro lr_node eq_lr_node }
end
lemma Label_to_Option :
  ∀(t : llot.tree)(pth : llot.path)(lvl lbl : ℕ),
  ∀{exp p1 p2 q : ℕ},
  ( 3 ≤ exp ) →
  ( aux.list_expoential (llot.list_tree_level_label t pth lvl lbl) exp p1 p2 q ) →
  ---------------------------
  ( ∃(opt : llot.node_option), aux.list_expoential (llot.list_tree_level_label_option t pth lvl lbl opt) exp p1 p2 q )
| t pth lvl lbl exp p1 p2 q := begin
  assume le_opt_exp exp_level_label,
  -- Combinatory Property
  rewrite [←llot.Length_Tree_Level_Label] at le_opt_exp,
  have main_combinatory, from aux.Main_Combinatory (llot.list_tree_level_label t pth lvl lbl) exp p1 p2 q le_opt_exp exp_level_label,
  cases main_combinatory with list_opt main_combinatory,
  cases main_combinatory with list_mem main_combinatory,
  -- Substitution
  have case_opt, from Case_Option t pth lvl lbl list_opt list_mem,
  cases case_opt with opt case_opt,
  rewrite [case_opt] at main_combinatory,
  -- ∃-Introduction
  from exists.intro opt main_combinatory
end

lemma Case_Leaf :
  ∀(t : llot.tree)(pth : llot.path)(lvl lbl : ℕ),
  ∀(lpt : list (llot.path × llot.tree)),
  -- This lemma needs a proof that lpt ⊆ llot.list_tree_level_label_option t pth lvl lbl leaf:
  ( ∀(mem : (llot.path × llot.tree)),
    ( mem ∈ lpt ) →
    ---------------------------
    ( mem ∈ llot.list_tree_level_label_option t pth lvl lbl leaf ) ) →
  ---------------------------
  ( llot.list_branch (leaf lvl lbl) lpt = lpt )
| t pth lvl lbl [] := by simp [llot.list_branch]
| t pth lvl lbl (⟨hp,ht⟩::lpt) := begin
  assume subset_list,
  simp [llot.list_tree_level_label_option] at subset_list,
  -- Proving that the node at the head of the list(ht) has the given branch(leaf lvl lbl)
  have is_branch : llot.is_branch (leaf lvl lbl) ht,
                 from begin
                   have mem_hpht_lpt : (hp,ht) ∈ ((hp,ht)::lpt),
                                     by simp [has_mem.mem, list.mem],
                   have mem_hpht_level_label_option, from subset_list (hp,ht) mem_hpht_lpt,
                   have and_eq, from llot.From_Level_Label_Option hp ht t pth root lvl lbl leaf mem_hpht_level_label_option,
                   cases and_eq with eq_level and_eq,
                   cases and_eq with eq_label eq_option,
                   -- Since the given node at the head of the list(ht) can only be a leaf, the result follows by induction
                   induction ht,
                   case llot.tree.leaf {
                     simp [llot.is_branch],
                     simp [llot.tree_level, eq_comm] at eq_level,
                     simp [llot.tree_label, eq_comm] at eq_label,
                     from and.intro eq_level eq_label
                   },
                   case llot.tree.u_node { simp [llot.tree_option] at eq_option, from false.elim eq_option },
                   case llot.tree.lr_node { simp [llot.tree_option] at eq_option, from false.elim eq_option }
                 end,
  simp [llot.list_branch, is_branch],
  -- The rest of the proof follows by induction
  have subset_tail : ∀(mem : (llot.path × llot.tree)),
                     ( mem ∈ lpt ) →
                     ---------------------------
                     ( mem ∈ llot.list_tree_level_label_option t pth lvl lbl leaf ),
                   from begin
                     assume mem mem_lpt,
                     apply subset_list,
                     simp [has_mem.mem, list.mem],
                     from or.inr mem_lpt
                   end,
  from Case_Leaf t pth lvl lbl lpt subset_tail
end
lemma Induction_End_Leaf :
  ∀(t : llot.tree)(pth : llot.path)(lvl lbl : ℕ),
  ∀{exp p1 p2 q : ℕ},
  ( aux.list_expoential (llot.list_tree_level_label_option t pth lvl lbl leaf) exp p1 p2 q ) →
  ---------------------------
  ( ∃(b : llot.branch), aux.list_expoential (llot.list_branch b (llot.list_tree_level_label_option t pth lvl lbl leaf)) exp p1 p2 q )
| t pth lvl lbl exp p1 p2 q := begin
  assume exp_leaf,
  -- In the case of an exponential number of leaf nodes, the leaves themselves are the exponential branches
  apply exists.intro (llot.branch.leaf lvl lbl),
  have subset_self : ∀(mem : llot.path × llot.tree),
                     ( mem ∈ llot.list_tree_level_label_option t pth lvl lbl leaf ) →
                     ---------------------------
                     ( mem ∈ llot.list_tree_level_label_option t pth lvl lbl leaf ),
                   by intros; assumption,
  have case_leaf : llot.list_branch (leaf lvl lbl) (llot.list_tree_level_label_option t pth lvl lbl leaf)
                 = llot.list_tree_level_label_option t pth lvl lbl leaf,
                 from Case_Leaf t pth lvl lbl (llot.list_tree_level_label_option t pth lvl lbl leaf) subset_self,
  rewrite [case_leaf],
  from exp_leaf
end

lemma Case_Height :
  ∀(t : llot.tree)(pth : llot.path)(lbl : ℕ)(opt : llot.node_option),
  ∀{exp p1 p2 q : ℕ},
  ( llot.is_finite t ) →
  ( lbl ≤ llot.max_label t ) →
  ( aux.list_expoential (llot.list_tree_level_label_option t pth (llot.max_level t) lbl opt) exp p1 p2 q ) →
  ---------------------------
  ( opt = leaf )
| t pth lbl opt exp p1 p2 q := begin
  assume finite_t le_lbl_max exp_opt,
  induction opt,
  case llot.node_option.leaf { simp [refl] },
  case llot.node_option.u_node {
    -- Using the finite property to show that a condition(opt = u_node) is false
    simp [aux.list_expoential] at exp_opt,
    have exp_unode, from and.elim_right exp_opt,
    simp [llot.is_finite] at finite_t,
    rewrite [and.elim_left (finite_t pth lbl le_lbl_max)] at exp_unode,
    from false.elim (aux.Not_LT_ZERO exp_unode)
  },
  case llot.node_option.lr_node {
    -- Using the finite property to show that a condition(opt = lr_node) is false
    simp [aux.list_expoential] at exp_opt,
    have exp_lrnode, from and.elim_right exp_opt,
    simp [llot.is_finite] at finite_t,
    rewrite [and.elim_right (finite_t pth lbl le_lbl_max)] at exp_lrnode,
    from false.elim (aux.Not_LT_ZERO exp_lrnode)
  }
end
lemma Case_UNode :
  ∀(t : llot.tree)(pth : llot.path)(lvl lbl : ℕ),
  ∀{exp p1 p2 q : ℕ},
  ( llot.is_leveled t ) →
  ( (lvl+1) ≤ llot.max_level t ) → ( lbl ≤ llot.max_label t ) →
  ( aux.list_expoential (llot.list_tree_level_label_option t pth lvl lbl u_node) exp p1 p2 q ) →
  ---------------------------
  ( aux.list_expoential (llot.list_tree_level t (u_path lvl lbl pth) (lvl+1)) exp p1 p2 q )
| t pth lvl lbl exp p1 p2 q := begin
  simp [aux.list_expoential],
  assume leveled_t le_succ_lvl_max le_lbl_max exp_unode,
  cases exp_unode with exp_constraints exp_unode,
  apply and.intro exp_constraints,
  -- Using the leveled property to jump between levels, from a given level(lvl) to the level above it(lvl+1)
  simp [llot.is_leveled] at leveled_t,
  have le_unode, from and.elim_left (leveled_t pth lvl lbl le_succ_lvl_max le_lbl_max),
  from aux.LT_of_LT_of_LE exp_unode le_unode
end
lemma Case_LRNode :
  ∀(t : llot.tree)(pth : llot.path)(lvl lbl : ℕ),
  ∀{exp p1 p2 q : ℕ},
  ( llot.is_leveled t ) →
  ( (lvl+1) ≤ llot.max_level t ) → ( lbl ≤ llot.max_label t ) →
  ( aux.list_expoential (llot.list_tree_level_label_option t pth lvl lbl lr_node) exp p1 p2 q ) →
  ---------------------------
  ( aux.list_expoential (llot.list_tree_level t (lr_path lvl lbl pth) (lvl+1)) exp p1 p2 q )
| t pth lvl lbl exp p1 p2 q := begin
  simp [aux.list_expoential],
  assume leveled_t le_succ_lvl_max le_lbl_max exp_lrnode,
  cases exp_lrnode with exp_constraints exp_lrnode,
  apply and.intro exp_constraints,
  -- Using the leveled property to jump between levels, from a given level(lvl) to the level above it(lvl+1)
  simp [llot.is_leveled] at leveled_t,
  have le_lrnode, from and.elim_right (leveled_t pth lvl lbl le_succ_lvl_max le_lbl_max),
  from aux.LT_of_LT_of_LE exp_lrnode le_lrnode
end
lemma Induction_Steps :
  ∀(t : llot.tree)(pth : llot.path)(lvl0 lbl0 : ℕ)(opt0 : llot.node_option),
  ∀(exp p1 p2 q diff : ℕ),
  ( llot.is_leveled t ) → ( llot.is_connected t ) → ( llot.is_finite t ) →
  ( (llot.max_label t)+1 ≤ exp  ) → ( 3 ≤ exp ) →
  ( lvl0 ≤ llot.max_level t ) → ( lbl0 ≤ llot.max_label t ) →
  ( diff = (llot.max_level t) - lvl0 ) →
  ( aux.list_expoential (llot.list_tree_level_label_option t pth lvl0 lbl0 opt0) exp p1 p2 q ) →
  ---------------------------
  ( ∃(b : llot.branch),
    aux.list_expoential (llot.list_branch b (llot.list_tree_level_label_option t pth lvl0 lbl0 opt0)) exp p1 p2 q )
| t pth lvl0 lbl0 opt0 exp p1 p2 q 0 := begin
  -- Base case, for when the induction ends at highest level of the tree
  assume leveled_t connected_t finite_t le_lbl_exp le_opt_exp le_lvl0_max le_lbl0_max eq_diff exp_height,
  rewrite [aux.EQ_or_SUCC_LE_iff_LE] at le_lvl0_max,
  cases le_lvl0_max with eq_lvl0_max le_succ_lvl0_max,
  case or.inl {
    rewrite [eq_lvl0_max] at exp_height,
    have eq_opt0_leaf : opt0 = leaf, from Case_Height t pth lbl0 opt0 finite_t le_lbl0_max exp_height,
    rewrite [eq_opt0_leaf] at exp_height,
    rewrite [eq_lvl0_max, eq_opt0_leaf],
    -- Same as when the induction ends at a level with an exponential number of leaves
    have exp_branch, from Induction_End_Leaf t pth (llot.max_level t) lbl0 exp_height,
    cases exp_branch with b exp_branch,
    apply exists.intro b,
    from exp_branch
  },
  case or.inr {
    -- Showing that this case(le_succ_lvl0_max) is impossible given the condition(diff = 0)
    have not_case, from aux.Not_SUCC_LE_of_ZERO_EQ_SUB eq_diff,
    from false.elim (not_case le_succ_lvl0_max)
  }
end
| t pth lvl0 lbl0 leaf exp p1 p2 q (n+1) := begin
  -- Base case, for when the induction ends at a level with an exponential number of leaves
  assume leveled_t connected_t finite_t le_lbl_exp le_opt_exp le_lvl0_max le_lbl0_max eq_diff exp_leaf,
  have exp_branch, from Induction_End_Leaf t pth lvl0 lbl0 exp_leaf,
  cases exp_branch with b exp_branch,
  apply exists.intro b,
  from exp_branch
end
| t pth lvl0 lbl0 u_node exp p1 p2 q (n+1) := begin
  assume leveled_t connected_t finite_t le_lbl_exp le_opt_exp le_lvl0_max le_lbl0_max eq_diff exp_unode,
  rewrite [aux.EQ_or_SUCC_LE_iff_LE] at le_lvl0_max,
  cases le_lvl0_max with eq_lvl0_max le_succ_lvl0_max,
  case or.inl {
    -- Showing that this case(eq_lvl0_max) is impossible given the condition(diff = (n+1))
    have not_case, from aux.Not_EQ_of_SUCC_EQ_SUB eq_diff,
    from false.elim (not_case eq_lvl0_max)
  },
  case or.inr {
    -- Prove that the above level is exponential:
    have exp_level1, from Case_UNode t pth lvl0 lbl0 leveled_t le_succ_lvl0_max le_lbl0_max exp_unode,
    -- Find an exponential label within the above level:
    have exp_level1_label1, from Level_to_Label t (u_path lvl0 lbl0 pth) (lvl0+1) le_lbl_exp exp_level1,
    cases exp_level1_label1 with lbl1 exp_level1_label1,
    cases exp_level1_label1 with le_lbl1_max exp_level1_label1,
    -- Within an exponential label, within the above level, there are either exponential leafs or u_nodes or lr_nodes:
    have exp_level1_label1_option1, from Label_to_Option t (u_path lvl0 lbl0 pth) (lvl0+1) lbl1 le_opt_exp exp_level1_label1,
    cases exp_level1_label1_option1 with opt1 exp_level1_label1_option1,
    -- Apply the induction principle, having the current level approach the height of the tree(and diff approaching 0)
    have induction_step, from Induction_Steps t (u_path lvl0 lbl0 pth) (lvl0+1) lbl1 opt1
                                              exp p1 p2 q n
                                              leveled_t connected_t finite_t
                                              le_lbl_exp le_opt_exp
                                              le_succ_lvl0_max le_lbl1_max
                                              (aux.EQ_PRED_of_SUCC_EQ eq_diff)
                                              exp_level1_label1_option1,
    cases induction_step with b1 induction_step,
    apply exists.intro (u_branch lvl0 lbl0 b1),
    simp [llot.is_connected] at connected_t,
    have or_unode, from and.elim_left (connected_t pth lvl0 lbl0 lbl1 opt1 b1 le_succ_lvl0_max le_lbl0_max le_lbl1_max),
    cases or_unode with eq_branch_zero or_unode,
    case or.inl {
      -- This condition(eq_branch_zero) is impossible, for the amount of branches(b) out of this combination(lvl0+1/lbl1/opt1) is exponential
      simp [aux.list_expoential] at induction_step,
      cases induction_step with exp_constraints exp_branch,
      rewrite [eq_branch_zero] at exp_branch,
      from false.elim (aux.Not_LT_ZERO exp_branch)
    },
    cases or_unode with eq_lvl0_zero connected_unode,
    case or.inl {
      -- This condition(eq_lvl0_zero) is impossible, for the amount of nodes at this combination(lvlv0/lbl0/u_node) is exponential
      simp [aux.list_expoential] at exp_unode,
      cases exp_unode with exp_constraints exp_unode,
      rewrite [eq_lvl0_zero] at exp_unode,
      from false.elim (aux.Not_LT_ZERO exp_unode)
    },
    case or.inr {
      -- As such, and by construction, the nodes below are connected to the nodes above by the given path
      simp [aux.list_expoential] at induction_step,
      rewrite [connected_unode] at induction_step,
      from induction_step
    }
  }
end
| t pth lvl0 lbl0 lr_node exp p1 p2 q (n+1) := begin
  assume leveled_t connected_t finite_t le_lbl_exp le_opt_exp le_lvl0_max le_lbl0_max eq_diff exp_lrnode,
  rewrite [aux.EQ_or_SUCC_LE_iff_LE] at le_lvl0_max,
  cases le_lvl0_max with eq_lvl0_max le_succ_lvl0_max,
  case or.inl {
    -- Showing that this case(eq_lvl_max) is impossible given the condition(diff = (n+1))
    have not_case, from aux.Not_EQ_of_SUCC_EQ_SUB eq_diff,
    from false.elim (not_case eq_lvl0_max)
  },
  case or.inr {
    -- Prove that the above level is exponential:
    have exp_level1, from Case_LRNode t pth lvl0 lbl0 leveled_t le_succ_lvl0_max le_lbl0_max exp_lrnode,
    -- Find an exponential label within the above level:
    have exp_level1_label1, from Level_to_Label t (lr_path lvl0 lbl0 pth) (lvl0+1) le_lbl_exp exp_level1,
    cases exp_level1_label1 with lbl1 exp_level1_label1,
    cases exp_level1_label1 with le_lbl1_max exp_level1_label1,
    -- Within an exponential label, within the above level, there are either exponential leafs or u_nodes or lr_nodes:
    have exp_level1_label1_option1, from Label_to_Option t (lr_path lvl0 lbl0 pth) (lvl0+1) lbl1 le_opt_exp exp_level1_label1,
    cases exp_level1_label1_option1 with opt1 exp_level1_label1_option1,
    -- Apply the induction principle, having the current level approach the height of the tree(and diff approaching 0)
    have induction_step, from Induction_Steps t (lr_path lvl0 lbl0 pth) (lvl0+1) lbl1 opt1
                                              exp p1 p2 q n
                                              leveled_t connected_t finite_t
                                              le_lbl_exp le_opt_exp
                                              le_succ_lvl0_max le_lbl1_max
                                              (aux.EQ_PRED_of_SUCC_EQ eq_diff)
                                              exp_level1_label1_option1,
    cases induction_step with b1 induction_step,
    apply exists.intro (lr_branch lvl0 lbl0 b1),
    simp [llot.is_connected] at connected_t,
    have or_lrnode, from and.elim_right (connected_t pth lvl0 lbl0 lbl1 opt1 b1 le_succ_lvl0_max le_lbl0_max le_lbl1_max),
    cases or_lrnode with eq_branch_zero or_lrnode,
    case or.inl {
      -- This condition(eq_branch_zero) is impossible, for the amount of branches(b) out of this combination(lvl0+1/lbl1/opt1) is exponential
      simp [aux.list_expoential] at induction_step,
      cases induction_step with exp_constraints exp_branch,
      rewrite [eq_branch_zero] at exp_branch,
      from false.elim (aux.Not_LT_ZERO exp_branch)
    },
    cases or_lrnode with eq_lvl0_zero connected_lrnode,
    case or.inl {
      -- This condition(eq_lvl0_zero) is impossible, for the amount of nodes at this combination(lvl0/lbl0/lr_node) is exponential
      simp [aux.list_expoential] at exp_lrnode,
      cases exp_lrnode with exp_constraints exp_lrnode,
      rewrite [eq_lvl0_zero] at exp_lrnode,
      from false.elim (aux.Not_LT_ZERO exp_lrnode)
    },
    case or.inr {
      -- As such, and by construction, the nodes below are connected to the nodes above by the given path(lr_path pth lvl0 lbl0)
      simp [aux.list_expoential] at induction_step,
      rewrite [connected_lrnode] at induction_step,
      from induction_step
    }
  }
end

theorem Main_Theorem :
  ∀(t : llot.tree),
  ∀{exp p1 p2 q : ℕ},
  ( llot.is_leveled t ) → ( llot.is_connected t ) → ( llot.is_finite t ) →
  ( (llot.max_level t)+1 ≤ exp ) → ( (llot.max_label t)+1 ≤ exp  ) → ( 3 ≤ exp ) →
  ( aux.list_expoential (llot.list_tree t root) exp p1 p2 q ) →
  ---------------------------
  ( ∃(lvl lbl : ℕ)(opt : llot.node_option)(b : llot.branch),
    aux.list_expoential (llot.list_branch b (llot.list_tree_level_label_option t root lvl lbl opt)) exp p1 p2 q )
| t exp p1 p2 q := begin
  assume leveled_t connected_t finite_t le_lvl_exp le_lbl_exp le_opt_exp huge_t,
  -- Find an exponential level:
  have exp_level, from Tree_to_Level t root le_lvl_exp huge_t,
  cases exp_level with lvl exp_level,
  cases exp_level with le_lvl_max exp_level,
  apply exists.intro lvl,
  -- Find an exponential label within the exponential level:
  have exp_level_label, from Level_to_Label t root lvl le_lbl_exp exp_level,
  cases exp_level_label with lbl exp_level_label,
  cases exp_level_label with le_lbl_max exp_level_label,
  apply exists.intro lbl,
  -- Within an exponential label, within an exponential level, there are either exponential leafs or u_nodes or lr_nodes:
  have exp_level_label_option, from Label_to_Option t root lvl lbl le_opt_exp exp_level_label,
  cases exp_level_label_option with opt exp_level_label_option,
  apply exists.intro opt,
  -- Induction on the above opt cases(leaf; u_node; lr_node):
  from Induction_Steps t root lvl lbl opt
                       exp p1 p2 q ((llot.max_level t) - lvl)
                       leveled_t connected_t finite_t
                       le_lbl_exp le_opt_exp
                       le_lvl_max le_lbl_max
                       (eq.refl ((llot.max_level t) - lvl))
                       exp_level_label_option
end



/- Test Cases -/
-- 4: 0   |  1 |
-- 3:  2  | 2  |  3
-- 2:   4 |  4 | 4
-- 1:   5 |  5 | 5
-- 0:   6 |  6 | 6
def b40A : llot.branch := leaf 4 0
def b32A : llot.branch := lr_branch 3 2 b40A
def b24A : llot.branch := lr_branch 2 4 b32A
def b15A : llot.branch := u_branch 1 5 b24A
def b06A : llot.branch := u_branch 0 6 b15A
def b41B : llot.branch := leaf 4 1
def b32B : llot.branch := lr_branch 3 2 b41B
def b24B : llot.branch := lr_branch 2 4 b32B
def b15B : llot.branch := u_branch 1 5 b24B
def b06B : llot.branch := u_branch 0 6 b15B
def b33C : llot.branch := leaf 3 3
def b24C : llot.branch := lr_branch 2 4 b33C
def b15C : llot.branch := u_branch 1 5 b24C
def b06C : llot.branch := u_branch 0 6 b15C
-- 4: 0     1
-- 3:    2     3
-- 2:       4
-- 1:       5
-- 0:       6
def t40 : llot.tree := leaf 4 0
def t41 : llot.tree := leaf 4 1
def t32 : llot.tree := lr_node 3 2 t40 t41
def t33 : llot.tree := leaf 3 3
def t24 : llot.tree := lr_node 2 4 t32 t33
def t15 : llot.tree := u_node 1 5 t24
def t06 : llot.tree := u_node 0 6 t15

#eval llot.tree.sizeof t06

def llot.list_level : llot.tree → list ℕ
| (leaf LVL LBL) := [LVL]
| (u_node LVL LBL U) := [LVL] ∪ llot.list_level U
| (lr_node LVL LBL L R) := [LVL] ∪ (llot.list_level L ∪ llot.list_level R)
#eval llot.tree_level t06
#eval llot.list_level t06
#eval llot.max_level t06

def llot.list_label : llot.tree → list ℕ
| (leaf LVL LBL) := [LBL]
| (u_node LVL LBL U) := [LBL] ∪ llot.list_label U
| (lr_node LVL LBL L R) := [LBL] ∪ (llot.list_label L ∪ llot.list_label R)
#eval llot.tree_label t06
#eval llot.list_label t06
#eval llot.max_label t06

#reduce list.mem (llot.list_tree_level_label_option t06 root 0 6 lr_node) (llot.list_tree_level_label t06 root 0 6)
#reduce (llot.list_tree_level_label_option t06 root 0 6 lr_node) ∈ (llot.list_tree_level_label t06 root 0 6)
#eval aux.count (llot.list_tree_level_label_option t06 root 0 6 lr_node)
#reduce list.mem (llot.list_tree_level_label_option t06 root 4 1 leaf) (llot.list_tree_level_label t06 root 4 1)
#reduce (llot.list_tree_level_label_option t06 root 4 1 leaf) ∈ (llot.list_tree_level_label t06 root 4 1)
#eval aux.count (llot.list_tree_level_label_option t06 root 4 1 leaf)

#eval llot.list_tree_level_label_option t06 root 0 4 u_node
#eval llot.list_tree_level_label_option t06 root 1 4 u_node
#eval llot.list_tree_level_label_option t06 root 2 4 u_node
#eval llot.list_tree_level_label_option t06 root 3 4 u_node
#eval llot.list_tree_level_label_option t06 root 4 4 u_node
#eval llot.list_tree_level_label_option t06 root 5 4 u_node
#eval aux.count (llot.list_tree_level_label_option t06 root 0 4 u_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 1 4 u_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 2 4 u_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 3 4 u_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 4 4 u_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 5 4 u_node)
#eval llot.list_tree_level_label_option t06 root 0 4 lr_node
#eval llot.list_tree_level_label_option t06 root 1 4 lr_node
#eval llot.list_tree_level_label_option t06 root 2 4 lr_node
#eval llot.list_tree_level_label_option t06 root 3 4 lr_node
#eval llot.list_tree_level_label_option t06 root 4 4 lr_node
#eval llot.list_tree_level_label_option t06 root 5 4 lr_node
#eval aux.count (llot.list_tree_level_label_option t06 root 0 4 lr_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 1 4 lr_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 2 4 lr_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 3 4 lr_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 4 4 lr_node)
#eval aux.count (llot.list_tree_level_label_option t06 root 5 4 lr_node)

#eval llot.list_tree_level_label t06 root 0 4
#eval llot.list_tree_level_label t06 root 1 4
#eval llot.list_tree_level_label t06 root 2 4
#eval llot.list_tree_level_label t06 root 3 4
#eval llot.list_tree_level_label t06 root 4 4
#eval llot.list_tree_level_label t06 root 5 4
#eval aux.count (llot.list_tree_level_label t06 root 0 4)
#eval aux.count (llot.list_tree_level_label t06 root 1 4)
#eval aux.count (llot.list_tree_level_label t06 root 2 4)
#eval aux.count (llot.list_tree_level_label t06 root 3 4)
#eval aux.count (llot.list_tree_level_label t06 root 4 4)
#eval aux.count (llot.list_tree_level_label t06 root 5 4)

#eval llot.list_tree_level t06 root 0
#eval llot.list_tree_level t06 root 1
#eval llot.list_tree_level t06 root 2
#eval llot.list_tree_level t06 root 3
#eval llot.list_tree_level t06 root 4
#eval llot.list_tree_level t06 root 5
#eval aux.count (llot.list_tree_level t06 root 0)
#eval aux.count (llot.list_tree_level t06 root 1)
#eval aux.count (llot.list_tree_level t06 root 2)
#eval aux.count (llot.list_tree_level t06 root 3)
#eval aux.count (llot.list_tree_level t06 root 4)
#eval aux.count (llot.list_tree_level t06 root 5)

#eval llot.list_tree t06 root
#eval aux.count (llot.list_tree t06 root) -- p ^ ((k * m) ^ q), p > 1 ∧ q > 0

#reduce llot.is_branch b06A t15
#reduce llot.is_branch b06B t15
#reduce llot.is_branch b06C t15
#reduce llot.is_branch b15A t15
#reduce llot.is_branch b15B t15
#reduce llot.is_branch b15B t15
#eval llot.list_branch b06A (llot.list_tree_level_label_option t06 root 1 5 u_node)
#eval llot.list_branch b06B (llot.list_tree_level_label_option t06 root 1 5 u_node)
#eval llot.list_branch b06C (llot.list_tree_level_label_option t06 root 1 5 u_node)
#eval llot.list_branch b15A (llot.list_tree_level_label_option t06 root 1 5 u_node)
#eval llot.list_branch b15B (llot.list_tree_level_label_option t06 root 1 5 u_node)
#eval llot.list_branch b15B (llot.list_tree_level_label_option t06 root 1 5 u_node)

-- LEVELLED PROPERTY:
--#reduce llot.is_leveled t06
def check_leveled : llot.tree → ℕ → ℕ → bool
--def check_leveled : llot.tree → ℕ → ℕ → Prop
| t lvl lbl := ( aux.list_count ( llot.list_tree_level_label_option t root lvl lbl u_node )
               ≤ aux.list_count ( llot.list_tree_level t root (lvl+1) ) )
             ∧ ( aux.list_count ( llot.list_tree_level_label_option t root lvl lbl lr_node )
               ≤ aux.list_count ( llot.list_tree_level t root (lvl+1) ) )
#reduce check_leveled t06 0 0
#reduce check_leveled t06 1 0
#reduce check_leveled t06 2 0
#reduce check_leveled t06 3 0
#reduce check_leveled t06 4 0
#reduce check_leveled t06 0 2
#reduce check_leveled t06 1 2
#reduce check_leveled t06 2 2
#reduce check_leveled t06 3 2
#reduce check_leveled t06 4 2
#reduce check_leveled t06 0 4
#reduce check_leveled t06 1 4
#reduce check_leveled t06 2 4
#reduce check_leveled t06 3 4
#reduce check_leveled t06 4 4
#reduce check_leveled t06 0 6
#reduce check_leveled t06 1 6
#reduce check_leveled t06 2 6
#reduce check_leveled t06 3 6
#reduce check_leveled t06 4 6

-- CONNECTED PROPERTY:
-- 4: 0     1    | 0   |  1 |
-- 3:    2     3 |  2  | 2  |  3
-- 2:       4    |   4 |  4 | 4
-- 1:       5    |   5 |  5 | 5
-- 0:       6    |   6 |  6 | 6
--#reduce llot.is_connected t06
def check_connected : llot.tree → ℕ → ℕ → ℕ → llot.node_option → llot.branch → bool
--def check_connected : llot.tree → ℕ → ℕ → ℕ → llot.node_option → llot.branch → Prop
| t lvl0 lbl0 lbl1 opt1 b :=
  ( aux.list_count (llot.list_branch b (llot.list_tree_level_label_option t (u_path lvl0 lbl0 root) (lvl0+1) lbl1 opt1)) = 0
  ∨ aux.list_count (llot.list_tree_level_label_option t root lvl0 lbl0 u_node) = 0
  ∨ aux.list_count (llot.list_branch b (llot.list_tree_level_label_option t (u_path lvl0 lbl0 root) (lvl0+1) lbl1 opt1))
  = aux.list_count (llot.list_branch (u_branch lvl0 lbl0 b) (llot.list_tree_level_label_option t root lvl0 lbl0 u_node)) )
∧ ( aux.list_count (llot.list_branch b (llot.list_tree_level_label_option t (lr_path lvl0 lbl0 root) (lvl0+1) lbl1 opt1)) = 0
  ∨ aux.list_count (llot.list_tree_level_label_option t root lvl0 lbl0 lr_node) = 0
  ∨ aux.list_count (llot.list_branch b (llot.list_tree_level_label_option t (lr_path lvl0 lbl0 root) (lvl0+1) lbl1 opt1))
  = aux.list_count (llot.list_branch (lr_branch lvl0 lbl0 b) (llot.list_tree_level_label_option t root lvl0 lbl0 lr_node)) )
#reduce check_connected t06 0 6 5 u_node b15A
#reduce check_connected t06 0 6 5 u_node b15B
#reduce check_connected t06 0 6 5 u_node b15C
#reduce check_connected t06 2 4 2 lr_node b32A
#reduce check_connected t06 2 4 2 lr_node b32B
#reduce check_connected t06 2 4 3 lr_node b33C

-- FINITE PROPERTY:
--#reduce llot.is_finite t06
def check_finite : llot.tree → ℕ → bool
--def check_finite : llot.tree → ℕ → Prop
| t lbl := ( aux.list_count (llot.list_tree_level_label_option t root (llot.max_level t) lbl u_node) = 0 )
         ∧ ( aux.list_count (llot.list_tree_level_label_option t root (llot.max_level t) lbl lr_node) = 0 )
#reduce check_finite t06 0
#reduce check_finite t06 1
#reduce check_finite t06 2
#reduce check_finite t06 3
#reduce check_finite t06 4
#reduce check_finite t06 5
#reduce check_finite t06 6