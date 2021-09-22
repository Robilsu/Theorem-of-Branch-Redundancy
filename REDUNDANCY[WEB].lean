/- To run this project, load the contents of this file at:
--   https://leanprover-community.github.io/lean-web-editor
-- You can either copy-and-paste it or use the load function.
-- The Lean web editor will take up to some minutes to load fully and process the code.
-- Do not worry! The waiting is normal and happens only once (when the code is loaded). -/

reserve prefix `#` : 9999     -- #_
reserve infix ` >> ` : 1000   -- _ >> _

/- Useful Properties -/
namespace use
  universes u v

  /- Proofs from L∃∀N's library regarding negation, conjunction, and disjunction -/
  lemma Not_Or {a b : Prop} : ¬ a → ¬ b → ¬ (a ∨ b)
  | hna hnb (or.inl ha) := absurd ha hna
  | hna hnb (or.inr hb) := absurd hb hnb
  lemma Not_Or_iff_And_Not (p q) [d₁ : decidable p] [d₂ : decidable q] : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  iff.intro
    (λ h, match d₁ with
          | is_true h₁  := false.elim $ h (or.inl h₁)
          | is_false h₁ :=
            match d₂ with
            | is_true h₂  := false.elim $ h (or.inr h₂)
            | is_false h₂ := ⟨h₁, h₂⟩
            end
          end)
    (λ ⟨np, nq⟩ h, or.elim h np nq)

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

  /- Useful properties regarding Lists -/
  lemma Index_LT_Length_of_Mem {α : Type u} [eqα : decidable_eq α] :
    ∀{a : α}{l : list α},
    ( a ∈ l ) →
    ---------------------------
    ( list.index_of a l < list.length l )
  | a [] := begin
    assume a_mem,
    simp [has_mem.mem, list.mem] at a_mem,
    from false.elim a_mem
  end
  | a (HEAD::TAIL) := begin
    assume a_mem,
    simp [has_mem.mem, list.mem] at a_mem,
    simp [list.index_of, list.find_index, list.length],
    with_cases { by_cases a_eq_head : a = HEAD },
    case pos {
      simp [a_eq_head],
      have one_le_succ, from nat.add_le_add_left (nat.zero_le (list.length TAIL)) 1,
      rewrite [nat.add_zero] at one_le_succ,
      have zero_lt_succ, from nat.lt_of_lt_of_le (nat.zero_lt_one) one_le_succ,
      rewrite [nat.add_comm] at zero_lt_succ,
      from nat.lt_of_lt_of_le nat.zero_lt_one zero_lt_succ
    },
    case neg {
      simp [a_eq_head] at ⊢ a_mem,
      rewrite [nat.succ_eq_add_one, nat.add_comm],
      have loop, from Index_LT_Length_of_Mem a_mem,
      have lt_loop, from nat.add_lt_add_left loop 1,
      rewrite [nat.add_comm 1 (TAIL.length)] at lt_loop,
      from lt_loop
    }
  end
  lemma Mem_Remove_of_Mem_of_Not_Mem {α : Type u} [eqα : decidable_eq α] :
    ∀{nth : α}{l1 l2 : list α},
    ( nth ∉ l1 ) →
    ( nth ∈ l2 ) →
    ---------------------------
    ( ∀(a : α), a ∈ l1 → a ∈ l2 → a ∈ list.remove_nth l2 (list.index_of nth l2) )
  | nth l1 [] := begin
    assume nth_not_l1 nth_mem_l2,
    simp [has_mem.mem, list.mem] at nth_mem_l2,
    from false.elim nth_mem_l2
  end
  | nth l1 (HEAD2::TAIL2) := begin
    assume nth_not_l1 nth_mem_l2,
    simp [list.index_of, list.find_index],
    with_cases { by_cases nth_eq_head2 : nth = HEAD2 },
    case pos {
      simp [nth_eq_head2] at ⊢ nth_not_l1,
      simp [list.index_of, list.find_index, list.remove_nth],
      have case_loop : ∀(a : α), a ∈ l1 → a ∈ (HEAD2::TAIL2) → a ∈ TAIL2,
      from begin
        assume loop loop_mem_l1 loop_mem_l2,
        simp [has_mem.mem, list.mem] at loop_mem_l2,
        cases loop_mem_l2 with loop_eq_head2 loop_mem_tail2,
        case or.inl {
          rewrite [loop_eq_head2] at loop_mem_l1,
          from absurd loop_mem_l1 nth_not_l1
        },
        case or.inr { from loop_mem_tail2 }
      end,
      from case_loop
    },
    case neg {
      simp [nth_eq_head2] at ⊢ nth_mem_l2,
      simp [list.remove_nth],
      have case_loop : ∀(a : α), a ∈ l1 → a ∈ (HEAD2::TAIL2) → a = HEAD2 ∨ a ∈ list.remove_nth TAIL2 (list.find_index (eq nth) TAIL2),
      from begin
        assume loop loop_mem_l1 loop_mem_l2,
        simp [has_mem.mem, list.mem] at loop_mem_l2,
        cases loop_mem_l2 with loop_eq_head2 loop_mem_tail2,
        case or.inl { simp [loop_eq_head2] },
        case or.inr {
          apply (or.intro_right),
          from Mem_Remove_of_Mem_of_Not_Mem nth_not_l1 nth_mem_l2 loop loop_mem_l1 loop_mem_tail2
        }
      end,
      from case_loop
    }
  end
  lemma Subset_Self {α : Type u} :
    ∀(l : list α),
    ---------------------------
    ( ∀(a : α), ( a ∈ l ) → ( a ∈ l ) )
  | l := begin
    have subset_self : ∀(a : α), a ∈ l → a ∈ l,
    from begin
      assume a a_mem_l,
      from a_mem_l
    end,
    from subset_self
  end

  /- Useful properties regarding Natural Numbers (Must be in Order) -/
  lemma LT_Add_of_Pos_of_LE :
    ∀{a b c : ℕ},
    ( 0 < a ) →
    ( b ≤ c ) →
    ---------------------------------
    b < a + c
  | a b c := begin
    assume a_pos b_le_c,
    have one_le_a, from nat.succ_le_of_lt a_pos,
    have b_le_ac, from nat.add_le_add one_le_a b_le_c,
    rewrite [nat.add_comm] at b_le_ac,
    from nat.lt_of_succ_le b_le_ac
  end
  lemma LT_Add_of_Pos_of_LT :
    ∀{a b c : ℕ},
    ( 0 < a ) →
    ( b < c ) →
    ---------------------------------
    b < a + c
  | a b c := begin
    assume a_pos b_lt_c,
    from LT_Add_of_Pos_of_LE a_pos (nat.le_of_lt b_lt_c)
  end
  lemma LT_Add_of_LE_of_Pos :
    ∀{a b c : ℕ},
    ( b ≤ c ) →
    ( 0 < a ) →
    ---------------------------------
    b < c + a
  | a b c := begin
    assume b_le_c a_pos,
    have one_le_a, from nat.succ_le_of_lt a_pos,
    have b_le_ca, from nat.add_le_add b_le_c one_le_a,
    from nat.lt_of_succ_le b_le_ca
  end
  lemma LT_Add_of_LT_of_Pos :
    ∀{a b c : ℕ},
    ( b < c ) →
    ( 0 < a ) →
    ---------------------------------
    b < c + a
  | a b c := begin
    assume b_lt_c a_pos,
    from LT_Add_of_LE_of_Pos (nat.le_of_lt b_lt_c) a_pos
  end
  lemma EQ_of_LT_ONE_of_GE :
    ∀{a b : ℕ},
    ( a ≥ b ) →
    ( a < 1 + b ) →
    ---------------------------------
    ( a = b )
  | 0 0 := begin
    assume a_ge_b a_lt_oneb,
    from eq.refl 0
  end
  | (a+1) 0 := begin
    assume a_ge_b a_lt_oneb,
    rewrite [nat.add_comm] at a_lt_oneb,
    have zero_lt_a, from nat.lt_of_add_lt_add_left a_lt_oneb,
    have not_zero_lt_a, from nat.not_lt_zero a,
    from absurd zero_lt_a not_zero_lt_a
  end
  | 0 (b+1) := begin
    assume a_ge_b a_lt_oneb,
    have zero_le_b, from nat.zero_le b,
    have b_le_oneb, from le_trans a_ge_b zero_le_b,
    rewrite [nat.add_one] at b_le_oneb,
    from absurd b_le_oneb (nat.not_succ_le_self b)
  end
  | (a+1) (b+1) := begin
    assume a_ge_b a_lt_oneb,
    have loop_ge : a ≥ b , from nat.le_of_succ_le_succ a_ge_b,
    rewrite [nat.add_comm] at a_lt_oneb,
    have loop_lt, from nat.lt_of_add_lt_add_left a_lt_oneb,
    rewrite [nat.add_comm] at loop_lt,
    rewrite [EQ_of_LT_ONE_of_GE loop_ge loop_lt]
  end
  lemma LE_Mul_Left_of_Pos :
    ∀{a : ℕ},
    ( 0 < a ) →
    ---------------------------------
    ( ∀(b : ℕ), b ≤ a * b )
  | a := begin
    assume zero_lt_a b,
    induction b,
    case nat.zero { simp [nat.mul_zero] },
    case nat.succ {
      have one_le_a, from nat.succ_le_of_lt zero_lt_a,
      rewrite [nat.succ_eq_add_one, nat.mul_comm a, nat.add_comm, nat.right_distrib, nat.one_mul, nat.mul_comm],
      from nat.add_le_add one_le_a b_ih
    }
  end
  /- Useful properties regarding Natural Numbers -/
  lemma Add_GE_Add :
    ∀{a b c d : ℕ},
    ( a ≥ b ) →
    ( c ≥ d ) →
    ---------------------------------
    ( a + c ≥ b + d )
  | a b c d := begin
    assume a_ge_b c_ge_d,
    from nat.add_le_add a_ge_b c_ge_d
  end
  lemma Add_Left_EQ_of_EQ :
    ∀{a b : ℕ},
    ( a = b ) →
    ---------------------------------
    ( ∀(c : ℕ), c + a = c + b )
  | a b := begin
    assume a_eq_b c,
    rewrite [a_eq_b]
  end
  lemma Add_Right_EQ_of_EQ :
    ∀{a b : ℕ},
    ( a = b ) →
    ---------------------------------
    ( ∀(c : ℕ), a + c = b + c )
  | a b := begin
    assume a_eq_b c,
    rewrite [a_eq_b]
  end
  lemma EQ_or_SUCC_LE_iff_LE :
    ∀{a b : ℕ},
    ---------------------------
    ( a ≤ b ) ↔ ( (a = b) ∨ (a+1 ≤ b) )
  := begin
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
    assume a b,
    from iff.intro case_to case_from
  end
  lemma EQ_PRED_of_SUCC_EQ : -- Notice that the other way does not hold true, since 0 ≠ 0 - 1
    ∀{a b : ℕ},
    ( a+1 = b ) →
    ---------------------------
    ( a = b-1 )
  | a b := begin
    assume eq_succ_a_b,
    rewrite [←eq_succ_a_b, eq_comm],
    from nat.add_sub_cancel a 1
  end
  lemma GE_Cancel_Right :
    ∀{a b c : ℕ},
    ( a ≥ b + c ) →
    ---------------------------------
    ( a ≥ b )
  | a b c := begin
    assume a_ge_bc,
    have bc_ge_b : b + c ≥ b, from
    begin
      have b_le_bc, from nat.add_le_add_left (nat.zero_le c) b,
      rewrite [nat.add_zero] at b_le_bc,
      from b_le_bc
    end,
    from ge_trans a_ge_bc bc_ge_b
  end
  lemma GE_iff_Not_LT :
    ∀{a b : ℕ},
    ---------------------------
    ( a ≥ b ) ↔ ( ¬( a < b ) )
  := begin
    have case_to : ∀{m n : ℕ}, ( m ≥ n ) → ( ¬( m < n ) ),
    from begin
      assume m n m_ge_n,
      from not_lt_of_ge m_ge_n
    end,
    have case_from : ∀{m n : ℕ}, ( ¬( m < n ) ) → ( m ≥ n ),
    from begin
      assume m n not_m_lt_n,
      have eq_or_lt, from nat.eq_or_lt_of_not_lt not_m_lt_n,
      cases eq_or_lt with m_eq_n m_lt_n,
      case or.inl { apply nat.le_of_eq, from (iff.elim_right eq_comm) m_eq_n },
      case or.inr { apply nat.le_of_lt, from m_lt_n },
    end,
    assume a b,
    from iff.intro case_to case_from
  end
  lemma LE_Add_Left :
    ∀{a b : ℕ},
    ( a ≤ b ) →
    ---------------------------------
    ( ∀(c : ℕ), ( a ≤ c + b ) )
  | a b := begin
    assume a_le_b c,
    from le_trans a_le_b (nat.le_add_left b c)
  end
  lemma LE_Add_Right :
    ∀{a b : ℕ},
    ( a ≤ b ) →
    ---------------------------------
    ( ∀(c : ℕ), ( a ≤ b + c ) )
  | a b := begin
    assume a_le_b c,
    from le_trans a_le_b (nat.le_add_right b c)
  end
  lemma LE_Mul_of_LE :
    ∀{a b : ℕ},
    ∀(c : ℕ),
    ( a ≤ b ) →
    ---------------------------
    ( a * c ≤ b * c )
  | a b 0 := begin
    assume a_le_b,
    simp [nat.mul_zero]
  end
  | a b (c+1) := begin
    assume a_le_b,
    rewrite [←nat.mul_comm (c+1), nat.right_distrib, nat.one_mul, nat.mul_comm c],
    rewrite [←nat.mul_comm (c+1), nat.right_distrib, nat.one_mul, nat.mul_comm c],
    have loop, from LE_Mul_of_LE c a_le_b,
    from nat.add_le_add loop a_le_b
  end
  lemma LT_Add_Left :
    ∀{a b : ℕ},
    ( a < b ) →
    ---------------------------------
    ( ∀(c : ℕ), ( a < c + b ) )
  | a b := begin
    assume a_lt_b c,
    with_cases {by_cases c_eq_zero : c = 0 },
    case pos { simp [c_eq_zero], rewrite [nat.add_comm, nat.add_zero], from a_lt_b },
    case neg {
      rewrite [eq_comm] at c_eq_zero,
      have c_pos, from lt_of_le_of_ne (nat.zero_le c) (c_eq_zero),
      from LT_Add_of_Pos_of_LT c_pos a_lt_b
    }
  end
  lemma LT_Add_Right :
    ∀{a b : ℕ},
    ( a < b ) →
    ---------------------------------
    ( ∀(c : ℕ), ( a < b + c ) )
  | a b := begin
    assume a_lt_b c,
    with_cases {by_cases c_eq_zero : c = 0 },
    case pos { simp [c_eq_zero], rewrite [nat.add_zero], from a_lt_b },
    case neg {
      rewrite [eq_comm] at c_eq_zero,
      have c_pos, from lt_of_le_of_ne (nat.zero_le c) (c_eq_zero),
      from LT_Add_of_LT_of_Pos a_lt_b c_pos
    }
  end
  lemma LT_ZERO_iff_LE_ONE :
    ∀{a : ℕ},
    ---------------------------
    ( 0 < a ) ↔ ( 1 ≤ a )
  := begin
    have case_to : ∀{a : ℕ}, ( 0 < a ) → ( 1 ≤ a ),
    from begin
      assume a zero_lt_a,
      from nat.le_of_lt_succ (nat.succ_lt_succ zero_lt_a)
    end,
    have case_from : ∀{a : ℕ}, ( 1 ≤ a ) → ( 0 < a ),
    from begin
      assume a one_le_a,
      from nat.lt_of_lt_of_le nat.zero_lt_one one_le_a
    end,
    assume a,
    from iff.intro case_to case_from
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
  lemma Sub_Add_Cancel :
    ∀{a b : ℕ},
    ( b ≤ a ) →
    ---------------------------------
    ( a - b + b = a )
  | a b := begin
    assume b_le_a,
    from nat.sub_add_cancel b_le_a
  end
  lemma ZERO_LT_Mul_iff_AND_ZERO_LT :
    ∀{a b : ℕ},
    ---------------------------------
    ( 0 < a * b ) ↔ ( 0 < a ∧ 0 < b )
  := begin
    have case_to : ∀{a b : ℕ}, ( 0 < a * b ) → ( 0 < a ∧ 0 < b ),
    from begin
      assume a b zero_lt_ab,
      with_cases {by_cases a_eq_zero : a = 0 },
      case pos {
        rewrite [a_eq_zero, nat.zero_mul] at zero_lt_ab,
        from false.elim (nat.not_lt_zero 0 zero_lt_ab)
      },
      case neg {
        with_cases {by_cases b_eq_zero : b = 0 },
        case pos {
          rewrite [b_eq_zero, nat.mul_zero] at zero_lt_ab,
          from false.elim (nat.not_lt_zero 0 zero_lt_ab)
        },
        case neg {
          have zero_le_a, from nat.lt_of_le_and_ne (nat.zero_le a),
          have zero_le_b, from nat.lt_of_le_and_ne (nat.zero_le b),
          rewrite [ne.def, eq_comm] at zero_le_a zero_le_b,
          from and.intro (zero_le_a a_eq_zero) (zero_le_b b_eq_zero)
        },
      }
    end,
    have case_from : ∀{a b : ℕ}, ( 0 < a ∧ 0 < b ) → ( 0 < a * b ),
    from begin
      assume a b zero_lt_a_and_b,
      cases zero_lt_a_and_b with zero_lt_a zero_lt_b,
      have zero_lt_ab, from nat.mul_lt_mul_of_pos_left zero_lt_b zero_lt_a,
      rewrite [nat.mul_zero] at zero_lt_ab,
      from zero_lt_ab
    end,
    assume a b,
    from iff.intro case_to case_from
  end
  lemma ZERO_LT_of_Not_EQ_ZERO :
    ∀{a : ℕ},
    ¬ ( a = 0 ) →
    ---------------------------------
    ( 0 < a )
  | 0 := begin
    assume not_refl_zero,
    from absurd (eq.refl 0) not_refl_zero
  end
  | (a+1) := begin
    assume not_succ_eq_zero,
    rewrite [nat.add_comm],
    from nat.zero_lt_one_add a
  end
end use

/- Auxiliary Definitions -/
namespace aux
  universes u

  /- Methods for determining the size of nested lists -/
  -- The order of the following definitions is important
  class has_size (α : Type u) := (size : α → ℕ)
  instance is_default_size (α : Type u) : has_size α := ⟨ (λx, 1) ⟩
  -- First the size method checks if it has been given a list, if not it goes to its default case
  def size {α : Type u} [hcα : has_size α] : α → ℕ := has_size.size
  def list_size {α : Type u} [hcα : has_size α] : list α → ℕ
  | [] := 0
  | (h::l) := size h + list_size l
  -- Writing [hcα : has_size α] means that α ay have either is_list_size or is_default_size
  -- If [hcα : has_size α] is omitted, than α must have is_default_size
  instance is_list_size (α : Type u) [hcα : has_size α] : has_size (list α) := ⟨list_size⟩

  /- Properties about list size -/
  lemma Deafault_Size_EQ_Length {α : Type} :
    ∀{l : list α},
    ---------------------------
    ( list_size l = list.length l )
  | [] := by simp [list.length, list_size]
  | (HEAD::TAIL) := begin
    simp [list.length, list_size],
    simp [size, has_size.size],
    rewrite [Deafault_Size_EQ_Length],
    from nat.add_comm 1 (list.length TAIL)
  end
  lemma ZERO_LT_Length_of_LT_Size {α : Type} [hcα : has_size α] :
    ∀{l : list α}{num : ℕ},
    ( num < list_size l ) →
    ---------------------------
    ( 0 < list.length l )
  | [] num := begin
    assume num_lt_size,
    simp [list_size] at num_lt_size,
    from absurd num_lt_size (nat.not_lt_zero num)
  end
  | (HEAD::TAIL) num := begin
    assume num_lt_size,
    simp [list.length, nat.add_comm],
    from nat.zero_lt_one_add (list.length TAIL)
  end
end aux

/- Auxiliary Definitions (Leaf) -/
namespace a_leaf
  universes u

  /- Combinatory theorem about nested lists -/
  theorem Main_Combinatory_Nested {α : Type u} [hsα : aux.has_size α] :
    ∀{num : ℕ}{ll : list (list α)},
    ( (list.length ll) * num < aux.list_size ll ) →
    ---------------------------------
    ( ∃(l : list α), l ∈ ll ∧ num < aux.list_size l )
  | num [] := begin
    assume mul_lt_ll,
    simp [aux.list_size] at mul_lt_ll,
    rewrite [nat.mul_comm, nat.mul_zero] at mul_lt_ll,
    from false.elim (nat.not_lt_zero 0 mul_lt_ll)
  end
  | num (HEAD::TAIL) := begin
    assume mul_lt_ll,
    simp [aux.list_size] at mul_lt_ll,
    with_cases { by_cases num_lt_head : num < aux.size HEAD },
    case pos { --If HEAD is big
      apply exists.intro HEAD,
      simp [has_mem.mem, list.mem],
      from num_lt_head
    },
    case neg { --If HEAD isn't big
      with_cases { by_cases mul_lt_tail : (list.length TAIL) * num < aux.list_size TAIL },
      case pos { --If TAIL is big
        have main_combinatory, from Main_Combinatory_Nested mul_lt_tail,
        cases main_combinatory with la main_combinatory,
        cases main_combinatory with mem_la_tail num_lt_la,
        apply exists.intro la,
        simp [has_mem.mem, list.mem] at ⊢ mem_la_tail,
        simp [mem_la_tail],
        from num_lt_la
      },
      case neg { --If TAIL isn't big
        rewrite [nat.right_distrib (list.length TAIL) 1 num, nat.one_mul] at mul_lt_ll,
        rewrite [←use.GE_iff_Not_LT] at num_lt_head,
        rewrite [←use.GE_iff_Not_LT] at mul_lt_tail,
        have not_mul_lt_ll, from use.Add_GE_Add mul_lt_tail num_lt_head,
        rewrite [use.GE_iff_Not_LT, nat.add_comm (aux.list_size TAIL)] at not_mul_lt_ll,
        from absurd mul_lt_ll not_mul_lt_ll
      }
    }
  end
end a_leaf

/- Auxiliary Definitions (Branch) -/
namespace a_branch
  universes u

  /- Methods for counting the number diferent elements in a list -/
  def list_set {α : Type u} [eqα : decidable_eq α] : list α → list α
  | [] := []
  | (HEAD::TAIL) := if HEAD ∈ TAIL
                    then list_set TAIL
                    else HEAD :: list_set TAIL
  def list_filter {α : Type u} [eqα : decidable_eq α] : α → list α → list α
  | _ [] := []
  | a (HEAD::TAIL) := if a = HEAD
                      then HEAD :: list_filter a TAIL
                      else list_filter a TAIL
  def list_delete {α : Type u} [eqα : decidable_eq α] : α → list α → list α
  | _ [] := []
  | a (HEAD::TAIL) := if a = HEAD
                      then list_delete a TAIL
                      else HEAD :: list_delete a TAIL

  /- Properties about list set, filter, and delete (Used outside this namespace) -/
  lemma Length_Set_LE_Length_of_Subset {α : Type u} [eqα : decidable_eq α] :
    ∀{l1 l2 : list α},
    ( ∀(a : α), ( a ∈ l1 ) → ( a ∈ l2 ) ) →
    ---------------------------
    ( list.length (list_set l1) ≤ list.length l2 )
  | [] l2 := begin
    assume case_mem,
    simp [list_set],
    from nat.zero_le (list.length l2)
  end
  | (HEAD1::TAIL1) l2 := begin
    assume case_mem,
    have head1_mem_l2 : HEAD1 ∈ l2, from
    begin
      apply (case_mem HEAD1),
      simp [has_mem.mem, list.mem]
    end,
    have case_mem_tail1 : ∀ (a : α), a ∈ TAIL1 → a ∈ l2, from
    begin
      assume loop loop_mem_tail1,
      simp [has_mem.mem, list.mem] at case_mem,
      apply (case_mem loop),
      simp [has_mem.mem, list.mem] at loop_mem_tail1,
      simp [loop_mem_tail1]
    end,
    simp [list_set],
    with_cases { by_cases head1_mem_tail1 : HEAD1 ∈ TAIL1 },
    -- 
    case pos { simp [head1_mem_tail1], from Length_Set_LE_Length_of_Subset case_mem_tail1 },
    case neg {
      simp [head1_mem_tail1],
      have case_loop : ∀ (a : α), a ∈ TAIL1 → a ∈ list.remove_nth l2 (list.index_of HEAD1 l2),
      from begin
        assume loop loop_mem_tail1,
        have loop_mem_l2, from case_mem_tail1 loop loop_mem_tail1,
        have case_remove, from use.Mem_Remove_of_Mem_of_Not_Mem head1_mem_tail1 head1_mem_l2,
        from case_remove loop loop_mem_tail1 loop_mem_l2
      end,
      have loop, from Length_Set_LE_Length_of_Subset case_loop,
      have case_index, from use.Index_LT_Length_of_Mem head1_mem_l2,
      rewrite [list.length_remove_nth l2 (list.index_of HEAD1 l2) case_index] at loop,
      have one_le_l2, from nat.lt_of_le_of_lt (nat.zero_le (list.index_of HEAD1 l2)) case_index,
      rewrite [use.LT_ZERO_iff_LE_ONE] at one_le_l2,
      rewrite [←use.Sub_Add_Cancel one_le_l2],
      from nat.add_le_add loop (nat.le_refl 1)
    }
  end
  /- Properties about list set, filter, and delete (Used only within this namespace) -/
  lemma Mem_of_Mem_Delete {α : Type u} [eqα : decidable_eq α] :
    ∀{a1 a2 : α}{l : list α},
    ( a1 ∈ (list_delete a2 l) ) →
    ---------------------------
    ( a1 ∈ l )
  | a1 a2 [] := begin
    assume a1_mem_del,
    simp [list_delete, has_mem.mem, list.mem] at a1_mem_del,
    from false.elim a1_mem_del
  end
  | a1 a2 (HEAD::TAIL) := begin
    assume a1_mem_del,
    simp [list_delete, has_mem.mem, list.mem] at ⊢ a1_mem_del,
    with_cases { by_cases a2_eq_head : a2 = HEAD },
    case pos { -- If HEAD = a2
      simp [a2_eq_head] at a1_mem_del,
      have loop, from Mem_of_Mem_Delete a1_mem_del,
      simp [has_mem.mem, list.mem] at ⊢ loop,
      simp [loop]
    },
    case neg { -- If HEAD ≠ a2
      simp [a2_eq_head, list.mem] at a1_mem_del,
      cases a1_mem_del with a1_eq_head a1_mem_del,
      case or.inl { simp [a1_eq_head] },
      case or.inr {
        have loop, from Mem_of_Mem_Delete a1_mem_del,
        simp [has_mem.mem, list.mem] at ⊢ loop,
        simp [loop]
      }
    }
  end
  lemma Size_Filter_Delete {α : Type u} [eqα : decidable_eq α] :
    ∀(a : α)(l : list α),
    ---------------------------
    ( aux.list_size (list_filter a (list_delete a l)) = 0 )
  | a [] := by simp [list_delete, list_filter, aux.list_size]
  | a (HEAD::TAIL) := begin
    with_cases { by_cases a_eq_head : a = HEAD },
    case pos { -- If a = HEAD
      simp [a_eq_head, list_delete],
      from Size_Filter_Delete HEAD TAIL
    },
    case neg { -- If a ≠ HEAD
      simp [a_eq_head, list_delete, list_filter],
      from Size_Filter_Delete a TAIL
    }
  end
  lemma Size_Delete_LE_Size {α : Type u} [eqα : decidable_eq α] :
    ∀(a1 a2 : α)(l : list α),
    ---------------------------
    ( aux.list_size (list_filter a1 (list_delete a2 l)) ≤ aux.list_size (list_filter a1 l)  )
  | a1 a2 [] := by simp [list_delete, list_filter]
  | a1 a2 (HEAD::TAIL) := begin
    simp [list_delete],
    with_cases { by_cases a2_eq_head : a2 = HEAD },
    case pos { -- If a2 = HEAD
      simp [a2_eq_head, list_filter],
      with_cases { by_cases a1_eq_head : a1 = HEAD },
      case pos { -- If a1 = HEAD
        simp [a1_eq_head, aux.list_size],
        from use.LE_Add_Left (Size_Delete_LE_Size HEAD HEAD TAIL) (aux.size HEAD)
      },
      case neg { -- If a1 ≠ HEAD
        simp [a1_eq_head, aux.list_size],
        from Size_Delete_LE_Size a1 HEAD TAIL
      }
    },
    case neg { -- If a2 ≠ HEAD
      simp [a2_eq_head, list_filter],
      with_cases { by_cases a1_eq_head : a1 = HEAD },
      case pos { -- If a1 = HEAD
        simp [a1_eq_head, aux.list_size],
        from nat.add_le_add (nat.le_refl (aux.size HEAD)) (Size_Delete_LE_Size HEAD a2 TAIL)
      },
      case neg { -- If a1 ≠ HEAD
        simp [a1_eq_head, aux.list_size],
        from Size_Delete_LE_Size a1 a2 TAIL
      }
    }
  end
  lemma Size_Filter_Delete_EQ_Size {α : Type u} [eqα : decidable_eq α] :
    ∀(a : α)(l : list α),
    ---------------------------
    ( aux.list_size (list_filter a l) + aux.list_size (list_delete a l) = aux.list_size l )
  | a [] := by simp [list_delete, list_filter, aux.list_size]
  | a (HEAD::TAIL) := begin
    simp [list_filter, list_delete],
    with_cases { by_cases a_eq_head : a = HEAD },
    case pos { -- If a = HEAD
      simp [a_eq_head, aux.list_size],
      rewrite [nat.add_assoc],
      have loop, from Size_Filter_Delete_EQ_Size HEAD TAIL,
      from use.Add_Left_EQ_of_EQ loop (aux.size HEAD)
    },
    case neg { -- If a ≠ HEAD
      simp [a_eq_head, aux.list_size],
      rewrite [←nat.add_assoc],
      rewrite [nat.add_comm (aux.list_size (list_filter a TAIL)) (aux.size HEAD)],
      rewrite [nat.add_assoc],
      have loop, from Size_Filter_Delete_EQ_Size a TAIL,
      from use.Add_Left_EQ_of_EQ loop (aux.size HEAD)
    }
  end
  /- Properties about list set, filter, and delete (Must be left in order) -/
  lemma Case_Not_Mem_Del {α : Type u} [eqα : decidable_eq α] :
    ∀{a1 a2 : α}{l : list α},
    ( a2 ≠ a1 ) →
    ( a1 ∉ l ) →
    ---------------------------
    ( a1 ∉ list_delete a2 l )
  | a1 a2 [] := by simp [list_delete]
  | a1 a2 (HEAD::TAIL) := begin
    assume a1_ne_a2 a1_not_mem,
    simp [has_mem.mem, list.mem] at a1_not_mem,
    rewrite [use.Not_Or_iff_And_Not] at a1_not_mem,
    cases a1_not_mem with a1_ne_head a1_not_mem_tail,
    --
    with_cases { by_cases a2_eq_head : a2 = HEAD },
    case pos { -- If a2 = HEAD
      simp [a2_eq_head, list_delete] at ⊢ a1_ne_a2,
      rewrite [eq_comm] at a1_ne_head,
      from Case_Not_Mem_Del a1_ne_head a1_not_mem_tail
    },
    case neg { -- If a2 ≠ HEAD
      simp [a2_eq_head, list_delete],
      from use.Not_Or a1_ne_head (Case_Not_Mem_Del a1_ne_a2 a1_not_mem_tail)
    }
  end
  lemma Case_Mem_Del {α : Type u} [eqα : decidable_eq α] :
    ∀{a1 a2 : α}{l : list α},
    ( a2 ≠ a1 ) →
    ( a1 ∈ l ) →
    ---------------------------
    ( a1 ∈ list_delete a2 l )
  | a1 a2 [] := begin
    assume a1_ne_a2 a1_mem,
    simp [list_delete] at a1_mem,
    from false.elim a1_mem
  end
  | a1 a2 (HEAD::TAIL) := begin
    assume a1_ne_a2 a1_mem,
    simp [has_mem.mem, list.mem] at a1_mem,
    --
    with_cases { by_cases a2_eq_head : a2 = HEAD },
    case pos { -- If a2 = HEAD
      simp [a2_eq_head, list_delete] at ⊢ a1_ne_a2,
      cases a1_mem with a1_eq_head a1_mem_tail,
      case or.inl { rewrite [eq_comm] at a1_eq_head, from absurd a1_eq_head a1_ne_a2 },
      case or.inr { from Case_Mem_Del a1_ne_a2 a1_mem_tail }
    },
    case neg { -- If a2 ≠ HEAD
      simp [a2_eq_head, list_delete],
      cases a1_mem with a1_eq_head a1_mem_tail,
      case or.inl { simp [a1_eq_head] },
      case or.inr { simp [Case_Mem_Del a1_ne_a2 a1_mem_tail] }
    }
  end
  lemma Lenght_EQ_Lenght_Set_Delete {α : Type u} [eqα : decidable_eq α] :
    ∀(a : α)(l : list α),
    ---------------------------
    ( list.length (list_set (a::l)) = 1 + list.length (list_set (list_delete a l)) )
  | a [] := by simp [list_delete, list_set]
  | a (HEAD::TAIL) := begin
    have loop_head, from Lenght_EQ_Lenght_Set_Delete HEAD TAIL,
    have loop_a, from Lenght_EQ_Lenght_Set_Delete a TAIL,
    simp [list_delete] at ⊢ loop_head loop_a,
    with_cases { by_cases a_eq_head : a = HEAD },
    case pos { -- If a = HEAD
      simp [a_eq_head, list_set] at ⊢ loop_head,
      with_cases { by_cases head_mem_tail : HEAD ∈ TAIL },
      case pos { -- If HEAD ∈ TAIL
        simp [head_mem_tail, list.length] at ⊢ loop_head,
        from loop_head
      },
      case neg { -- If HEAD ∉ TAIL
        simp [head_mem_tail, list.length] at ⊢ loop_head,
        from loop_head
      }
    },
    case neg { -- If a ≠ HEAD
      simp [a_eq_head, list_set] at ⊢ loop_a,
      with_cases { by_cases a_mem_tail : a ∈ TAIL },
      case pos { -- If a ∈ TAIL
        simp [a_mem_tail, list.length] at ⊢ loop_a,
        with_cases { by_cases head_mem_tail : HEAD ∈ TAIL },
        case pos { -- If HEAD ∈ TAIL
          simp [head_mem_tail, list.length] at ⊢ loop_a,
          simp [Case_Mem_Del a_eq_head head_mem_tail],
          from loop_a
        },
        case neg { -- If HEAD ∉ TAIL
          simp [head_mem_tail, list.length] at ⊢ loop_a,
          simp [Case_Not_Mem_Del a_eq_head head_mem_tail],
          rewrite [nat.add_comm (list.length (list_set TAIL)) 1],
          rewrite [nat.add_comm] at loop_a,
          from use.Add_Left_EQ_of_EQ loop_a 1
        }
      },
      case neg { -- If a ∉ TAIL
        simp [a_mem_tail, list.length] at ⊢ loop_a,
        with_cases { by_cases head_mem_tail : HEAD ∈ TAIL },
        case pos { -- If HEAD ∈ TAIL
          simp [head_mem_tail, list.length] at ⊢ loop_a,
          simp [Case_Mem_Del a_eq_head head_mem_tail],
          from loop_a
        },
        case neg { -- If HEAD ∉ TAIL
          simp [head_mem_tail, list.length] at ⊢ loop_a,
          simp [Case_Not_Mem_Del a_eq_head head_mem_tail],
          rewrite [nat.add_comm 1 (list.length (list_set (list_delete a TAIL)))] at loop_a,
          rewrite [nat.add_comm (list.length (list_set TAIL) + 1)  1],
          from use.Add_Left_EQ_of_EQ loop_a 1
        }
      }
    }
  end

  /- Combinatory theorem about lists (Filter) -/
  theorem Main_Combinatory_Filter {α : Type} [eqα : decidable_eq α] :
    ∀(num : ℕ)(l : list α),
    ( list.length (list_set l) * num < aux.list_size l ) →
    ---------------------------------
    ( ∃(a : α), a ∈ l ∧ num < aux.list_size (list_filter a l) )
  | num [] := begin
    assume mul_lt_l,
    simp [aux.list_size] at mul_lt_l,
    from false.elim (nat.not_lt_zero (list.length (list_set []) * num) mul_lt_l)
  end
  | num (HEAD::TAIL) := begin
    assume mul_lt_l,
    with_cases { by_cases num_lt_head : num < 1 + aux.list_size (list_filter HEAD TAIL) },
    case pos { -- If list_filter HEAD (HEAD::TAIL) is big
      apply exists.intro HEAD,
      simp [list_filter, aux.list_size, has_mem.mem, list.mem, aux.size, aux.has_size.size],
      from num_lt_head
    },
    case neg { -- If list_filter HEAD (HEAD::TAIL) isn't big
      with_cases { by_cases mul_lt_del : list.length (list_set (list_delete HEAD TAIL)) * num < aux.list_size (list_delete HEAD TAIL) },
      case pos { -- If list_delete HEAD (HEAD::TAIL) is big
        have main_combinatory : ∃(a : α), a ∈ list_delete HEAD TAIL ∧ num < aux.list_size (list_filter a (list_delete HEAD TAIL)),
          from Main_Combinatory_Filter num (list_delete HEAD TAIL) mul_lt_del, -- sorry,
        cases main_combinatory with a main_combinatory,
        cases main_combinatory with a_mem_del num_lt_a,
        apply exists.intro a,
        simp [has_mem.mem, list.mem] at ⊢ a_mem_del,
        simp [a_mem_del, list_filter],
        with_cases { by_cases a_eq_head : a = HEAD },
        case pos { -- If a = HEAD
          rewrite [a_eq_head] at num_lt_a a_mem_del,
          rewrite [Size_Filter_Delete HEAD TAIL] at num_lt_a,
          from absurd num_lt_a (nat.not_lt_zero num)
        },
        case neg { -- If a ≠ HEAD
          simp [a_eq_head],
          have a_mem_tail, from Mem_of_Mem_Delete a_mem_del,
          simp [has_mem.mem] at a_mem_tail,
          simp [a_mem_tail],
          from nat.lt_of_lt_of_le num_lt_a (Size_Delete_LE_Size a HEAD TAIL)
        }
      },
      case neg { --If list_delete HEAD (HEAD::TAIL) isn't big
        rewrite [Lenght_EQ_Lenght_Set_Delete, nat.right_distrib, nat.one_mul] at mul_lt_l,
        simp [list_delete, aux.list_size, aux.size, aux.has_size.size] at mul_lt_l,
        rewrite [←use.GE_iff_Not_LT] at mul_lt_del,
        rewrite [←use.GE_iff_Not_LT] at num_lt_head,
        have mul_ge_l, from use.Add_GE_Add num_lt_head mul_lt_del,
        rewrite [nat.add_assoc, Size_Filter_Delete_EQ_Size] at mul_ge_l,
        rewrite [use.GE_iff_Not_LT] at mul_ge_l,
        -- This proof is the same as Main_Combinatory_Nested
        from absurd mul_lt_l mul_ge_l
      }
    }
  end using_well_founded
  -- So that the recursion is explicitly done over the list-type
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ t, list.sizeof t.snd)⟩] }
  -- L∃∀N gives us a warning that the recursion at Main_Combinatory_Filter is not a well founded relation
  --  @has_well_founded.r (Σ' (num : ℕ), list α)
  --    (@has_well_founded.mk (Σ' (num : ℕ), list α)
  --       (@measure (Σ' (num : ℕ), list α)
  --          (λ (t : Σ' (num : ℕ), list α), @list.sizeof α (default_has_sizeof α) t.snd))
  --       _)
  --  The nested exception message contains the failure state for the decreasing tactic:
  --  ⊢ (list_delete HEAD TAIL).sizeof < 1 + 0 + TAIL.sizeof
  -- However, we show this target is true for all type-instances
  -- Proving that, despite the warning, the recursion used in Main_Combinatory_Filter is well-founded
  lemma Well_Founded_Delete {α : Type u} [eqα : decidable_eq α] :
    ∀(head : α)(tail : list α),
    ---------------------------------
    ( list.sizeof (list_delete head tail) < 1 + 0 + list.sizeof tail )
  | head [] := begin
    rewrite [nat.add_zero],
    simp [list_delete], simp [list.sizeof],
    have del_lt_sizeof, from nat.add_lt_add_left nat.zero_lt_one 1,
    rewrite [nat.add_zero] at del_lt_sizeof,
    from del_lt_sizeof
  end
  | head (HEAD::TAIL) := begin
    rewrite [nat.add_zero],
    simp [list_delete],
    with_cases { by_cases eq_head : head = HEAD },
    case pos { -- If head = HEAD
      simp [eq_head], simp [list.sizeof],
      have loop_0, from Well_Founded_Delete HEAD TAIL,
      have loop_1, from use.LT_Add_Right loop_0 (sizeof HEAD),
      rewrite [nat.add_assoc] at loop_1,
      from use.LT_Add_Left loop_1 1
    },
    case neg { -- If head ≠ HEAD
      simp [eq_head], simp [list.sizeof],
      have loop_0, from Well_Founded_Delete head TAIL,
      have loop_1, from nat.add_lt_add_left loop_0 (sizeof HEAD),
      rewrite [←nat.add_assoc] at loop_1,
      rewrite [nat.add_comm (sizeof HEAD) 1] at loop_1,
      have loop_2, from nat.add_lt_add_left loop_1 1,
      rewrite [←nat.add_assoc] at loop_2,
      from loop_2
    }
  end
end a_branch

/- Type Definitions and Properties -/
namespace types
  /- Inductive Types: Formula -/
  inductive formula
  | atom (SBL : ℕ) : formula
  | implication (ANT CON : formula) : formula
  export formula (atom implication)
  notation #SBL := formula.atom SBL
  notation ANT >> CON := formula.implication ANT CON
  /- Inductive Types: Proof-Graph -/
  inductive node_option
  | leaf : node_option
  | node : node_option
  export node_option (leaf node)
  inductive tree
  -- Top Formulas and Hypotheses
  | leaf (LVL : ℕ) (FML : formula) : tree
  -- Nodes resulting from →Introduction
  | u_tree (LVL : ℕ) (FML : formula) (UNI : tree) : tree
  -- Nodes resulting from →Elimination
  | lr_tree (LVL : ℕ) (FML : formula) (MNR MJR : tree) : tree
  export tree (leaf u_tree lr_tree)
  inductive branch
  -- The First Node of the Branch (Always a leaf when a Proof-Branch)
  | leaf (BRC : branch) (OPT : node_option) (LVL : ℕ) (FML : formula) : branch
  -- Nodes resulting from →Introduction
  | u_branch (BRC : branch) (OPT : node_option) (LVL : ℕ) (FML : formula) : branch
  -- Nodes resulting from →Elimination, connected to their Minor Premise
  | l_branch (BRC : branch) (OPT : node_option) (LVL : ℕ) (FML : formula) : branch
  -- Nodes resulting from →Elimination, connected to their Major Premise
  | r_branch (BRC : branch) (OPT : node_option) (LVL : ℕ) (FML : formula) : branch
  -- Pointer to the Ending of the Branch (Always the Root of the Proof-Tree before Pruning)
  | root : branch
  export branch (leaf u_branch l_branch r_branch root)

  /- Instances of Decidability (Equality): Formula -/
  instance formula.decidable_eq :
    ∀(f1 f2 : formula),
    ---------------------------------
    decidable (f1 = f2)
  -- ATOM:
  | (atom SBL1) (atom SBL2) := begin simp [eq.decidable], from @nat.decidable_eq SBL1 SBL2 end
  | (atom _) (implication _ _) := begin simp [eq.decidable], from is_false not_false end
  -- IMPLICATION:
  | (implication _ _) (atom _) := begin simp [eq.decidable], from is_false not_false end
  | (implication ANT1 CON1) (implication ANT2 CON2) := begin
    simp [eq.decidable],
    from @and.decidable (ANT1 = ANT2) (CON1 = CON2) (@formula.decidable_eq ANT1 ANT2) (@formula.decidable_eq CON1 CON2)
  end
  /- Instances of Decidability (Equality): Proof-Graph -/
  instance node_option.decidable_eq :
    ∀(opt1 opt2 : node_option),
    ---------------------------------
    decidable (opt1 = opt2)
  -- LEAF:
  | leaf leaf := begin simp [eq.decidable], from is_true trivial end
  | leaf node := begin simp [eq.decidable], from is_false not_false end
  -- NODE:
  | node leaf := begin simp [eq.decidable], from is_false not_false end
  | node node := begin simp [eq.decidable], from is_true trivial end
  instance tree.decidable_eq :
    ∀(t1 t2 : tree),
    ---------------------------------
    decidable (t1 = t2)
  -- LEAF:
  | (leaf LVL1 FML1) (leaf LVL2 FML2) := begin
    simp [eq.decidable],
    from @and.decidable (LVL1 = LVL2) (FML1 = FML2) (@nat.decidable_eq LVL1 LVL2) (@formula.decidable_eq FML1 FML2)
  end
  | (leaf _ _) (u_tree _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (leaf _ _) (lr_tree _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  -- U_Tree:
  | (u_tree _ _ UNI1) (leaf _ _) := begin simp [eq.decidable], from is_false not_false end
  | (u_tree LVL1 FML1 UNI1) (u_tree LVL2 FML2 UNI2) := begin
    simp [eq.decidable],
    have dec_and1, from @and.decidable (FML1 = FML2) (UNI1 = UNI2) (@formula.decidable_eq FML1 FML2) (@tree.decidable_eq UNI1 UNI2),
    from @and.decidable (LVL1 = LVL2) (FML1 = FML2 ∧ UNI1 = UNI2) (@nat.decidable_eq LVL1 LVL2) dec_and1
  end
  | (u_tree _ _ _) (lr_tree _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  -- LR_Tree:
  | (lr_tree _ _ MNR1 MJR1) (leaf _ _) := begin simp [eq.decidable], from is_false not_false end
  | (lr_tree _ _ MNR1 MJR1) (u_tree _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (lr_tree LVL1 FML1 MNR1 MJR1) (lr_tree LVL2 FML2 MNR2 MJR2) := begin
    simp [eq.decidable],
    have dec_and1, from @and.decidable (MNR1 = MNR2) (MJR1 = MJR2) (@tree.decidable_eq MNR1 MNR2) (@tree.decidable_eq MJR1 MJR2),
    have dec_and2, from @and.decidable (FML1 = FML2) (MNR1 = MNR2 ∧ MJR1 = MJR2) (@formula.decidable_eq FML1 FML2) dec_and1,
    from @and.decidable (LVL1 = LVL2) (FML1 = FML2 ∧ MNR1 = MNR2 ∧ MJR1 = MJR2) (@nat.decidable_eq LVL1 LVL2) dec_and2
  end
  instance branch.decidable_eq :
    ∀(p1 p2 : branch),
    ---------------------------------
    decidable (p1 = p2)
  -- LEAF:
  | (leaf BRC1 OPT1 LVL1 FML1) (leaf BRC2 OPT2 LVL2 FML2) := begin
    simp [eq.decidable],
    have dec_and1, from @and.decidable (LVL1 = LVL2) (FML1 = FML2) (@nat.decidable_eq LVL1 LVL2) (@formula.decidable_eq FML1 FML2),
    have dec_and2, from @and.decidable (OPT1 = OPT2) (LVL1 = LVL2 ∧ FML1 = FML2) (@node_option.decidable_eq OPT1 OPT2) dec_and1,
    from @and.decidable (BRC1 = BRC2) (OPT1 = OPT2 ∧ LVL1 = LVL2 ∧ FML1 = FML2) (@branch.decidable_eq BRC1 BRC2) dec_and2
  end
  | (leaf _ _ _ _) (u_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (leaf _ _ _ _) (l_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (leaf _ _ _ _) (r_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (leaf _ _ _ _) root := begin simp [eq.decidable], from is_false not_false end
  -- U_Path:
  | (u_branch _ _ _ _) (leaf _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (u_branch BRC1 OPT1 LVL1 FML1) (u_branch BRC2 OPT2 LVL2 FML2) := begin
    simp [eq.decidable],
    have dec_and1, from @and.decidable (LVL1 = LVL2) (FML1 = FML2) (@nat.decidable_eq LVL1 LVL2) (@formula.decidable_eq FML1 FML2),
    have dec_and2, from @and.decidable (OPT1 = OPT2) (LVL1 = LVL2 ∧ FML1 = FML2) (@node_option.decidable_eq OPT1 OPT2) dec_and1,
    from @and.decidable (BRC1 = BRC2) (OPT1 = OPT2 ∧ LVL1 = LVL2 ∧ FML1 = FML2) (@branch.decidable_eq BRC1 BRC2) dec_and2
  end
  | (u_branch _ _ _ _) (l_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (u_branch _ _ _ _) (r_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (u_branch _ _ _ _) root := begin simp [eq.decidable], from is_false not_false end
  -- L_Path:
  | (l_branch _ _ _ _) (leaf _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (l_branch _ _ _ _) (u_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (l_branch BRC1 OPT1 LVL1 FML1) (l_branch BRC2 OPT2 LVL2 FML2) := begin
    simp [eq.decidable],
    have dec_and1, from @and.decidable (LVL1 = LVL2) (FML1 = FML2) (@nat.decidable_eq LVL1 LVL2) (@formula.decidable_eq FML1 FML2),
    have dec_and2, from @and.decidable (OPT1 = OPT2) (LVL1 = LVL2 ∧ FML1 = FML2) (@node_option.decidable_eq OPT1 OPT2) dec_and1,
    from @and.decidable (BRC1 = BRC2) (OPT1 = OPT2 ∧ LVL1 = LVL2 ∧ FML1 = FML2) (@branch.decidable_eq BRC1 BRC2) dec_and2
  end
  | (l_branch _ _ _ _) (r_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (l_branch _ _ _ _) root := begin simp [eq.decidable], from is_false not_false end
  -- R_Path:
  | (r_branch _ _ _ _) (leaf _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (r_branch _ _ _ _) (u_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (r_branch _ _ _ _) (l_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | (r_branch BRC1 OPT1 LVL1 FML1) (r_branch BRC2 OPT2 LVL2 FML2) := begin
    simp [eq.decidable],
    have dec_and1, from @and.decidable (LVL1 = LVL2) (FML1 = FML2) (@nat.decidable_eq LVL1 LVL2) (@formula.decidable_eq FML1 FML2),
    have dec_and2, from @and.decidable (OPT1 = OPT2) (LVL1 = LVL2 ∧ FML1 = FML2) (@node_option.decidable_eq OPT1 OPT2) dec_and1,
    from @and.decidable (BRC1 = BRC2) (OPT1 = OPT2 ∧ LVL1 = LVL2 ∧ FML1 = FML2) (@branch.decidable_eq BRC1 BRC2) dec_and2
  end
  | (r_branch _ _ _ _) root := begin simp [eq.decidable], from is_false not_false end
  -- ROOT:
  | root (leaf _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | root (u_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | root (l_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | root (r_branch _ _ _ _) := begin simp [eq.decidable], from is_false not_false end
  | root root := begin simp [eq.decidable], from is_true trivial end

  /- Get Methods: Formula -/
  def is_atomic : formula → Prop
  | (atom _) := true
  | (implication _ _) := false
    instance formula.is_atomic :
      ∀(f : formula),
      ---------------------------------
      decidable (is_atomic f)
    | (atom _) := begin simp [is_atomic], from is_true trivial end
    | (implication _ _) := begin simp [is_atomic], from is_false not_false end
  def not_atomic : formula → Prop
  | (atom _) := false
  | (implication _ _) := true
    instance formula.not_atomic :
      ∀(f : formula),
      ---------------------------------
      decidable (not_atomic f)
    | (atom _) := begin simp [not_atomic], from is_false not_false end
    | (implication _ _) := begin simp [not_atomic], from is_true trivial end
  def get_antecedent : formula → formula
  | (atom SBL) := #0 -- NULL
  | (implication ANT _) := ANT
  def get_consequent : formula → formula
  | (atom SBL) := #0 -- NULL
  | (implication _ CON) := CON
  /- Get Methods: Proof-Graph -/
  def not_root : branch → Prop
  | (leaf _ _ _ _) := true
  | (u_branch _ _ _ _) := true
  | (l_branch _ _ _ _) := true
  | (r_branch _ _ _ _) := true
  | root := false
    instance branch.not_root :
      ∀(b : branch),
      ---------------------------------
      decidable (not_root b)
    | (leaf _ _ _ _) := begin simp [not_root], from is_true trivial end
    | (u_branch _ _ _ _) := begin simp [not_root], from is_true trivial end
    | (l_branch _ _ _ _) := begin simp [not_root], from is_true trivial end
    | (r_branch _ _ _ _) := begin simp [not_root], from is_true trivial end
    | root := begin simp [not_root], from is_false not_false end
  def get_option : branch → node_option
  | (leaf _ OPT _ _) := OPT
  | (u_branch _ OPT _ _) := OPT
  | (l_branch _ OPT _ _) := OPT
  | (r_branch _ OPT _ _) := OPT
  | root := node -- NULL
  def get_level : branch → ℕ
  | (leaf _ _ LVL _) := LVL
  | (u_branch _ _ LVL _) := LVL
  | (l_branch _ _ LVL _) := LVL
  | (r_branch _ _ LVL _) := LVL
  | root := 0 -- NULL
  def get_formula : branch → formula
  | (leaf _ _ _ FML) := FML
  | (u_branch _ _ _ FML) := FML
  | (l_branch _ _ _ FML) := FML
  | (r_branch _ _ _ FML) := FML
  | root := #0 -- NULL

  /- Numbber of Levels and Formulas -/
  def list_levels : tree → list (ℕ)
  | (leaf LVL _) := [LVL]
  | (u_tree LVL _ UNI) := if LVL ∈ list_levels UNI
                          then list_levels UNI
                          else [LVL] ++ list_levels UNI
  | (lr_tree LVL _ MNR MJR) := if LVL ∈ (list_levels MNR ∩ list_levels MJR)
                               then (list_levels MNR ∩ list_levels MJR)
                               else [LVL] ++ (list_levels MNR ∩ list_levels MJR)
  def list_formulas : tree → list (formula)
  | (leaf _ FML) := [FML]
  | (u_tree _ FML UNI) := if FML ∈ list_formulas UNI
                          then list_formulas UNI
                          else [FML] ++ list_formulas UNI
  | (lr_tree _ FML MNR MJR) := if FML ∈ (list_formulas MNR ∩ list_formulas MJR)
                               then (list_formulas MNR ∩ list_formulas MJR)
                               else [FML] ++ (list_formulas MNR ∩ list_formulas MJR)
  def count_levels : tree → ℕ
  | t := list.length (list_levels t)
  def count_formulas : tree → ℕ
  | t := list.length (list_formulas t)

  /- For this proof, trees are viewed as lists of nodes(which are also trees) -/
  -- The lists are arranged in an orderly fashion, splitting the tree by types of node, levels, and formulas
  -- The lists return a branch from the original tree's root to a node given by the by type/level/formula
  def loop_tree_option_level_formula : branch → tree → node_option → ℕ → formula → list (branch)
  -- Matched node_option with the type of tree constructor
  | BRC (leaf LVL FML) leaf lvl fml :=
    if LVL=lvl ∧ FML=fml
    then [leaf BRC leaf LVL FML]
    else []
  | BRC (u_tree LVL FML UNI) node lvl fml :=
    if LVL=lvl ∧ FML=fml
    then [leaf BRC node LVL FML]
    else loop_tree_option_level_formula (u_branch BRC node LVL FML) UNI node lvl fml
  | BRC (lr_tree LVL FML MNR MJR) node lvl fml :=
    if LVL=lvl ∧ FML=fml
    then [leaf BRC node LVL FML]
    else loop_tree_option_level_formula (l_branch BRC node LVL FML) MNR node lvl fml
      ++ loop_tree_option_level_formula (r_branch BRC node LVL FML) MJR node lvl fml
  -- Mismatched node_option with the type of tree constructor
  | BRC (leaf LVL FML) node lvl fml := []
  | BRC (u_tree LVL FML UNI) leaf lvl fml := loop_tree_option_level_formula (u_branch BRC node LVL FML) UNI leaf lvl fml
  | BRC (lr_tree LVL FML MNR MJR) leaf lvl fml := loop_tree_option_level_formula (l_branch BRC node LVL FML) MNR leaf lvl fml
                                               ++ loop_tree_option_level_formula (r_branch BRC node LVL FML) MJR leaf lvl fml
  -- Returns all the nodes in the tree, with a given constructor, at a given level, and with a specific formula
  def list_tree_option_level_formula : tree → node_option → ℕ → formula → list (branch)
  | t opt lvl fml := loop_tree_option_level_formula root t opt lvl fml
  -- Returns all the nodes in the tree, with a given constructor, and at a given level
  def loop_tree_option_level : tree → node_option → ℕ → list (formula) → list (list (branch))
  | t opt lvl [] := []
  | t opt lvl (HEAD::TAIL) := [list_tree_option_level_formula t opt lvl HEAD]
                           ++ loop_tree_option_level t opt lvl TAIL
  def list_tree_option_level : tree → node_option → ℕ → list (list (branch))
  | t opt lvl := loop_tree_option_level t opt lvl (list_formulas t)
  -- Returns all the nodes in the tree, with a given constructor
  def loop_tree_option :tree → node_option → list (ℕ) → list (list (list (branch)))
  | t opt [] := []
  | t opt (HEAD::TAIL) := [list_tree_option_level t opt HEAD]
                       ++ loop_tree_option t opt TAIL
  def list_tree_option : tree → node_option → list (list (list (branch)))
  | t opt := loop_tree_option t opt (list_levels t)
  -- Returns all the nodes in the tree
  def list_tree : tree → list (list (list (list (branch))))
  | t := [list_tree_option t leaf] ++ [list_tree_option t node]

  /- Prooving the correctness of the list_tree_option_level_formula method -/
  lemma Loop_Level_Formula_Option :
    ∀(mem b : branch)(t : tree)(opt : node_option)(lvl : ℕ)(fml : formula),
    ( mem ∈ loop_tree_option_level_formula b t opt lvl fml ) →
    ---------------------------
    ( (get_option mem = opt) ∧ (get_level mem = lvl) ∧ (get_formula mem = fml) )
  -- When mem and opt match
  | mem BRC (leaf LVL FML) leaf lvl fml := begin
    assume mem_node,
    -- Simplifying ∈ at the condition(mem_node)
    simp [loop_tree_option_level_formula] at mem_node,
    simp [has_mem.mem] at mem_node,
    simp [use.ITE_Distribution (list.mem mem)] at mem_node,
    simp [list.mem] at mem_node,
    -- Cases over (LVL=lvl ∧ FML=fml)
    with_cases { by_cases and_eq : (LVL=lvl ∧ FML=fml) },
    case pos { simp [and_eq] at mem_node, simp [mem_node, get_option, get_level, get_formula] },
    -- The case where ¬(LVL=lvl ∧ FML=fml) is impossible, since b ∉ []
    case neg { simp [and_eq] at mem_node, from false.elim mem_node }
  end
  | mem BRC (u_tree LVL FML UNI) node lvl fml := begin
    assume mem_node,
    -- Simplifying ∈ at the condition(mem_node)
    simp [loop_tree_option_level_formula] at mem_node,
    simp [has_mem.mem] at mem_node,
    simp [use.ITE_Distribution (list.mem mem)] at mem_node,
    simp [list.mem] at mem_node,
    -- Cases over (LVL=lvl ∧ FML=fml)
    with_cases { by_cases and_eq : (LVL=lvl ∧ FML=fml) },
    case pos { simp [and_eq] at mem_node, simp [mem_node, get_option, get_level, get_formula] },
    -- The case where ¬(LVL=lvl ∧ FML=fml) continues up the single child
    case neg {
      simp [and_eq] at mem_node,
      from Loop_Level_Formula_Option mem (u_branch BRC node LVL FML) UNI node lvl fml mem_node
    }
  end
  | mem BRC (lr_tree LVL FML MNR MJR) node lvl fml := begin
    assume mem_node,
    -- Simplifying ∈ at the condition(mem_node)
    simp [loop_tree_option_level_formula] at mem_node,
    simp [has_mem.mem] at mem_node,
    simp [use.ITE_Distribution (list.mem mem)] at mem_node,
    simp [list.mem] at mem_node,
    -- Cases over (LVL=lvl ∧ FML=fml)
    with_cases { by_cases and_eq : (LVL=lvl ∧ FML=fml) },
    case pos { simp [and_eq] at mem_node, simp [mem_node, get_option, get_level, get_formula] },
    -- The case where ¬(LVL=lvl ∧ FML=fml) continues up both children
    case neg {
      simp [and_eq] at mem_node,
      -- Using the relation between append[++] and or[∨] regarding item membership over lists
      have or_mem_node, from (iff.elim_left list.mem_append) mem_node,
      cases or_mem_node with mem_node mem_node,
      case or.inl { from Loop_Level_Formula_Option mem (l_branch BRC node LVL FML) MNR node lvl fml mem_node },
      case or.inr { from Loop_Level_Formula_Option mem (r_branch BRC node LVL FML) MJR node lvl fml mem_node }
    }
  end
  -- When mem and opt don't match
  | mem BRC (leaf LVL FML) node lvl fml := begin
    assume mem_node,
    simp [loop_tree_option_level_formula] at mem_node,
    from false.elim mem_node
  end
  | mem BRC (u_tree LVL FML UNI) leaf lvl fml := begin
    assume mem_node,
    simp [loop_tree_option_level_formula] at mem_node,
    from Loop_Level_Formula_Option mem (u_branch BRC node LVL FML) UNI leaf lvl fml mem_node
  end
  | mem BRC (lr_tree LVL FML MNR MJR) leaf lvl fml := begin
    simp [loop_tree_option_level_formula],
    assume mem_node, cases mem_node,
    case or.inl { from Loop_Level_Formula_Option mem (l_branch BRC node LVL FML) MNR leaf lvl fml mem_node },
    case or.inr { from Loop_Level_Formula_Option mem (r_branch BRC node LVL FML) MJR leaf lvl fml mem_node }
  end
  lemma From_Level_Formula_Option :
    ∀(mem : branch)(t : tree)(opt : node_option)(lvl : ℕ)(fml : formula),
    ( mem ∈ list_tree_option_level_formula t opt lvl fml ) →
    ---------------------------
    ( (get_option mem = opt) ∧ (get_level mem = lvl) ∧ (get_formula mem = fml) )
  | mem t opt lvl fml := begin
    assume mem_node,
    simp [list_tree_option_level_formula] at mem_node,
    from Loop_Level_Formula_Option mem root t opt lvl fml mem_node
  end
end types
export types.formula (atom implication)
export types.node_option (leaf node)
export types.tree (leaf u_tree lr_tree)
export types.branch (leaf u_branch l_branch r_branch root)

/- Proof: Leaf Redundancy -/
namespace p_leaf
  /- Restrictions Regarding Proof-Trees -/
  -- Trees must be finite, meaning that every node must have a path ending on a leaf
  def is_finite : types.tree → Prop
  | t :=
    ∀(lvl : ℕ),
    ---------------------------
    ( aux.list_size (types.list_tree_option_level t node lvl) ≤ aux.list_size (types.list_tree_option t leaf) )

  lemma Case_Option :
    ∀(t : types.tree),
    ∀(lll : list (list (list (types.branch)))),
    ( lll ∈ (types.list_tree t ) ) →
    ---------------------------
    ( ∃(opt : types.node_option), lll = types.list_tree_option t opt )
  | t lll := begin
    assume or_eq,
    simp [types.list_tree] at or_eq,
    -- ∨-Elimination
    cases or_eq with eq_leaf eq_node,
    case or.inl { from exists.intro leaf eq_leaf },
    case or.inr { from exists.intro node eq_node }
  end
  lemma Length_Tree :
    ∀(t : types.tree),
    ---------------------------
    ( 2 = list.length (types.list_tree t) )
  | t := by simp [types.list_tree]
  lemma Tree_to_Option :
    ∀(t : types.tree),
    ∀{num : ℕ},
    ( 2 * num < aux.list_size (types.list_tree t) ) →
    ---------------------------
    ( ∃(opt : types.node_option), num < aux.list_size (types.list_tree_option t opt) )
  | t n := begin
    assume big_tree,
    -- Combinatory Property
    rewrite [Length_Tree t] at big_tree,
    have main_combinatory, from a_leaf.Main_Combinatory_Nested big_tree,
    cases main_combinatory with list_opt main_combinatory,
    cases main_combinatory with list_mem main_combinatory,
    -- Substitution
    have case_opt, from Case_Option t list_opt list_mem,
    cases case_opt with opt case_opt,
    rewrite [case_opt] at main_combinatory,
    -- ∃-Introduction
    from exists.intro opt main_combinatory
  end

  lemma Case_Level :
    ∀(t : types.tree)(opt : types.node_option)(loop : list (ℕ)),
    ∀(ll : list (list (types.branch))),
    ( ll ∈ types.loop_tree_option t opt loop ) →
    ---------------------------
    ( ∃(lvl : ℕ), lvl ∈ loop ∧ ll = types.list_tree_option_level t opt lvl )
  | t opt [] ll := begin
    assume ll_mem,
    simp [types.loop_tree_option] at ll_mem,
    from false.elim ll_mem
  end
  | t opt (HEAD::TAIL) ll := begin
    simp [types.loop_tree_option],
    assume or_eq_mem,
    cases or_eq_mem with eq_head list_mem,
    case or.inl {
      apply exists.intro HEAD,
      simp [eq.refl HEAD],
      from eq_head
    },
    case or.inr {
      have case_inductive, from Case_Level t opt TAIL ll list_mem,
      cases case_inductive with lvl case_inductive,
      apply exists.intro lvl,
      cases case_inductive with mem_lvl eq_lllt,
      simp [mem_lvl],
      from eq_lllt
    }
  end
  lemma Length_Tree_Option :
    ∀(t : types.tree)(opt : types.node_option),
    ---------------------------
    ( types.count_levels t = list.length (types.list_tree_option t opt) )
  | t opt := begin
    simp [types.list_tree_option, types.count_levels],
    induction (types.list_levels t),
    case list.nil { simp [types.loop_tree_option] },
    case list.cons { simp [types.loop_tree_option, ih] }
  end
  lemma Option_to_Level :
    ∀(t : types.tree)(opt : types.node_option),
    ∀{num : ℕ},
    ( (types.count_levels t) * num < aux.list_size (types.list_tree_option t opt) ) →
    ---------------------------
    ( ∃(lvl : ℕ),
      lvl ∈ types.list_levels t
    ∧ num < aux.list_size (types.list_tree_option_level t opt lvl) )
  | t opt num := begin
    assume big_option,
    -- Combinatory Property
    rewrite [Length_Tree_Option t opt] at big_option,
    have main_combinatory, from a_leaf.Main_Combinatory_Nested big_option,
    cases main_combinatory with list_lvl main_combinatory,
    cases main_combinatory with list_mem main_combinatory,
    -- Substitution
    have case_level, from Case_Level t opt (types.list_levels t) list_lvl list_mem,
    cases case_level with lvl case_level,
    cases case_level with mem_lvl case_level,
    rewrite [case_level] at main_combinatory,
    -- ∃-Introduction and ∧-Introduction
    apply exists.intro lvl,
    from and.intro mem_lvl main_combinatory
  end

  lemma Case_Formula :
    ∀(t : types.tree)(opt : types.node_option)(lvl : ℕ)(loop : list (types.formula)),
    ∀(l : list (types.branch)),
    ( l ∈ types.loop_tree_option_level t opt lvl loop ) →
    ---------------------------
    ( ∃(fml : types.formula), fml ∈ loop ∧ l = types.list_tree_option_level_formula t opt lvl fml )
  | t opt lvl [] ll := begin
    assume l_mem,
    simp [types.loop_tree_option_level] at l_mem,
    from false.elim l_mem
  end
  | t opt lvl (HEAD::TAIL) ll := begin
    simp [types.loop_tree_option_level],
    assume or_eq_mem,
    cases or_eq_mem with eq_head list_mem,
    case or.inl {
      apply exists.intro HEAD,
      simp [eq.refl HEAD],
      from eq_head
    },
    case or.inr {
      have case_inductive, from Case_Formula t opt lvl TAIL ll list_mem,
      cases case_inductive with fml case_inductive,
      apply exists.intro fml,
      cases case_inductive with mem_fml eq_llt,
      simp [mem_fml],
      from eq_llt
    }
  end
  lemma Length_Tree_Option_Level:
    ∀(t : types.tree)(opt : types.node_option)(lvl : ℕ),
    ---------------------------
    ( types.count_formulas t = list.length (types.list_tree_option_level t opt lvl) )
  | t opt lvl := begin
    simp [types.list_tree_option_level, types.count_formulas],
    induction (types.list_formulas t),
    case list.nil { simp [types.loop_tree_option_level] },
    case list.cons { simp [types.loop_tree_option_level, ih] }
  end
  lemma Level_to_Formula :
    ∀(t : types.tree)(opt : types.node_option)(lvl : ℕ),
    ∀{num : ℕ},
    ( (types.count_formulas t) * num < aux.list_size (types.list_tree_option_level t opt lvl) ) →
    ---------------------------
    ( ∃(fml : types.formula),
      fml ∈ types.list_formulas t
    ∧ num < aux.list_size (types.list_tree_option_level_formula t opt lvl fml) )
  | t opt lvl num := begin
    assume big_option_level,
    -- Combinatory Property
    rewrite [Length_Tree_Option_Level t opt lvl] at big_option_level,
    have main_combinatory, from a_leaf.Main_Combinatory_Nested big_option_level,
    cases main_combinatory with list_fml main_combinatory,
    cases main_combinatory with list_mem main_combinatory,
    -- Substitution
    have case_fml, from Case_Formula t opt lvl (types.list_formulas t) list_fml list_mem,
    cases case_fml with fml case_fml,
    cases case_fml with mem_fml case_fml,
    rewrite [case_fml] at main_combinatory,
    -- ∃-Introduction and ∧-Introduction
    apply exists.intro fml,
    from and.intro mem_fml main_combinatory
  end
  
  lemma Option_to_Leaf :
    ∀(t : types.tree)(opt : types.node_option),
    ∀{num : ℕ},
    ( is_finite t ) →
    ( (types.count_levels t) * num < aux.list_size (types.list_tree_option t opt) ) →
    ---------------------------
    ( num < aux.list_size (types.list_tree_option t leaf) )
  | t leaf num := begin
    assume finite big_option,
    have levels_pos, from aux.ZERO_LT_Length_of_LT_Size big_option,
    rewrite [←Length_Tree_Option t leaf] at levels_pos,
    have le_mul, from use.LE_Mul_Left_of_Pos levels_pos num,
    from nat.lt_of_le_of_lt le_mul big_option
  end
  | t node num := begin
    assume finite big_option,
    have big_lrnode_level, from Option_to_Level t node big_option,
    cases big_lrnode_level with lvl big_lrnode_level,
    cases big_lrnode_level with mem_lvl big_lrnode,
    from nat.lt_of_lt_of_le big_lrnode (finite lvl)
  end

  theorem Main_Theorem_Leaves :
    ∀(t : types.tree)(mul num : ℕ),
    ( is_finite t ) →
    ( mul = (2 * (types.count_levels t * (types.count_levels t * (types.count_formulas t * (types.count_formulas t * num))))) ) →
    ( mul < aux.list_size (types.list_tree t) ) →
    ---------------------------
    ( ∃(lvl : ℕ)(fml : types.formula),
      lvl ∈ types.list_levels t
    ∧ fml ∈ types.list_formulas t
    ∧ (types.count_formulas t) * num < aux.list_size (types.list_tree_option_level_formula t leaf lvl fml) )
  | t mul num := begin
    assume finite mul_constant big_tree,
    rewrite [mul_constant] at big_tree,
    -- Find a redundant type-constructor within the tree:
    have big_option, from Tree_to_Option t big_tree,
    cases big_option with opt big_option,
    -- Since the tree is finite, there must be a redundant number of leaves within the tree:
    have big_leaf, from Option_to_Leaf t opt finite big_option,
    -- Find a redundant level within the repeating leaf-constructor:
    have big_leaf_level, from Option_to_Level t leaf big_leaf,
    cases big_leaf_level with lvl big_leaf_level,
    cases big_leaf_level with mem_lvl big_leaf_level,
    apply exists.intro lvl, simp [mem_lvl],
    -- Find a redundant formula within the repeating leaf-constructor/level:
    have big_leaf_level_formula, from Level_to_Formula t leaf lvl big_leaf_level,
    cases big_leaf_level_formula with fml big_leaf_level_formula,
    cases big_leaf_level_formula with mem_fml big_leaf_level_formula,
    apply exists.intro fml, simp [mem_fml],
    from big_leaf_level_formula
  end
end p_leaf

/- Proof: Leaf Redundancy Implies Proof-Branch Redundancy -/
namespace p_branch
  /- Methods Regarding Proof-Branchs (Prop) -/
  -- Proofs and Derivations in Natural Deduction can be seen as Proof-Trees
  -- Proofs have no open formulas, while Derivations may have open formulas
  -- In a Normal Proof-Tree, every Leaf is part of a Proof-Branch
  -- A Proof-Branch can be obtained by pruning the Branch which connects its Leaf to the proof's conclusion
  -- This pruning is done top-down, from the Leaf to either the minor premise of an →ELIMINATION or the proof's conclusion
  -- Along the pruning, if a visited node in the unpruned Branch is the result of an:
  --   →ELIMINATION from its major premise: visited node = CON; visited premise = _ >> CON; the Proof-Branch continues
  --   →ELIMINATION from its minor premise: visited node = some formula; the Proof-Branch ends at the visited premise
  --   →INTRODUCTION:
  --     In a Normal Proof-Tree, an →INTRODUCTION can only be followed by an:
  --       →INTRODUCTION: visited node = _ >> CON; visited premise = CON; the Proof-Branch continues
  --       →ELIMINATION from its minor premise: visited node = some formula; the Proof-Branch ends at the visited premise
  --       The proof's conclusion: the Proof-Branch ends at the proof's conclusion
  --     But no matter where this →INTRODUCTION sequence ends, the formula where it ends determines the sequence
  -- Every Proof-Branch of a Normal Proof-Tree is either:
  --   Composed of an →ELIMINATION (from its major premise) part followed by an →INTRODUCTION part
  --   Composed of an →ELIMINATION (from its major premise) only
  --   Composed of an →INTRODUCTION only
  --   A Leaf that is the minor premise of an →ELIMINATION
  -- In an Atomicaly Expanded Normal Proof-Tree:
  --  If there is an →ELIMINATION part, it ends in a atomic formula
  --  If there is an →INTRODUCTION part, it begins in a atomic formula
  -- That is to say, in an Atomicaly Expanded Normal Proof-Tree:
  -- The Proof-Branch's Leaf determines completely the →ELIMINATION part
  -- The Proof-Branch's Ending Formula completely determines the →INTRODUCTION part
  -- Loops over the →INTRODUCTION part
  def loop_check_intro : ℕ → types.formula → types.branch → Prop
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
                                            ∧ ( types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1 )
                                            ∧ loop_check_intro LVL0 FML0 BRC
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
  | lvl1 fml1 root := ( lvl1 = 1 )
  | _ _ _ := false
  -- Loops over the →ELIMINATION part and verifies if the minimal formula is atomic
  def loop_check_elim : ℕ → types.formula → types.branch → Prop
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
                                            ∧ ( types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1 )
                                            ∧ loop_check_intro LVL0 FML0 BRC
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
                                            ∧ ( types.is_atomic fml1 )
  | lvl1 fml1 (r_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
                                            ∧ ( types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0 )
                                            ∧ loop_check_elim LVL0 FML0 BRC
  | lvl1 fml1 root := ( lvl1 = 1 )
                    ∧ ( types.is_atomic fml1 )
  | _ _ _ := false
  -- Verifies the type of branch (→ELIMINATION→INTRODUCTION; →ELIMINATION; →INTRODUCTION; Leaf)
  def check_leaf : ℕ → types.formula → types.branch → Prop
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
                                            ∧ ( types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1 )
                                            ∧ loop_check_intro LVL0 FML0 BRC
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
  | lvl1 fml1 (r_branch BRC OPT LVL0 FML0) := ( OPT = node )
                                            ∧ ( lvl1 = LVL0+1 )
                                            ∧ ( types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0 )
                                            ∧ loop_check_elim LVL0 FML0 BRC
  | _ _ _ := false
  -- To check if a regular Branch, ending at the Proof-Tree's conclusion, can be pruned into a Proof-Branch
  def check_proof_branch : types.branch → Prop
  | (leaf BRC leaf LVL0 FML0) := check_leaf LVL0 FML0 BRC
  | _ := false
  -- Using check_proof_branch as an if-clause demands a proof of decidability for each method
  instance types.branch.loop_check_intro :
    ∀(lvl1 : ℕ)(fml1 : types.formula)(b : types.branch),
    ---------------------------------
    decidable (loop_check_intro lvl1 fml1 b)
  | _ _ (leaf _ _ _ _) := begin simp [loop_check_intro], from is_false not_false end
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := begin
    simp [loop_check_intro],
    have dec_and1, from @and.decidable (types.not_atomic FML0)
                                       (types.get_consequent FML0 = fml1)
                                       (@types.formula.not_atomic FML0)
                                       (@types.formula.decidable_eq (types.get_consequent FML0) fml1),
    have dec_and2, from @and.decidable (types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1)
                                       (loop_check_intro LVL0 FML0 BRC)
                                       dec_and1
                                       (@types.branch.loop_check_intro LVL0 FML0 BRC),
    have dec_and3, from @and.decidable (lvl1 = LVL0+1)
                                       ((types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1) ∧ loop_check_intro LVL0 FML0 BRC)
                                       (@nat.decidable_eq lvl1 (LVL0+1))
                                       dec_and2,
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0+1 ∧ (types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1) ∧ loop_check_intro LVL0 FML0 BRC)
                        (@types.node_option.decidable_eq OPT node)
                        dec_and3
  end
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := begin
    simp [loop_check_intro],
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0 + 1)
                        (@types.node_option.decidable_eq OPT node)
                        (@nat.decidable_eq lvl1 (LVL0+1))
  end
  | _ _ (r_branch _ _ _ _) := begin simp [loop_check_intro], from is_false not_false end
  | lvl1 fml1 root := begin simp [loop_check_intro], from @nat.decidable_eq lvl1 1 end
  instance types.branch.loop_check_elim :
    ∀(lvl1 : ℕ)(fml1 : types.formula)(b : types.branch),
    ---------------------------------
    decidable (loop_check_elim lvl1 fml1 b)
  | _ _ (leaf _ _ _ _) := begin simp [loop_check_elim], from is_false not_false end
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := begin
    simp [loop_check_elim],
    have dec_and1, from @and.decidable (types.not_atomic FML0)
                                       (types.get_consequent FML0 = fml1)
                                       (@types.formula.not_atomic FML0)
                                       (@types.formula.decidable_eq (types.get_consequent FML0) fml1),
    have dec_and2, from @and.decidable (types.is_atomic fml1)
                                       (types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1)
                                       (@types.formula.is_atomic fml1)
                                       dec_and1,
    have dec_and3, from @and.decidable (types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1)
                                       (loop_check_intro LVL0 FML0 BRC)
                                       dec_and2
                                       (@types.branch.loop_check_intro LVL0 FML0 BRC),
    have dec_and4, from @and.decidable (lvl1 = LVL0+1)
                                       ((types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1) ∧ loop_check_intro LVL0 FML0 BRC)
                                       (@nat.decidable_eq lvl1 (LVL0+1))
                                       dec_and3,
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0+1 ∧ (types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1) ∧ loop_check_intro LVL0 FML0 BRC)
                        (@types.node_option.decidable_eq OPT node)
                        dec_and4
  end
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := begin
    simp [loop_check_elim],
    have dec_and1, from @and.decidable (lvl1 = LVL0 + 1)
                                       (types.is_atomic fml1)
                                       (@nat.decidable_eq lvl1 (LVL0+1))
                                       (@types.formula.is_atomic fml1),
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0 + 1 ∧ types.is_atomic fml1)
                        (@types.node_option.decidable_eq OPT node)
                        dec_and1
  end
  | lvl1 fml1 (r_branch BRC OPT LVL0 FML0) := begin
    simp [loop_check_elim],
    have dec_and1, from @and.decidable (types.not_atomic fml1)
                                       (types.get_consequent fml1 = FML0)
                                       (@types.formula.not_atomic fml1)
                                       (@types.formula.decidable_eq (types.get_consequent fml1) FML0),
    have dec_and2, from @and.decidable (types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0)
                                       (loop_check_elim LVL0 FML0 BRC)
                                       dec_and1
                                       (@types.branch.loop_check_elim LVL0 FML0 BRC),
    have dec_and3, from @and.decidable (lvl1 = LVL0+1)
                                       ((types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0) ∧ loop_check_elim LVL0 FML0 BRC)
                                       (@nat.decidable_eq lvl1 (LVL0+1))
                                       dec_and2,
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0+1 ∧ (types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0) ∧ loop_check_elim LVL0 FML0 BRC)
                        (@types.node_option.decidable_eq OPT node)
                        dec_and3
  end
  | lvl1 fml1 root := begin
    simp [loop_check_elim],
    from @and.decidable (lvl1 = 1)
                        (types.is_atomic fml1)
                        (@nat.decidable_eq lvl1 1)
                        (@types.formula.is_atomic fml1)
  end
  instance types.branch.check_leaf :
    ∀(lvl1 : ℕ)(fml1 : types.formula)(b : types.branch),
    ---------------------------------
    decidable (check_leaf lvl1 fml1 b)
  | _ _ (leaf _ _ _ _) := begin simp [check_leaf], from is_false not_false end
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := begin
    simp [check_leaf],
    have dec_and1, from @and.decidable (types.not_atomic FML0)
                                       (types.get_consequent FML0 = fml1)
                                       (@types.formula.not_atomic FML0)
                                       (@types.formula.decidable_eq (types.get_consequent FML0) fml1),
    have dec_and2, from @and.decidable (types.is_atomic fml1)
                                       (types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1)
                                       (@types.formula.is_atomic fml1)
                                       dec_and1,
    have dec_and3, from @and.decidable (types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1)
                                       (loop_check_intro LVL0 FML0 BRC)
                                       dec_and2
                                       (@types.branch.loop_check_intro LVL0 FML0 BRC),
    have dec_and4, from @and.decidable (lvl1 = LVL0+1)
                                       ((types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1) ∧ loop_check_intro LVL0 FML0 BRC)
                                       (@nat.decidable_eq lvl1 (LVL0+1))
                                       dec_and3,
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0+1 ∧ (types.is_atomic fml1 ∧ types.not_atomic FML0 ∧ types.get_consequent FML0 = fml1) ∧ loop_check_intro LVL0 FML0 BRC)
                        (@types.node_option.decidable_eq OPT node)
                        dec_and4
  end
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := begin
    simp [check_leaf],
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0 + 1)
                        (@types.node_option.decidable_eq OPT node)
                        (@nat.decidable_eq lvl1 (LVL0+1))
  end
  | lvl1 fml1 (r_branch BRC OPT LVL0 FML0) := begin
    simp [check_leaf],
    have dec_and1, from @and.decidable (types.not_atomic fml1)
                                       (types.get_consequent fml1 = FML0)
                                       (@types.formula.not_atomic fml1)
                                       (@types.formula.decidable_eq (types.get_consequent fml1) FML0),
    have dec_and2, from @and.decidable (types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0)
                                       (loop_check_elim LVL0 FML0 BRC)
                                       dec_and1
                                       (@types.branch.loop_check_elim LVL0 FML0 BRC),
    have dec_and3, from @and.decidable (lvl1 = LVL0+1)
                                       ((types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0) ∧ loop_check_elim LVL0 FML0 BRC)
                                       (@nat.decidable_eq lvl1 (LVL0+1))
                                       dec_and2,
    from @and.decidable (OPT = node)
                        (lvl1 = LVL0+1 ∧ (types.not_atomic fml1 ∧ types.get_consequent fml1 = FML0) ∧ loop_check_elim LVL0 FML0 BRC)
                        (@types.node_option.decidable_eq OPT node)
                        dec_and3
  end
  | _ _ root := begin simp [check_leaf], from is_false not_false end
  instance types.branch.check_proof_branch :
    ∀(b : types.branch),
    ---------------------------------
    decidable (check_proof_branch b)
  | (leaf BRC leaf LVL0 FML0) := begin simp [check_proof_branch], from @types.branch.check_leaf LVL0 FML0 BRC end
  | (leaf _ node _ _) := begin simp [check_proof_branch], from is_false not_false end
  | (u_branch _ _ _ _) := begin simp [check_proof_branch], from is_false not_false end
  | (l_branch _ _ _ _) := begin simp [check_proof_branch], from is_false not_false end
  | (r_branch _ _ _ _) := begin simp [check_proof_branch], from is_false not_false end
  | root := begin simp [check_proof_branch], from is_false not_false end

  /- Methods Regarding Proof-Branchs (Formulas) -/
  -- Finally, the pruning, per se
  def loop_prune_intro : ℕ → types.formula → types.branch → types.formula
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := if loop_check_intro lvl1 fml1 (u_branch BRC OPT LVL0 FML0)
                                              then loop_prune_intro LVL0 FML0 BRC
                                              else #0 --false
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := if loop_check_intro lvl1 fml1 (l_branch BRC OPT LVL0 FML0)
                                              then fml1
                                              else #0 --false
  | lvl1 fml1 root := if loop_check_intro lvl1 fml1 root
                      then fml1
                      else #0 --false
  | _ _ _ := #0 --false
  def loop_prune_elim : ℕ → types.formula → types.branch → types.formula
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := if loop_check_elim lvl1 fml1 (u_branch BRC OPT LVL0 FML0)
                                              then loop_prune_intro LVL0 FML0 BRC
                                              else #0 --false
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := if loop_check_elim lvl1 fml1 (l_branch BRC OPT LVL0 FML0)
                                              then fml1
                                              else #0 --false
  | lvl1 fml1 (r_branch BRC OPT LVL0 FML0) := if loop_check_elim lvl1 fml1 (r_branch BRC OPT LVL0 FML0)
                                              then loop_prune_elim LVL0 FML0 BRC
                                              else #0 --false
  | lvl1 fml1 root := if loop_check_elim lvl1 fml1 root
                      then fml1
                      else #0 --false
  | _ _ _ := #0 --false
  def prune_leaf : ℕ → types.formula → types.branch → types.formula
  | lvl1 fml1 (u_branch BRC OPT LVL0 FML0) := if check_leaf lvl1 fml1 (u_branch BRC OPT LVL0 FML0)
                                              then loop_prune_intro LVL0 FML0 BRC
                                              else #0 --false
  | lvl1 fml1 (l_branch BRC OPT LVL0 FML0) := if check_leaf lvl1 fml1 (l_branch BRC OPT LVL0 FML0)
                                              then fml1
                                              else #0 --false
  | lvl1 fml1 (r_branch BRC OPT LVL0 FML0) := if check_leaf lvl1 fml1 (r_branch BRC OPT LVL0 FML0)
                                              then loop_prune_elim LVL0 FML0 BRC
                                              else #0 --false
  | _ _ _ := #0 --false
  def prune_proof_branch : types.branch → types.formula
  | (leaf BRC leaf LVL0 FML0) := prune_leaf LVL0 FML0 BRC
  | _ := #0 --false

  def prune_branch : types.branch → (types.formula)
  | (leaf BRC leaf LVL FML) := #0
  | _ := #0 --false
  -- Defining a method to prune all the branches in a list of branches
  def prune_list_branch : list (types.branch) → list (types.formula)
  | [] := []
  | (HEAD::TAIL) := if check_proof_branch HEAD
                    then [prune_branch HEAD] ++ prune_list_branch TAIL
                    else prune_list_branch TAIL
  -- 
  def list_proof_branch_root : types.tree → types.node_option → ℕ → types.formula→ types.formula → list (types.formula)
  | t opt lvl1 fml1 fml0 := a_branch.list_filter fml0 (prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1))

  /- Restrictions Regarding Proof-Branchs -/
  -- In a Normal Proof-Tree, every Leaf is part of a Proof-Branch
  def is_normal_check : types.tree → Prop
  | t :=
    ∀(lvl1 : ℕ)(fml1 : types.formula)(b : types.branch),
    ( b ∈ (types.list_tree_option_level_formula t leaf lvl1 fml1) ) →
    ---------------------------
    ( check_proof_branch b )
  def is_normal_mem : types.tree → Prop
  | t :=
    ∀(lvl1 : ℕ)(fml1 fml0 : types.formula),
    ( fml0 ∈ prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1) ) →
    ---------------------------
    ( fml0 ∈ types.list_formulas t )

  lemma Case_Size :
    ∀{t : types.tree}{lvl1 : ℕ}{fml1 : types.formula},
    ∀{l : list (types.branch)},
    ( is_normal_check t ) →
    ( ∀(b : types.branch), b ∈ l → b ∈ types.list_tree_option_level_formula t leaf lvl1 fml1 ) →
    ---------------------------
    ( aux.list_size l = aux.list_size (prune_list_branch l) )
  | t lvl1 fml1 [] := begin
    assume normal_check subset,
    simp [prune_list_branch, aux.list_size]
  end
  | t lvl1 fml1 (HEAD::TAIL) := begin
    assume normal_check subset,
    have head_mem : HEAD ∈ types.list_tree_option_level_formula t leaf lvl1 fml1,
    from begin
      apply (subset HEAD),
      simp [has_mem.mem, list.mem]
    end,
    have tail_subset : ∀(b : types.branch), b ∈ TAIL → b ∈ types.list_tree_option_level_formula t leaf lvl1 fml1,
    from begin
      assume loop loop_mem_tail,
      apply (subset loop),
      simp [has_mem.mem, list.mem] at ⊢ loop_mem_tail,
      simp [loop_mem_tail]
    end,
    simp [prune_list_branch],
    rewrite [use.ITE_Distribution (aux.list_size)],
    simp [aux.list_size, aux.size, aux.has_size.size],
    have check_head, from normal_check lvl1 fml1 HEAD head_mem,
    simp [implies, has_mem.mem, list.mem] at check_head,
    simp [check_head],
    rewrite [Case_Size normal_check tail_subset]
  end
  lemma Normal_Size :
    ∀(t : types.tree)(lvl1 : ℕ)(fml1 : types.formula),
    ( is_normal_check t ) →
    ---------------------------
    ( aux.list_size (types.list_tree_option_level_formula t leaf lvl1 fml1)
    = aux.list_size (prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1)) )
  | t lvl1 fml1 := begin
    assume normal_check,
    from Case_Size normal_check (use.Subset_Self (types.list_tree_option_level_formula t leaf lvl1 fml1))
  end

  lemma Case_Set :
    ∀(t : types.tree)(lvl1 : ℕ)(fml1 : types.formula)(n : ℕ),
    ( is_normal_mem t ) →
    ---------------------------
    ( list.length (a_branch.list_set (prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1))) * n
    ≤ list.length (types.list_formulas t) * n )
  | t lvl1 fml1 n := begin
    assume normal_mem,
    have set_le_formulas, from a_branch.Length_Set_LE_Length_of_Subset (normal_mem lvl1 fml1),
    from use.LE_Mul_of_LE n set_le_formulas
  end

  theorem Main_Theorem_Branchs :
    ∀(t : types.tree)(lvl1 : ℕ)(fml1 : types.formula)(num : ℕ),
    ( is_normal_check t ) → ( is_normal_mem t ) →
    ( (types.count_formulas t) * num < aux.list_size (types.list_tree_option_level_formula t leaf lvl1 fml1) ) →
    ---------------------------
    ( ∃(fml0 : types.formula),
      fml0 ∈ prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1)
    ∧ num < aux.list_size (list_proof_branch_root t leaf lvl1 fml1 fml0) )
  | t lvl1 fml1 num := begin
    assume normal_check normal_mem big_leaf_level_formula,
    simp [list_proof_branch_root, aux.list_size] at ⊢ big_leaf_level_formula,
    simp [types.count_formulas, nat.mul_assoc] at big_leaf_level_formula,
    rewrite [Normal_Size t lvl1 fml1 normal_check] at big_leaf_level_formula,
    -- 
    have main_combinatory, from a_branch.Main_Combinatory_Filter
                                num
                                (prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1)),
    -- 
    have case_set, from Case_Set t lvl1 fml1 num normal_mem,
    have big_branch, from main_combinatory (nat.lt_of_le_of_lt case_set big_leaf_level_formula),
    cases big_branch with fml0 big_branch,
    cases big_branch with mem_fml0 big_branch,
    apply exists.intro fml0, simp [mem_fml0],
    from big_branch
  end
end p_branch

/- Proof: Theorem of Proof-Branch Redundancy -/
theorem Proof_Branch_Redundancy :
  ∀(t : types.tree)(mul num : ℕ),
  ( p_leaf.is_finite t ) → ( p_branch.is_normal_check t ) → ( p_branch.is_normal_mem t ) →
  ( mul = (2 * (types.count_levels t * (types.count_levels t * (types.count_formulas t * (types.count_formulas t * num))))) ) →
  ( mul < aux.list_size (types.list_tree t) ) →
  ---------------------------
  ( ∃(lvl1 : ℕ)(fml1 fml0 : types.formula),
    lvl1 ∈ types.list_levels t
  ∧ fml1 ∈ types.list_formulas t
  ∧ fml0 ∈ p_branch.prune_list_branch (types.list_tree_option_level_formula t leaf lvl1 fml1)
  ∧ num < aux.list_size (p_branch.list_proof_branch_root t leaf lvl1 fml1 fml0) )
| t mul num := begin
  assume finite normal_check normal_mem mul_constant big_tree,
  -- Find a repeating leaf-constructor/level/formula:
  have big_leaf_level_formula, from p_leaf.Main_Theorem_Leaves
                                    t mul num
                                    finite mul_constant big_tree,
  cases big_leaf_level_formula with lvl1 big_leaf_level_formula,
  cases big_leaf_level_formula with fml1 big_leaf_level_formula,
  cases big_leaf_level_formula with mem_lvl1 big_leaf_level_formula,
  cases big_leaf_level_formula with mem_fml1 big_leaf_level_formula,
  apply exists.intro lvl1, simp [mem_lvl1],
  apply exists.intro fml1, simp [mem_fml1],
  -- Find a redundant proof-branch from the repeating leaf-constructor/level/formula:
  have big_branch, from p_branch.Main_Theorem_Branchs
                        t lvl1 fml1 num
                        normal_check normal_mem big_leaf_level_formula,
  cases big_branch with fml0 big_branch,
  cases big_branch with mem_fml0 big_branch,
  apply exists.intro fml0, simp [mem_fml0],
  from big_branch
end
