
import LLMlean


section StrongInduction

def is_prime (n: Nat): Prop := 2 ≤ n ∧ ∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n)

-- some truth in classical logic - `simp`
-- The simplifier is what is known as a conditional term rewriting system: all it does is repeatedly replace (or rewrite) subterms of the form A by B, for all applicable facts of the form A = B or A ↔ B. The simplifier mindlessly rewrites until it can rewrite no more
def cl_1 {α : Sort u} {p: α → Prop}: ¬ (∀ (a: α), p a) → (∃ (a: α), ¬ p a) := by simp
def cl_2 {p q: Prop}: ¬ (p → ¬ q) → p ∧ q := by simp
def cl_3 {p q: Prop}: ¬ (p ∧ q) → p → ¬ q := by simp

-- divide is reflexive and transitive `def Nat.dvd (m n : Nat) : Prop := ∃ k, n = m * k`
def divide_rfl: ∀ (n: Nat), n ∣ n := by
  intro n
  let h : n = n * 1 := Eq.symm (Nat.mul_one n)
  exact Exists.intro 1 h
def divide_trans: ∀ (m n l: Nat), m ∣ n → n ∣ l → m ∣ l := by
  intro (m: Nat) (n: Nat) (l: Nat) (hmn: m ∣ n) (hnl: n ∣ l)
  cases hmn with | intro k₁ hk₁ => -- `k₁: Nat`, `hk₁: n = m * k₁`
      cases hnl with | intro k₂ hk₂ => -- `k₂: Nat`, `hk₂: l = n * k₂`
          let k := k₁ * k₂
          let h : l = m * k := by
            calc
              l = n * k₂ := by rw [hk₂]
              _ = m * k₁ * k₂ := by rw[hk₁]
              _ = m * (k₁ * k₂) := by rw[Nat.mul_assoc]
              _ = m * k := by rfl

          exact Exists.intro k h

theorem prime_factor: ∀ (n: Nat), 2 ≤ n → ∃ (m: Nat), is_prime m ∧ m ∣ n := by
  intro (n: Nat) -- wts `2 ≤ n → ∃ m, is_prime m ∧ m ∣ n`
  -- strong induction
  induction n using Nat.strongRecOn with | ind n ih =>
    -- `ih : ∀ (m : ℕ), m < n → 2 ≤ m → ∃ l, is_prime l ∧ l ∣ m`
    -- wts `2 ≤ n → ∃ m, is_prime m ∧ m ∣ n` given `ih`
    intro (h₁: 2 ≤ n)
    if h₂ : is_prime n then
      exact Exists.intro n (And.intro h₂ (divide_rfl n))
    else -- `h₂: ¬ is_prime n`
      let h₃ : ∃ (m: Nat), ¬(m ∣ n → ¬ (2 ≤ m ∧ m < n)) := cl_1 (cl_3 h₂ h₁)
      let ⟨(m: Nat), (hm : ¬(m ∣ n → ¬(2 ≤ m ∧ m < n)))⟩ := h₃
      let h₄ : m ∣ n ∧ 2 ≤ m ∧ m < n := cl_2 hm
      let m_divides_n : m ∣ n := h₄.left
      let m_ge_2 : 2 ≤ m := h₄.right.left
      let m_lt_n : m < n := h₄.right.right
      if h₅ : is_prime m then
        exact Exists.intro m (And.intro h₅ m_divides_n)
      else -- `h₅ : ¬ is_prime m`
        let h₆ : ∃ l, is_prime l ∧ l ∣ m := ih m m_lt_n m_ge_2
        let ⟨(l: Nat), (hl: is_prime l ∧ l ∣ m)⟩ := h₆
        let l_is_prime: is_prime l := hl.left
        let l_divides_m: l ∣ m := hl.right
        let l_divides_n := divide_trans l m n l_divides_m m_divides_n
        exact Exists.intro l (And.intro l_is_prime l_divides_n)


#print prime_factor


-- with mainly tactics
namespace v2

-- import LLMlean
-- llmstep for one step
-- llmqed for all steps


def div (a b : Nat) := ∃ (k: Nat), a = k * b

def is_prime (a: Nat): Prop := ¬ (∃ (k: Nat), 2 ≤ k ∧ k < a ∧ div k a)

def div_rfl: ∀ (a: Nat), div a a := by
  intro a
  exists 1
  rw [Nat.one_mul]

def div_trans: ∀ (a b c: Nat), div a b → div b c → div a c := by
  intro a b c
  intro a_div_b b_div_c
  rcases a_div_b with ⟨x, a_eq_xb⟩
  rcases b_div_c with ⟨y, b_eq_yc⟩
  simp [div]
  exists x * y
  rw [Nat.mul_assoc, a_eq_xb, b_eq_yc]

def prime_factor: ∀ (a: Nat), 2 ≤ a → ∃ (k: Nat), is_prime k ∧ div k a := by
  intros a
  induction a using Nat.strongRecOn with
    | ind a ha_ind =>
      intro _2_le_a
      by_cases h: is_prime a
      case pos =>
        exists a
        constructor
        case left => exact h
        case right => exact (div_rfl a)
      case neg =>
        simp [is_prime] at h
        rcases h with ⟨k, ⟨_2_le_k, k_lt_a, k_div_a⟩⟩
        have hl: ∃ (l: Nat), is_prime l ∧ div l k := ha_ind k k_lt_a _2_le_k
        rcases hl with ⟨l, ⟨l_is_prime, l_div_k⟩⟩
        exists l
        constructor
        case left => exact l_is_prime
        case right => exact (div_trans l k a l_div_k k_div_a)

#print prime_factor

end v2

-- with Ax-Prover
namespace v3

-- import LLMlean
-- llmstep for one step
-- llmqed for all steps


def div (a b : Nat) := ∃ (k: Nat), a = k * b

def is_prime (a: Nat): Prop := ¬ (∃ (k: Nat), 2 ≤ k ∧ k < a ∧ div k a)

def div_rfl: ∀ (a: Nat), div a a := by
  intro a
  exists 1
  rw [Nat.one_mul]

def div_trans: ∀ (a b c: Nat), div a b → div b c → div a c := by
  intro a b c
  intro a_div_b b_div_c
  rcases a_div_b with ⟨x, a_eq_xb⟩
  rcases b_div_c with ⟨y, b_eq_yc⟩
  simp [div]
  exists x * y
  rw [Nat.mul_assoc, a_eq_xb, b_eq_yc]

def prime_factor: ∀ (a: Nat), 2 ≤ a → ∃ (k: Nat), is_prime k ∧ div k a := by
  sorry

#print prime_factor

end v3

end StrongInduction
