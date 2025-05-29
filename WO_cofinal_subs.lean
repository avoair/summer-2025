import Mathlib.Tactic

section
variable [LinearOrder α]

-- End extension ordering on sets. A is an end extension of B iff B is an initial segment of A
def endext (A B : Set α) := A ⊆ B ∧ ∀ b ∈ (B \ A), ∀ a ∈ A, a < b

local infix:50 " ≼ " => endext

theorem endext_trans (A B C : Set α): A ≼ B → B ≼ C → A ≼ C := by
  intro hab hbc
  constructor
  · apply le_trans hab.left hbc.left
  · intro c hc a ha
    have : c ∈ (B \ A) ∨ c ∈ (C \ B) := by
      simp ; simp at hc
      rcases Classical.em (c ∈ B) with h1 | h2
      · left ; exact And.intro h1 hc.right
      · right ; exact And.intro hc.left h2
    rcases this with h1 | h2
    · apply hab.right c h1 _ ha
    · apply hbc.right _ h2
      apply hab.1 ha
end

abbrev WFs (α : Type*) [LinearOrder α] := {A : Set α // A.WellFoundedOn (· < ·)}

variable [LinearOrder α]
def endext'  (A B : WFs α) := endext A.1 B.1
local infix:50 " ≼ " => endext'

theorem endext_trans' (A B C : WFs α): A ≼ B → B ≼ C → A ≼ C := by
  apply endext_trans

def WF_convert (α : Type*) [LinearOrder α] (c : Set (WFs α)) : Set (Set α)
               := Set.image (λ x => x.1) c

lemma Mem_from_mem_Uwf {α : Type*} [LinearOrder α] {C : Set (WFs α)}
                       (x) (h: x ∈ ⋃₀ (WF_convert α C)) : ∃ c ∈ C, x ∈ c.1 := by
  rcases Set.mem_sUnion.mp h with ⟨c₀, hc₀⟩
  simp [WF_convert] at hc₀
  rcases hc₀.left with ⟨c₀wf, inC⟩
  use ⟨c₀, c₀wf⟩
  exact And.intro inC hc₀.right


lemma WF_of_WF_chain_union {α : Type*} [LinearOrder α] (C : Set (WFs α)) :
  IsChain (. ≼ .) C → (⋃₀ (WF_convert α C)).WellFoundedOn (· < ·) := by
  intro isChain_C

  rw [Set.wellFoundedOn_iff_no_descending_seq]
  intro f
  by_contra hf_image
  rcases Mem_from_mem_Uwf (f 0) (hf_image 0) with ⟨c, hc⟩
  apply Set.wellFoundedOn_iff_no_descending_seq.mp c.2 f
  intro n
  by_contra contra
  rcases Mem_from_mem_Uwf (f n) (hf_image n) with ⟨c', hc'⟩

  have :c ≠ c' := by
    intro h
    rw [<-h] at hc'
    apply contra hc'.right

  rcases isChain_C hc.left hc'.left this with h1 | h1
  · have : f 0 < f n := by
      exact h1.right (f n) (And.intro hc'.right contra) (f 0) hc.right
    exact (Nat.lt_irrefl 0) (lt_of_le_of_lt  (Nat.zero_le n) ((@f.map_rel_iff' 0 n).mp this))
  · apply Set.not_subset_iff_exists_mem_not_mem.mpr
    use (f n)
    · exact And.intro hc'.right contra
    · exact h1.left

-- Every linear order has a well ordered, cofinal subset
lemma exists_cof_WF_subset  {α : Type*} [LinearOrder α]:
  ∃ (A : Set α), IsCofinal A ∧ A.WellFoundedOn (· < ·) := by

  -- every chain of well orders (ordered by end extension) is bounded
  have zorn_prop : ∀ (C : Set (WFs α)),
                  IsChain (. ≼ .) C
                  → ∃ (ub : WFs α), ∀ a ∈ C, a ≼ ub := by
    intro C hC
    simp [IsChain] at hC

    let maxwf := (⋃₀ (WF_convert α C))
    have maxwf_wf : maxwf.WellFoundedOn (· < ·) := by
      exact WF_of_WF_chain_union C hC

    use ⟨maxwf, maxwf_wf⟩
    intro a hac
    simp [maxwf]
    constructor
    · have : ↑a ∈ WF_convert α C := by
        simp [WF_convert,hac]
        exact a.2
      apply Set.subset_sUnion_of_subset (WF_convert α C) a
      simp
      exact this
    · intro x hx y hy
      rcases Mem_from_mem_Uwf x hx.left with ⟨c, hc⟩
      rcases eq_or_ne c a with eq | neq
      · by_contra _
        rw [eq] at hc
        exact hx.right hc.right
      · specialize hC hc.left hac neq
        rcases hC with h1 | h2
        · by_contra _
          exact hx.right (h1.left hc.right)
        · exact h2.right x (And.intro hc.right hx.right) y hy

  have le_trans_overWF : ∀ {a b c : WFs α}, a ≼ b → b ≼ c → a ≼ c := by
    intro a b c hab hbc
    exact endext_trans a.1 b.1 c.1 hab hbc

  have max_elt: ∃ (m : (WFs α)), ∀ (a : (WFs α)), m ≼ a → a ≼ m := by
    exact exists_maximal_of_chains_bounded zorn_prop le_trans_overWF
  rcases max_elt with ⟨M, hM⟩
  use M
  constructor
  · by_contra not_cof
    simp [IsCofinal] at not_cof
    rcases not_cof with ⟨a, ha⟩

    let M' := insert a M.1

    have hM' : M'.WellFoundedOn fun x1 x2 => x1 < x2 := by
      exact Set.WellFoundedOn.insert M.2 a

    let (M'₀ : WFs α) := ⟨M', hM'⟩
    have M's_eq: M'₀.1 = M' := by
      sorry -- this should be straightforward, but there is a type problem
    have h :  M ≼ M'₀ := by
      constructor
      · have : M.1 ⊆ M' := by
          exact (M.1).subset_insert a
        rw[M's_eq]
        exact Set.subset_insert a (M.1)
      · intro y hy x hx
        have : a ∉ M.1 := by
          by_contra haM
          exact lt_irrefl a (ha a haM)
        have : y = a := by
          simp [M's_eq, M'] at hy
          rcases hy.left with h | h
          · exact h
          · by_contra _ ; exact hy.right h
        rw [this]
        exact ha x hx

    have : ↑M'₀ ≼ ↑M := by
      exact hM M'₀ h

    have Meq : M'₀.1 = M.1 := by
      exact Set.Subset.antisymm (this.left) (h.left)

    have aM : a ∈ M'₀.1 := by
      simp [M's_eq]
      exact Set.mem_insert a M.1
    rw [Meq] at aM
    exact lt_irrefl a (ha a aM)
  · exact M.2
