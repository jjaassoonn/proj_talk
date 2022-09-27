import affine_algebraic_set.V
import topology.category.Top.opens
import affine_algebraic_set.V_and_I
import for_mathlib.calle_set
import algebra.module.submodule_lattice

namespace affine_algebraic_set

variables {k : Type*} [comm_ring k] [is_domain k] {σ : Type*}

local notation `𝔸ⁿ` := σ → k

open set
open topological_space

instance Zariski_topology  :
  topological_space 𝔸ⁿ := 
{ -- First we need to define what an open is, in lean we need to give a function
  -- from set (n → k) → Prop i.e. a function which takes a set in k^n and
  -- determines if this is open or not.
  is_open := λ U, ∃ (S : set (mv_polynomial σ k)), U = (𝕍 (S))ᶜ,
  -- Secondly we show that univ, the whole set, is open.
  is_open_univ :=
  begin
    -- we know that the whole set will be the required set, so we "use univ"
    use (set.univ : set (mv_polynomial σ k)),
    -- Use fact that V(univ) = ∅
    rw 𝕍_univ,
    simp only [set.compl_empty],
  end,
  -- Now we show that being open is preserved by intersections.
  is_open_inter :=
  begin
    -- Let U, V be opens and let U_set be the fact that there is some S such
    -- that U = - 𝕍 (S). Similarly for V_set.
    intros U V U_set V_set,
    -- unpack U_set and V_set to access the underlying sets S and T
    cases U_set with S U_comp,
    cases V_set with T V_comp,
    -- Now we wish to show that S*T satisfies the goal
    use S*T,
    -- Use multiplicative property of 𝕍
    rw [𝕍_mul],
    -- TODO: explain convert
    convert (set.compl_union _ _).symm,
  end,
  -- Finally we wish to show that opens is preserved by arbitary unions
  is_open_sUnion :=
  begin
  -- Let opens be the set of opens that we wish to union over
  intros opens open_comp,
  -- Define H to be the set of sets of polynomials S s.t. - 𝕍 (S) is in opens.
  let H := {S : set (mv_polynomial σ k) | (𝕍 (S))ᶜ ∈ opens},
  -- We now want to show that union over H satisfies the goal
  use ⋃₀ H,
  -- converting from sUnion to Union so that we can use the lemma 𝕍_union
  rw @set.sUnion_eq_Union (mv_polynomial σ k) H,
  rw 𝕍_Union,
  simp only [set.Inter_coe_set, set.mem_set_of_eq, subtype.coe_mk, set.compl_Inter],
  
  rw set.sUnion_eq_Union,
  -- We prove the two sides are equal by showing the double inclusion
  apply set.eq_of_subset_of_subset,
    {
      intros s hs, rw set.mem_Union at hs,
      rcases hs with ⟨⟨o, ho⟩, hs⟩,
      rcases open_comp o ho with ⟨o', ho'⟩,
      refine ⟨o, ⟨o', _⟩, hs⟩,
      dsimp,
      rw ←ho',
      haveI : nonempty (o ∈ opens) := ⟨ho⟩,
      rw set.Union_const,
    },
  intros S hS,
  rw [set.mem_Union] at hS,
  rcases hS with ⟨i, hi⟩,
  rw [set.mem_Union] at hi,
  rcases hi with ⟨hi1, hi2⟩,
  simp only [set.Union_coe_set, set.mem_Union],
  refine ⟨(𝕍 i)ᶜ, hi1, hi2⟩,
  end
}

open_locale classical

lemma is_closed_iff (C : set 𝔸ⁿ) :
  is_closed C ↔ ∃ (S : set (mv_polynomial σ k)), C = 𝕍 S :=
begin
  rw ←is_open_compl_iff,
  dunfold is_open,
  -- unfold is_closed,
  show (∃ (S : set (mv_polynomial σ k)), (compl C) = compl (𝕍 S)) ↔ _,
  rw exists_congr,
  intro S,
  split,
    intro h, ext x, apply not_iff_not.1, rw [←set.mem_compl_iff, ←set.mem_compl_iff],
    congr', rintro rfl, refl, 
end

theorem zariski_wf {k : Type*} {n : Type*} [fintype n] [comm_ring k] [is_domain k] [is_noetherian k k] :
  well_founded ((>) : (opens (n → k) → (opens (n → k)) → Prop)) :=
begin
  have subrel : ∀ (V U: opens (n → k)), U < V → 𝕀' (↑U)ᶜ < 𝕀' (↑V)ᶜ,
    {
      intros U V lt,
      have exists_U_eq_𝕍_S := (is_closed_iff (↑U)ᶜ).1 (is_closed_compl_iff.2 U.2),
      cases exists_U_eq_𝕍_S with S U_eq_𝕍_S,
      have exists_V_eq_𝕍_T := (is_closed_iff (↑V)ᶜ).1 (is_closed_compl_iff.2 V.2),
      cases exists_V_eq_𝕍_T with T V_eq_𝕍_T,
      rw [U_eq_𝕍_S, V_eq_𝕍_T],
      have lt' : (↑U : set (n → k))ᶜ < (↑V)ᶜ,
      { simp only [set.lt_eq_ssubset],
        rw set.ssubset_iff_subset_ne,
        rw set.compl_subset_compl,
        split, simp only [opens.subset_coe, ←set.le_eq_subset], apply le_of_lt lt,
        have := ne_of_lt lt, contrapose! this, replace this := congr_arg has_compl.compl this, rw [compl_compl, compl_compl] at this,
        exact (subtype.coe_injective this).symm, },
      have : 𝕍 S < 𝕍 T,
      { rw [←U_eq_𝕍_S, ←V_eq_𝕍_T],
        apply compl_lt_compl,
        rw compl_compl, rw compl_compl, convert lt, },
      have h1 := 𝕀_strantimono_on_𝕍 this,
      rw ideal.lt_def, exact h1,
    },
  apply subrelation.wf subrel _,
  refine @inv_image.wf _ _ (>) (λ U : opens (n → k), 𝕀' ((↑U : set (n → k))ᶜ)) _,
  apply is_noetherian_iff_well_founded.1,
  sorry
  -- refine @is_noetherian_ring_mv_polynomial_of_fintype _ _ _ _ _inst_4,
end

end affine_algebraic_set