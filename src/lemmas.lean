import ring_theory.graded_algebra.basic
import ring_theory.localization.basic
import algebraic_geometry.structure_sheaf

section

variables {ΞΉ R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A] [decidable_eq ΞΉ] [add_monoid ΞΉ]

variables (π : ΞΉ β submodule R A)
variables [graded_algebra π]

lemma set_like.graded_monoid.nat_mem (n : β) : (n : A) β π 0 :=
begin
  induction n with n ih,
  exact submodule.zero_mem _,

  rw nat.succ_eq_add_one,
  have : (β(n + 1) : A) = (n : A) + 1 := rfl,
  erw this,
  apply submodule.add_mem _ ih,
  exact set_like.graded_monoid.one_mem,
end

end

section

open_locale big_operators

variables {R : Type*} [comm_ring R] (M : submonoid R)

lemma localization.mk_sum {ΞΉ : Type*} (m : M) (s : finset ΞΉ) (f : ΞΉ β R) :
  localization.mk (β i in s, f i) m = β i in s, localization.mk (f i) m :=
begin
  haveI : decidable_eq ΞΉ := classical.dec_eq _,
  induction s using finset.induction_on with i s hi ih,
  { simp },
  { rw [finset.sum_insert hi, finset.sum_insert hi, β ih, localization.add_mk],
    simp only [localization.mk_eq_mk', is_localization.eq],
    use 1,
    simp only [submonoid.coe_one, submonoid.coe_mul, mul_one],
    ring, }
end

end

section

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (π : β β submodule R A)
variables [graded_algebra π]

lemma graded_algebra.proj_hom_mul (a b : A) (i j : β) (a_mem : a β π i)
  (hb : graded_algebra.proj π j b β  0) :
  graded_algebra.proj π (i + j) (a * b) = a * graded_algebra.proj π j b :=
begin
  haveI : Ξ  (i : β) (x : π i), decidable (x β  0) := Ξ» _ _, classical.dec _,
  by_cases INEQ : a = 0,
  rw [INEQ, zero_mul, zero_mul, linear_map.map_zero],

  rw [graded_algebra.proj_apply, alg_equiv.map_mul, direct_sum.coe_mul_apply_submodule π,
    βgraded_algebra.support, βgraded_algebra.support],

  have set_eq1 : graded_algebra.support π a = {i},
    { ext1, split; intros hx,
      { erw graded_algebra.mem_support_iff at hx,
        erw finset.mem_singleton,
        contrapose hx,
        erw [not_not, graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne],
        exact a_mem,
        symmetry,
        exact hx, },
      { rw finset.mem_singleton at hx,
        rw [hx, graded_algebra.mem_support_iff, graded_algebra.proj_apply,
          graded_algebra.decompose_of_mem_same],
        exact INEQ,
        exact a_mem, }, },
    erw [set_eq1],
    have set_eq2 : finset.filter
          (Ξ» z : β Γ β, z.1 + z.2 = i + j)
          (finset.product
            {i}
            (graded_algebra.support π b)) =
      {(i, j)},
    { ext1 x, rcases x with β¨n1, n2β©,
      split; intros ha,
      { erw finset.mem_filter at ha,
        rcases ha with β¨ha1, ha3β©,
        erw finset.mem_product at ha1,
        rcases ha1 with β¨ha1, ha2β©,
        dsimp only at ha1 ha2 ha3,
        erw finset.mem_singleton at ha1,
        erw finset.mem_singleton,
        ext; dsimp only,
        { exact ha1, },
        { erw ha1 at ha3,
          linarith, }, },
      { erw [finset.mem_singleton, prod.ext_iff] at ha,
        rcases ha with β¨ha1, ha2β©,
        dsimp only at ha1 ha2,
        erw [ha1, ha2, finset.mem_filter, finset.mem_product, finset.mem_singleton],
        refine β¨β¨rfl, _β©, rflβ©,
        dsimp only,
        erw graded_algebra.mem_support_iff,
        exact hb, }, },
    erw [set_eq2, finset.sum_singleton],
    dsimp only,
    erw [graded_algebra.decompose_of_mem_same π, βgraded_algebra.proj_apply],
    exact a_mem,
end

end

namespace algebraic_geometry.structure_sheaf

open topological_space algebraic_geometry opposite

variables (R : Type*) [comm_ring R]

lemma is_locally_fraction_pred'
  {U : opens (prime_spectrum.Top R)} (f : Ξ  x : U, localizations R x) :
  (is_locally_fraction R).pred f β
  β x : U, β (V) (m : x.1 β V) (i : V βΆ U),
  β (r s : R), β y : V, β (s_not_mem : Β¬ (s β y.1.as_ideal)),
    f (i y : U) = localization.mk r β¨s, s_not_memβ© :=
begin
  rw is_locally_fraction_pred,
  split; intros H,
  { rintros x,
    obtain β¨V, m, i, r, s, Hβ© := H x,
    refine β¨V, m, i, r, s, _β©,
    intros y,
    obtain β¨s_not_mem, Hβ© := H y,
    refine β¨s_not_mem, _β©,
    rw [localization.mk_eq_mk'],
    erw is_localization.eq_mk'_iff_mul_eq,
    exact H, },
  { intros x,
    obtain β¨V, m, i, r, s, Hβ© := H x,
    refine β¨V, m, i, r, s, _β©,
    intros y,
    obtain β¨s_not_mem, Hβ© := H y,
    refine β¨s_not_mem, _β©,
    rw [localization.mk_eq_mk'] at H,
    erw is_localization.eq_mk'_iff_mul_eq at H,
    exact H },
end

lemma one_val (U : opens (prime_spectrum.Top R)) :
  (1 : sections_subring R (op U)).1 = 1 := rfl

lemma zero_val (U : opens (prime_spectrum.Top R)) :
  (0 : sections_subring R (op U)).1 = 0 := rfl

lemma add_val (U : opens (prime_spectrum.Top R)) (x y : sections_subring R (op U)) :
  (x + y : sections_subring R (op U)).1 = x.1 + y.1 := rfl

lemma mul_val (U : opens (prime_spectrum.Top R)) (x y : sections_subring R (op U)) :
  (x * y : sections_subring R (op U)).1 = x.1 * y.1 := rfl


end algebraic_geometry.structure_sheaf
