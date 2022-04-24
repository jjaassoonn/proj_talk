import ring_theory.graded_algebra.basic
import ring_theory.localization.at_prime

variables {ι R A: Type*}
variables [add_comm_monoid ι] [decidable_eq ι]
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variables (𝔭 : ideal A) [ideal.is_prime 𝔭]

def homogeneous_localization : subring (localization.at_prime 𝔭) :=
{ carrier := {x | ∃ (n : ι) (a b : 𝒜 n) (b_not_mem : b.1 ∉ 𝔭), x = localization.mk a.1 ⟨b.1, b_not_mem⟩},
  mul_mem' := _,
  one_mem' := _,
  add_mem' := _,
  zero_mem' := _,
  neg_mem' := _ }