import data.set.lattice
import ring_theory.ideal.basic

open set

theorem compl_lt_compl {α : Type*} (U V : set α) : Uᶜ < Vᶜ → V < U :=
λ H, ⟨compl_subset_compl.1 H.1, λ H1, H.2 (compl_subset_compl.2 H1)⟩

theorem ideal.lt_def {α : Type*} [semiring α] (I J : ideal α)  :
  I < J ↔ (I : set α) < J :=
iff.rfl