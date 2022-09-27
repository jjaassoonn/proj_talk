import affine_algebraic_set.I
import affine_algebraic_set.basic

open affine_algebraic_set

variables {k : Type*} [comm_ring k]
variable {σ : Type*} 
variables (S : set (σ → k))

#print 𝕀
#check 𝕀 S
#print 𝕀'