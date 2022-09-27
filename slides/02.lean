import affine_algebraic_set.V
import affine_algebraic_set.basic

variables {k : Type*} [comm_semiring k]
variable {σ : Type*} 
variables (S : set (mv_polynomial σ k))
variables (X : affine_algebraic_set k σ)

#print 𝕍
#check 𝕍 S
#check affine_algebraic_set.is_algebraic X