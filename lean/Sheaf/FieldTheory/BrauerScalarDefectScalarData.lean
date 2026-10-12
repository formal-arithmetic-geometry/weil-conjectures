module
public import Sheaf.FieldTheory.BrauerScalarDefect
import Sheaf.FieldTheory.GaloisUnitsCohomology

@[expose] public section
universe u
namespace Field
open scoped TensorProduct

/-- Scalar extraction from locally constant matrix descent lifts.
Proof: put X_a = e(1 ⊗ a). Apply g to the descent equation for h and substitute
that for g. Then P = b_g g(b_h) and b_(gh) induce the same conjugation on X_a,
so D = P b_(gh)⁻¹ commutes with X_a. The tensors 1 ⊗ a span after scalar
extension, and e is surjective, so D commutes with every matrix. Commutation
with the diagonal matrix units kills off-diagonal entries; commutation with
the remaining units makes all diagonal entries equal. Since n > 0 and D is
invertible, its common diagonal entry is a unique unit c(g,h).
Near (g,h), local constancy of b and continuity of multiplication fix b_g,
b_h and b_(gh). Each entry of the fixed b_h is algebraic over K, and its
stabilizer is Krull-open. Intersecting these finitely many stabilizers fixes
g(b_h), hence D and its diagonal unit. Thus c is jointly locally constant.
Expand b_g g(b_h) gh(b_k) in both associative orders, substitute the scalar
relations, and cancel b_(ghk). Injectivity of scalar matrices for n > 0 gives
the displayed cocycle identity. No normalization at the identity is required.
Source: Stacks Project, Tag 03R6 and the two-cocycle construction before Tag 03R7.
(blueprint: lem-sc-brauer-scalar-defect-scalar-data). -/
theorem exists_brauerScalarDefect_scalar_data (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) :
    ∃ c : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        (SeparableClosure K ≃ₐ[K] SeparableClosure K) → (SeparableClosure K)ˣ,
      IsLocallyConstant (Function.uncurry c) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (c g h) * b (g * h)) ∧
      (∀ g h k, c g h * c (g * h) k =
        g (c h k) * c g (h * k)) := by sorry
end Field
