module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-!
# Faithful flatness and rational points of affine group schemes

Source: Milne, Algebraic Groups (2017), Proposition 5.47, printed p.110;
affine image factorization, Theorem 3.34, printed p.75.
(blueprint: lem-sfb-affine-group-homomorphism-image)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over an algebraically closed field, a homomorphism of affine finite type group schemes
with smooth target is faithfully flat exactly when it is surjective on rational points.

Source: Milne, Algebraic Groups (2017), Proposition 5.47, printed p.110.
(blueprint: lem-sfb-affine-group-homomorphism-image)

Proof plan: write A = F[H₂], B = F[H₁]. If A → B is faithfully flat, spectrum
surjectivity (lem-weil-pbc-faithfully-flat-surjective-spectrum) gives a prime above the
maximal ideal of any F-point. A maximal ideal containing it still contracts to that ideal.
The Nullstellensatz (lem-wf-affine-nullstellensatz-vanishing, clause 1) makes its residue
field F, producing a lift of the given point.

Conversely, lem-sfb-affine-homomorphism-flat-image factors f through a faithfully flat
map to its image and a closed immersion into H₂. Write this closed image as Spec(A/J)
using def-weil-closed-immersion. Surjectivity on F-points says every element of J vanishes
at every F-point of H₂. Smoothness makes H₂ geometrically reduced
(sbc-lem-smooth-geometrically-reduced), hence its coordinate ring is reduced
(def-pc-reduced-scheme). The Nullstellensatz, clause 2, gives J = 0. Thus the closed
immersion is an isomorphism and f is faithfully flat. -/
theorem affineGroupHom_faithfullyFlat_iff_surjective_points
    (F : Type u) [Field F] [IsAlgClosed F]
    (H₁ H₂ : Over (Spec (.of F))) [GrpObj H₁] [GrpObj H₂]
    [IsAffine H₁.left] [IsAffine H₂.left]
    [LocallyOfFiniteType H₁.hom] [QuasiCompact H₁.hom]
    [LocallyOfFiniteType H₂.hom] [QuasiCompact H₂.hom] [Smooth H₂.hom]
    (f : H₁ ⟶ H₂) [IsMonHom f] :
    f.left.appTop.hom.FaithfullyFlat ↔
      Function.Surjective (fun x : Over.mk (𝟙 (Spec (.of F))) ⟶ H₁ ↦ x ≫ f) := by
  sorry

end AlgebraicGeometry
