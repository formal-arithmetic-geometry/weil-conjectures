/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionFormal

/-! # Shift compatibility of normalized qcqs compactification comparison data

Source: Stacks Tags 0F7J and 05SU; latest blueprint lem-zl-shriek-composition.proof
(blueprint: new-z6-qcqs-composition-core-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]
/-- The normalized qcqs compactification data carry the canonical shift and triangle maps.
Source: Stacks Tag 0F7J (lemma-shriek-composition) and Tag 05SU (derived shift);
latest blueprint lem-zl-shriek-composition.proof
(blueprint: new-z6-qcqs-composition-core-shift).

Proof: every field of A is pinned. Each `comparison` is the refinement transformation on a
refinement and is fixed elsewhere by the cocycle and a common refinement (cofiltered
compactifications). On a compatible tower `tower_normalized` fixes `alpha` as the
canonical word through the normalized interchange, which is unique by
condensed-proper-open-interchange. `independent` fixes it on every other triple.
`Exchange.normalized` fixes every exchange as `exchangeComponent`. So each map in
ShiftCompatibility is a composite of canonical proper direct-image and open
extension-by-zero compositors, proper/open interchanges, exact-to-total pullback
identifications and refinement comparisons. By the qcqs shift calculus each factor commutes
with the canonical shifts, and so does their composite. A natural transformation of
triangulated functors that commutes with shifts gives a morphism of image triangles, and the
inverse of a shift-compatible isomorphism is shift-compatible. -/
theorem qcqsCompositionCoreShift
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated]
    (A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) :
    ShiftCompatibility ℓ A := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
