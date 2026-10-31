/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPunctualWeights
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Stalk Frobenius comparison for canonical immersion inverse image

Source: blueprint restriction argument for open--closed reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]
  (W₀ X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The normalized inverse-image stalk comparison intertwines local geometric
Frobenius after passage to finite Weil presentations. The coefficient and scheme
universes are independent.

Source: the restriction paragraph of lem-zl-morphism-open-closed-reduction,
lem-zl-immersion-weil-local-behavior(1), and its finite-model descent convention.
(blueprint: lem-zl-canonical-immersion-stalk-conjugacy).

Proof: descend the input sheaf and its invertible Weil structure to one finite
coefficient field. Pull it back using the two integral composition comparisons
that define zlFrobeniusSquare. On compatible geometric lifts the inverse
pullback-composition iso identifies the stalks. Immersions induce isomorphisms on
residue fields, hence the two local return exponents agree. Induction on that
exponent, using integral pullback associativity and point-transport naturality,
shows that this stalk iso intertwines all three factors in local Frobenius.
Extend scalars to Qbar and take degree-zero cohomology. The arbitrary output
presentation in the statement is isomorphic to the pulled-back finite model:
descend that isomorphism and its inverse to a common finite coefficient extension.
The local-model conjugacy theorem transports the comparison to that presentation.
Compose the resulting conjugacies. This constructs the displayed isomorphism and
its operator equation; it asserts no weight bound or eigenvalue implication. -/
theorem zlCanonicalImmersionStalkConjugacy (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left]
    (z : {z : W₀.left // z ∈ closedPoints W₀.left})
    (hx : h₀.left z.val ∈ closedPoints X₀.left)
    (F : sfCommonStageWeilSheaf D l hl X₀ Qbar)
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K : sfWeilComplex D l hl W₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L))
    (hK : Nonempty (((zlWeilPull D l hl Qbar h₀).obj F).obj ≅
      sfWeilStageObject D l hl W₀ Qbar L K))
    (ι : W₀.left.residueField z.val →+* D.k)
    (hι : ι.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k) :
    ∃ (L' : Padic.FiniteCoefficientFields l Qbar)
      (K' : sfWeilComplex D l hl X₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L')),
      Nonempty (F.obj ≅ sfWeilStageObject D l hl X₀ Qbar L' K') ∧
      ∃ (ι' : X₀.left.residueField (h₀.left z.val) →+* D.k)
        (hι' : ι'.comp (X₀.hom.residueFieldAlgebraMap (h₀.left z.val)) =
          algebraMap D.k₀ D.k),
      ∃ e :
        (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L)).obj
          ((DerivedCategory.coefficientFdCohomology
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) 0).obj
            (localPointComplex l _ D hl W₀ K (localClosedPoint D W₀ z ι hι))) ≅
        (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L')).obj
          ((DerivedCategory.coefficientFdCohomology
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L') 0).obj
            (localPointComplex l _ D hl X₀ K'
              (localClosedPoint D X₀ ⟨h₀.left z.val, hx⟩ ι' hι'))),
        e.hom ≫ (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L')).map
            (localClosedFrobeniusCohomology l _ D hl X₀ K'
              ⟨h₀.left z.val, hx⟩ ι' hι' 0) =
          (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L)).map
            (localClosedFrobeniusCohomology l _ D hl W₀ K z ι hι 0) ≫ e.hom := by
  sorry

end WeilConjectures
