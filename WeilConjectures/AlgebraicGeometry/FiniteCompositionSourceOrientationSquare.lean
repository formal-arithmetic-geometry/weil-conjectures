/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionSingleMatePresentation

/-! # The normalized finite purity source square

Source: latest blueprint, smooth-purity composition proof, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Geometry
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

/-- The source comparison transports arbitrary maps out of the second oriented tensor
source. This square contains no tensor mate for f, no composition identity for tensor
mates, and no purity map. In particular its endpoint is still a tensor source.
Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 2, canonical
pullback, twist, tensor and shift identifications
(blueprint: lem-pur-finite-composition-source-orientation-square).

Proof: expand the eight factors that uniquely normalize compositionSourceFixed.
Naturality of the tensor-shift comparison cancels the two opposite reassociations.
Naturality of the realization unit moves that unit to L. Insert the exact-to-derived
pullback comparisons and use their naturality and compatibility with composition.
The inverse monoidal pullback comparison and inverse associator leave r_K. The twist
power splitting is the inverse of mu followed by the signed block symmetry. Naturality
of that symmetry moves the two inverse orientations through it, producing V inverse.
Naturality of the pullback tensorator moves b to the last tensor factor. These operations
leave exactly the displayed realization unit and the specified r_K, including the
zero-rank unit constraints. No assertion about a counit or tensor mate is used. -/
theorem finiteCompositionSourceOrientationSquare
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    :
    letI := P.noetherian (Z ↘ Spec (.of P.field.k))
    letI := P.noetherian (Y ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P f (Y ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P g (Z ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P (f ≫ g) (Z ↘ Spec (.of P.field.k))
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of P.field.k))
    letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
      (Z ↘ Spec (.of P.field.k))
    let M := (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K
    let F := ProEtale.CompositionTensorMate.S P.Coefficient f
    let E := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor
    let J := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
    let O := P.modelOrientation e g (Z ↘ Spec (.of P.field.k))
    let V := P.compatibleTensorIso
      (P.modelOrientation d f (Y ↘ Spec (.of P.field.k))) (F.mapIso O)
    ∀ (L : ProEtale.CompositionTensorMate.D P.Coefficient Y)
      (b : (ProEtale.CompositionTensorMate.S P.Coefficient g).obj M ⊗
        ProEtale.CompositionTensorMate.omega P.Coefficient g ⟶ L),
    (P.compositionSourceIdentification f g d e K).hom ≫
        (P.compositionShiftedPullback f d).map
          ((P.compositionMateSource g e K).hom ≫
            J.functor.map
              ((ProEtale.CompositionTensorMate.S P.Coefficient g).obj M ◁ O.inv ≫ b)) ≫
        (P.compositionMateSource f d (J.functor.obj L)).hom ≫
        E.map (F.obj (J.inverse.obj (J.functor.obj L)) ◁
          (P.modelOrientation d f (Y ↘ Spec (.of P.field.k))).inv) =
      (P.compositionMateSource (f ≫ g) (d + e) K).hom ≫
        E.map ((ProEtale.CompositionTensorMate.S P.Coefficient (f ≫ g)).obj M ◁
          ((P.modelOrientationMu d e f (Y ↘ Spec (.of P.field.k))).inv ≫ V.inv) ≫
            ProEtale.CompositionTensorMate.r P.Coefficient f g M ≫
            F.map b ▷ ProEtale.CompositionTensorMate.omega P.Coefficient f ≫
            F.map (J.unitIso.hom.app L) ▷
              ProEtale.CompositionTensorMate.omega P.Coefficient f) := by
  sorry

end Geometry
end WeilConjectures.PurityFiniteSetting
