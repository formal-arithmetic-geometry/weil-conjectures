/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.CompositionModelOrientationDefinitions

/-! # Purity in the standing tensor-mate coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale.CompositionTensorMate

/-- Change from the inverse-shift presentation to the left-derived tensor source.
Source: composition proof Step 2, twist reassociation and exact pullback comparison
(blueprint: lem-pur-composition-single-mate-presentation). -/
def compositionMateSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.compositionShiftedPullback f d).obj K ≅
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
        ((S P.Coefficient f).obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) ⊗
            P.diagonalTwist X d) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)) ≪≫
    compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).symm.app
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))
      (Iso.refl (P.diagonalTwist X d)))

variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

/-- A single smooth purity map is orientation insertion followed by the standing
projection/counit tensor mate, in the specified coefficient-unit coordinates.
Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 2 and
Step 1's identification of the co-projection constituents
(blueprint: lem-pur-composition-single-mate-presentation).

Proof: choose a bounded etale representative of K using constructible origin. The
characterization of smoothPurityTensorMap computes gamma in that representative.
Transpose its theta through the standing Hom bijection: comparison naturality,
the projection comparison and the adjunction triangles give exactly the defining
inverse-projection/counit transpose of CompositionTensorMate.theta. The unit change
is modelOrientationUnit, so tensoring the inverse diagonal orientation becomes
tensoring modelOrientation inverse. Insert the exact/left-derived pullback comparison
and the specified shift reassociation, which together are compositionMateSource.
Faithfulness of comparison identifies the two transposes. Realizing the equality
through the intrinsic coefficient equivalence proves the displayed formula. This
uses no composition assertion and applies equally in relative dimension zero. -/
theorem composition_single_mate_presentation (f : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    letI := P.noetherian (Y ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P f (Y ↘ Spec (.of P.field.k))
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of P.field.k))
    let M := (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K
    P.smoothPurityMap f d K hK =
      (P.compositionMateSource f d K).hom ≫
        (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((S P.Coefficient f).obj M ◁
            (P.modelOrientation d f (Y ↘ Spec (.of P.field.k))).inv ≫
              theta P.Coefficient f M) := by sorry

end WeilConjectures.PurityFiniteSetting
