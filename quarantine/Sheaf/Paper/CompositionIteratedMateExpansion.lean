/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.CompositionSingleMatePresentation

/-! # Purity in the standing tensor-mate coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale.CompositionTensorMate

variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

/-- Expanding the iterated purity maps gives the right tensor-mate route with
separate inverse orientations. This does not identify them with the composite
orientation, and does not use the tensor-mate composition equation.
Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 2;
the expanded K-form in assembly Step 3 of the DAG
(blueprint: lem-pur-composition-iterated-mate-expansion).

Proof: use the single-map presentation for g and for f at g!K. Expand the eight
normalized factors of compositionSourceIdentification. Naturality of tensor-shift
reassociation cancels the opposite inner and outer reassociations. Naturality of
left-derived pullback composition and its tensor comparison leaves exactly r_K.
The twist-power factors give mu inverse, and the two orientation insertions give
the inverse of their tensor V. Move the pulled-back orientation past tensor and
pullback comparisons using their naturality. Naturality of theta_f moves theta_g
past that orientation insertion, leaving r_K followed by pulled-back theta_g and
then theta_f, which is rhs. The intermediate realization unit moves to the target
by the same naturality and becomes f! of that unit. No orientation comparison for
gf, DNC descent or composition identity for theta is used in this expansion. The
unit cases reduce to the unit constraints; even shifts carry their actual signs. -/
theorem composition_iterated_mate_expansion (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
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
    let V := P.compatibleTensorIso (P.modelOrientation d f (Y ↘ Spec (.of P.field.k)))
      ((S P.Coefficient f).mapIso (P.modelOrientation e g (Z ↘ Spec (.of P.field.k))))
    (P.compositionSourceIdentification f g d e K).hom ≫
        (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
        P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
          (P.compositionExceptional_ctf g e K hK) =
      (P.compositionMateSource (f ≫ g) (d + e) K).hom ≫
        (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((S P.Coefficient (f ≫ g)).obj M ◁
            ((P.modelOrientationMu d e f (Y ↘ Spec (.of P.field.k))).inv ≫ V.inv) ≫
              rhs P.Coefficient f g M ≫
                (G P.Coefficient f).map
                  ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app
                    ((G P.Coefficient g).obj M))) := by sorry

end WeilConjectures.PurityFiniteSetting
