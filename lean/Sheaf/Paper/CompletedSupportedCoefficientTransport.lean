/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.DiagonalCompletedPushSquare
public import Sheaf.Paper.CanonicalDiagonalRightDerived

/-! # Transporting only the supported coefficient source

Source: diagonal tower coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The supported coefficient isomorphism is an actual ordinary direct-image
comparison at the diagonal, followed by the regular-unit comparison.
Source: coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport). -/
def completedSupportedCoefficientIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sΔ : CompletedOrdinarySquare l (diagonalImmersion Y) eP eW) :
    eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y :=
  sΔ.ordinary.app (SheafOfModules.unit
    (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≪≫
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (diagonalImmersion Y)).mapIso eP.unitIso

/-- Categorical cancellation for an ordinary square; the heterogeneous form
keeps the source-object equality explicit.
Source: categorical cancellation in the supported-source normalization.
(blueprint: lem-diagonal-completed-supported-transport). -/
private theorem normalized_underlying_square
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B T : C} {S : D}
    (u : A ≅ B) (v : S ≅ H.obj B)
    (o : S ⟶ H.obj A) (w : A ⟶ T)
    (h : o ≫ H.map u.hom = v.hom) :
    v.inv ≫ o ≫ H.map w = H.map (u.inv ≫ w) := by
  have ho : v.inv ≫ o = H.map u.inv := by
    apply (cancel_mono (H.map u.hom)).mp
    rw [Category.assoc, h, v.inv_hom_id, ← H.map_comp,
      u.inv_hom_id, H.map_id]
  rw [H.map_comp, ← Category.assoc, ho]

private theorem normalized_underlying_square_heq
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B T : C} {S V : D}
    (u : A ≅ B) (v : S ≅ V)
    (o : S ⟶ H.obj A) (w : A ⟶ T)
    (e : V = H.obj B) (h : HEq (o ≫ H.map u.hom) v.hom) :
    HEq (v.inv ≫ o ≫ H.map w) (H.map (u.inv ≫ w)) := by
  subst V
  exact heq_of_eq (normalized_underlying_square H u v o w (eq_of_heq h))

private theorem completed_source_underlying (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (diagonalCompletedRestriction l (diagonalSurface Y) ⋙
        diagonalForget l (diagonalSurface Y)).obj (diagonalCompletedSource l Y) =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj
        ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
          diagonalForget l (ProjectiveLine Y)).obj (SheafOfModules.unit
            (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))) := rfl

/-- The explicit supported coefficient isomorphism has the prescribed
underlying-sheaf normalization.

Source: coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport).

Proof: the ordinary diagonal square intertwines the two underlying-sheaf
comparisons. Cancel the image of the regular-module underlying isomorphism,
then compose with the direct image of the regular-unit comparison. -/
theorem completedSupportedCoefficientIso_normalization (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sΔ : CompletedOrdinarySquare l (diagonalImmersion Y) eP eW) :
    HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫
        (completedSupportedCoefficientIso l Y eP eW sΔ).hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)) := by
  let M := SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
    (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
  let H := lowerStar Ab.{u + 1} (diagonalImmersion Y)
  change HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫
    (sΔ.ordinary.hom.app M).hom ≫ H.map eP.unitIso.hom.hom)
      (H.map (eP.underlying.inv.app M ≫ eP.unitIso.hom.hom))
  exact normalized_underlying_square_heq H (eP.underlying.app M)
    (eW.underlying.app (diagonalCompletedSource l Y))
    (sΔ.ordinary.hom.app M).hom eP.unitIso.hom.hom
    (completed_source_underlying l Y) (sΔ.normalization M)


/-- The constructed supported comparison transports every normalized acyclic
supported source through the universal-unit derived square.
The coefficient realizations and all ordinary squares are inputs, rather than
part of the conclusion. No trace or integration identity occurs.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), supported-source
identification; diagonal trace proof step 9.
(blueprint: lem-diagonal-completed-supported-transport).

Proof: expand the constructed isomorphism. The diagonal ordinary square's
normalization and naturality of the underlying comparison give the displayed
source normalization. For a projection f, transport the ordinary supported
isomorphism using the regular-unit comparison, its ordinary coefficient square,
and the constructed source comparison. On underlying sheaves the composite is
the composition isomorphism for direct images followed by the equality
Delta f = id and the identity direct-image isomorphism. Thus it has the required
support normalization. Apply the full universal-unit equation to the complex
concentrated in degree zero at the supported source. The single-complex and
single-functor comparison isomorphisms identify this equation with the displayed
derived source square. All other arrows in that square are isomorphisms:
exact equivalences preserve the original source's acyclicity, and the endpoint
and derived-square comparisons are isomorphisms. Consequently the condensed
single-object derived unit is an isomorphism. Together with the normalized
ordinary isomorphism this gives the asserted NormalizedSource. -/
theorem completedSupportedCoefficient_transport (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sΔ : CompletedOrdinarySquare l (diagonalImmersion Y) eP eW) :
    let i := completedSupportedCoefficientIso l Y eP eW sΔ
    ∀ (f : diagonalSurface Y ⟶ ProjectiveLine Y)
      (R : DiagonalRightDerived (diagonalTracePush l f))
      (a : DiagonalTrace.SupportedSource l Y f R)
      (s : CompletedOrdinarySquare l f eW eP),
      let R' := canonicalDiagonalRightDerived
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      ∃ b : DiagonalTrace.NormalizedSource
          (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
          R'
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)))
          (diagonalImmersion Y ≫ f = 𝟙 _)
          (SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y f),
        eP.F.mapDerivedCategory.map a.hom ≫
            (s.derive (R := R) (R' := R')).derived.iso.hom.app _ ≫
            R'.R.map
              ((eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
                (DerivedCategory.singleFunctor
                  (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l])
                    (diagonalSurface Y)) 0).map i.hom) =
          eP.singleUnit l (ProjectiveLine Y) ≫ b.hom := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
