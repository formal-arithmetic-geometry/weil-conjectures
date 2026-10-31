/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence

/-! # Scalar compatibility for one ordered affine coordinate

Source: blueprint Charts, scalar mates for the standard affine-line compactification
(blueprint: lem-sp-affine-line-canonical-scalar-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem compose_counit_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {Q : E ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {M' : D' ⥤ E'} {Q' : E' ⥤ D'}
    (a : L ⊣ R) (b : M ⊣ Q) (a' : L' ⊣ R') (b' : M' ⊣ Q')
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M')
    (K : E) (r : S.obj (R.obj (Q.obj K)) ⟶ R'.obj (T.obj (Q.obj K)))
    (q : T.obj (Q.obj K) ⟶ Q'.obj (U.obj K))
    (hr : β.app (R.obj (Q.obj K)) ≫ L'.map r ≫ a'.counit.app (T.obj (Q.obj K)) =
      T.map (a.counit.app (Q.obj K)))
    (hq : γ.app (Q.obj K) ≫ M'.map q ≫ b'.counit.app (U.obj K) =
      U.map (b.counit.app K)) :
    γ.app (L.obj (R.obj (Q.obj K))) ≫ M'.map (β.app (R.obj (Q.obj K))) ≫
      M'.map (L'.map (r ≫ R'.map q)) ≫ (a'.comp b').counit.app (U.obj K) =
      U.map ((a.comp b).counit.app K) := by
  simp only [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
  have hn := a'.counit.naturality q
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hn' := congrArg (fun z ↦ M'.map z) hn
  simp only [Functor.map_comp] at hn'
  rw [reassoc_of% hn']
  have hr' := congrArg (fun z ↦ M'.map z) hr
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have hm := γ.naturality (a.counit.app (Q.obj K))
  simp only [Functor.comp_map] at hm
  rw [← reassoc_of% hm, hq, ← U.map_comp]

private theorem open_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategoryModule A V) :
    (ExceptionalCoefficients.openIso φ j).hom.app
        ((ordinaryFinitePullback A j).obj K) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((scalarPullbackIso φ j).inv.app K) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} B) j).symm).counit.app ((scalarExtension φ V).obj K) =
    (scalarExtension φ V).map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) j).symm).counit.app K) := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  let b := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let v := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x v).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom)
  have he : α.natTrans = (scalarPullbackIso φ j).inv := by
    change (ProEtale.scalarPullbackEtaleIsoFromMate φ j).inv = _
    exact congrArg Iso.inv (scalarPullback_eq φ j)
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b v x
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom))
  change ((mateEquiv a b).symm α).natTrans = _ at h
  change ((mateEquiv a b).symm α).natTrans = (ExceptionalCoefficients.openIso φ j).inv at h
  have hc := mateEquiv_counit_symm a b α K
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (α.natTrans.app K) ≫ b.counit.app ((scalarExtension φ V).obj K) =
    ((mateEquiv a b).symm α).natTrans.app _ ≫
      (scalarExtension φ V).map (a.counit.app K) at hc
  rw [he, h] at hc
  have hh := congrArg (fun z ↦ (ExceptionalCoefficients.openIso φ j).hom.app
    ((ordinaryFinitePullback A j).obj K) ≫ z) hc
  simpa only [a, b, ordinaryFinitePullback, Category.assoc,
    Iso.hom_inv_id_app_assoc] using hh

private theorem etaleCoefficientMap_eq_compactScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) :
    ProEtale.CoefficientCompatibility.etaleCoefficientMap φ c L =
      (Etale.compactScalarMap φ c).app L := by
  have hi : ((Etale.ExceptionalCoefficients.openIso φ c.i).app L).inv =
      (Etale.properOpenCoefficientOpenIso φ c.i L).inv :=
    Etale.compactScalarOpen_normalization φ c.i L
  have he := Iso.ext_inv hi
  unfold ProEtale.CoefficientCompatibility.etaleCoefficientMap
    Etale.compactScalarMap Etale.ExceptionalCoefficients.compactSupportMap
  rw [← he]
  rfl

private theorem line_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (DB : OrdinaryFiniteP1Datum B N hB tB S hS)
    (K : DerivedCategoryModule A S) :
    (compactScalarMap φ (affineTraceLineCompactification S)).app
        ((affineTraceLineRight A N hA S).obj K) ≫
      (affineTraceLineLeft B S).map
        (ProEtale.reductionEtaleLineScalarIso φ S N hA hB hS K).hom ≫
      (affineTraceLineAdjunction B N hB tB S hS DB).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((affineTraceLineAdjunction A N hA tA S hS DA).counit.app K) := by
  have h := compose_counit_scalar
    (affineTraceOpenAdjunction A S) DA.adjunction
    (affineTraceOpenAdjunction B S) DB.adjunction
    (scalarExtension φ (AffineSpace PUnit.{u + 1} S))
    (scalarExtension φ (ProjectiveLine S)) (scalarExtension φ S)
    (ExceptionalCoefficients.openIso φ (ProjectiveLine.affineChart S)).hom
    (scalarMate φ (ProjectiveLine S ↘ S)) K
    ((scalarPullbackIso φ (ProjectiveLine.affineChart S)).inv.app
      ((ordinaryFiniteP1Right A N hA S).obj K))
    (ProEtale.reductionEtaleP1ScalarIso φ S N hA hB hS K).hom
    (by simpa only [affineTraceOpenAdjunction, affineTraceOpenLeft] using
      (open_scalar_counit φ (ProjectiveLine.affineChart S)
        ((ordinaryFiniteP1Right A N hA S).obj K)))
    (ordinaryChartP1CounitScalar φ N hN hA hB S hS tA tB DA DB K)
  simpa only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    affineTraceLineCompactification, Compactification.copy, Functor.comp_map,
    ProEtale.reductionEtaleLineScalarIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, affineTraceLineAdjunction, affineTraceComposeAdjunction_eq,
    affineTraceOpenLeft, affineTraceLineRight, affineTraceLineLeft,
    rightDerivedLowerShriekOfCompactification, ordinaryFinitePushforward, rightDerivedLowerStar,
    Functor.comp_obj, Category.assoc] using h

/-- The canonical root-normalized right comparison respects the actual open/projective
composite counit.
Source: blueprint Charts, scalar mates for the standard affine-line compactification
(blueprint: lem-sp-affine-line-canonical-scalar-counit).

Proof: The standard compactification coefficient map is the proper coefficient map
followed by the open-extension coefficient isomorphism. The latter is defined by
transposing the open unit against the exact scalar/pullback comparison. The triangle
identities therefore give the open counit square, after transport from exact to derived
pullback. The projective counit square is lem-sp-p1-counit-scalar. Its same-annihilator
root map is the identity: cancel the root inclusion in roots_power, using N/N=1.
Its generator equation then identifies the sheaf adjunct with reductionEtaleTateMap
by uniqueness. The scalar-adjunction single-complex equation identifies its derived
normalization with reductionEtaleTateExtensionMap. Hence its right comparison is
reductionEtaleP1ScalarIso. Expand the composite counit. Naturality of the open counit
moves the projective right comparison through it. Apply the open counit square,
then naturality of the proper scalar map, then the projective counit square.
Functoriality gives exactly the scalar image of the A composite counit. Finite-Tor
constructibility supplies the allowed projective input; no coefficient flatness is used.
The formulas also hold for empty schemes, zero objects and zero coefficient rings. -/
theorem affineLineCanonicalScalarCounit
    (ell p n : ℕ) [Fact ell.Prime] (hp : 0 < p) (hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
    (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
    (dA : OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
    (dB : OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT)
    (K : DerivedCategoryModule A T)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A T K) :
    ProEtale.CoefficientCompatibility.etaleCoefficientMap φ
        (affineTraceLineCompactification T) ((affineTraceLineRight A (ell ^ n) hA T).obj K) ≫
      (affineTraceLineLeft B T).map
        (ProEtale.reductionEtaleLineScalarIso φ T (ell ^ n) hA hB hT K).hom ≫
      (affineTraceLineAdjunction B (ell ^ n) hB tB T hT dB).counit.app
        ((scalarExtension φ T).obj K) =
    (scalarExtension φ T).map
      ((affineTraceLineAdjunction A (ell ^ n) hA tA T hT dA).counit.app K) := by
  let _ : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  let _ : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (T ↘ Spec (.of k))
  let _ : IsNoetherian T := ⟨⟩
  have h := line_scalar_counit φ (ell ^ n)
    (Nat.pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime ell)))
    hA hB T hT tA tB dA dB K
  rw [etaleCoefficientMap_eq_compactScalarMap]
  exact h

end AlgebraicGeometry.Etale
