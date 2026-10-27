/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups P2 and E7
-/
module

public import Sheaf.Paper.FiniteSiteCoordinates
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.Targets.VectorBundlePurity

import Sheaf.Paper.OrderedTateExponentPullback
import Sheaf.Paper.OrderedAffineTraceExponent

/-! # Root transitions of the ordinary local vector trace

Source: vector-bundle integration, local chart construction; Stacks 03PK.
(blueprint: lem-pur-vector-local-trace-exponent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

private theorem coefficient_square_core
    {C D H J : Type*} [Category C] [Category D] [Category H] [Category J]
    (U : C ⥤ D) (V : D ⥤ H) (W : C ⥤ J) (P : J ⥤ H)
    (c : U ⋙ V ≅ W ⋙ P) {Ks Kr : C} {Ls Lr : J} {Rs Rr : H}
    (B : Ks ⟶ Kr) (b : Ls ⟶ Lr)
    (bs : W.obj Ks ≅ Ls) (br : W.obj Kr ≅ Lr)
    (ds : Rs ≅ P.obj Ls) (dr : Rr ≅ P.obj Lr)
    (hb : W.map B ≫ br.hom = bs.hom ≫ b) :
    V.map (U.map B) ≫ (c.app Kr ≪≫ P.mapIso br ≪≫ dr.symm).hom =
      (c.app Ks ≪≫ P.mapIso bs ≪≫ ds.symm).hom ≫
        (ds.hom ≫ P.map b ≫ dr.inv) := by
  have hn := c.hom.naturality B
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, ← P.map_comp_assoc, hb, P.map_comp]
  simp only [Category.assoc]

private theorem coefficient_square
    {C D H J : Type*} [Category C] [Category D] [Category H] [Category J]
    (U : C ⥤ D) (V : D ⥤ H) (W : C ⥤ J) (P : J ⥤ H)
    {F₁ F₂ : C ⥤ H} (c₁ : U ⋙ V ≅ F₁) (c₂ : F₁ ≅ F₂) (c₃ : F₂ ≅ W ⋙ P)
    {Ks Kr : C} {Ls Lr : J} {Rs Rr : H}
    (B : Ks ⟶ Kr) (b : Ls ⟶ Lr)
    (bs : W.obj Ks ≅ Ls) (br : W.obj Kr ≅ Lr)
    (ds : Rs ≅ P.obj Ls) (dr : Rr ≅ P.obj Lr)
    (hb : W.map B ≫ br.hom = bs.hom ≫ b) :
    V.map (U.map B) ≫
        (c₁.app Kr ≪≫ c₂.app Kr ≪≫ c₃.app Kr ≪≫ P.mapIso br ≪≫ dr.symm).hom =
      (c₁.app Ks ≪≫ c₂.app Ks ≪≫ c₃.app Ks ≪≫ P.mapIso bs ≪≫ ds.symm).hom ≫
        (ds.hom ≫ P.map b ≫ dr.inv) := by
  simpa only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Category.assoc] using
    coefficient_square_core U V W P (c₁ ≪≫ c₂ ≪≫ c₃) B b bs br ds dr hb

private theorem paste_trace_square
    {C D : Type*} [Category C] [Category D] (R T : C ⥤ D)
    {Xs Xr Ys Yr : C} {Ms Mr U : D}
    (m : Ms ⟶ Mr) (er : Mr ⟶ R.obj Xr) (es : Ms ⟶ R.obj Xs)
    (f : Xs ⟶ Xr) (cr : Xr ⟶ Yr) (cs : Xs ⟶ Ys) (z : Ys ⟶ Yr)
    (kr : R.obj Yr ⟶ T.obj Yr) (ks : R.obj Ys ⟶ T.obj Ys)
    (tr : T.obj Yr ⟶ U) (ts : T.obj Ys ⟶ U)
    (he : m ≫ er = es ≫ R.map f) (hc : f ≫ cr = cs ≫ z)
    (hk : R.map z ≫ kr = ks ≫ T.map z) (ht : T.map z ≫ tr = ts) :
    m ≫ er ≫ R.map cr ≫ kr ≫ tr = es ≫ R.map cs ≫ ks ≫ ts := by
  rw [reassoc_of% he, ← R.map_comp_assoc, hc, R.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hk, ht]

private theorem compact_comparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hA : (N : A) = 0) (hB : (M : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (M : Γ(T, ⊤))) (d : ℕ)
    (z : (Etale.affineTraceRight A M hB T d).obj (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hA T d).obj (Etale.ordinaryFiniteUnit A T)) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection T d)).map z ≫
      (Etale.affineLinearCompactComparison N hN A hA T hT d).inv =
    (Etale.affineLinearCompactComparison M hM A hB T hT' d).inv ≫
      (Etale.affineTraceLeft A T d).map z := by
  let Kr : DerivedCategory.Plus
      (Sheaf (affineTraceTower T d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (Etale.exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 T hT d).2.1))⟩
  let Ks : DerivedCategory.Plus
      (Sheaf (affineTraceTower T d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (Etale.exists_affineSpaceTopTrace M hM A hB) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 T hT' d).2.1))⟩
  let c := (Etale.affineTracePlusCompatibility A T d).symm ≪≫
    Functor.isoWhiskerRight (Etale.affineTraceCompactSupportComparison A T d)
      DerivedCategory.Plus.ι ≪≫
    Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection T d)
  change (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection T d)).map z ≫ c.inv.app Kr =
    c.inv.app Ks ≫ (Etale.affineTraceLeft A T d).map z
  exact c.inv.naturality (ObjectProperty.homMk (X := Ks) (Y := Kr) z)

/-- The prescribed ordinary trace on one frame commutes with the root-power transition.
This is a local equation, before any global integration is glued or compared between sites.
Source: blueprint vector-bundle integration, construction of the maps a_i; Stacks 03PK,
and integration-exponent-transpose-transport, proof Steps 6--10.
(blueprint: lem-pur-vector-local-trace-exponent).

Proof: the power map on roots commutes with the Kummer boundary. On the projective
line it therefore identifies both components of the normalized decomposition: the
shifted unit by naturality of the adjunction unit, and the infinity Chern class by
the Kummer boundary. Cancel the two decompositions and project to the constant
summand to identify their inverse traces. Naturality of the open-extension counit
then identifies the restricted affine-line traces. Induct on the ordered affine
tower: the length-zero transition and counit are identities; at a successor apply
the previous left functor to the last affine counit and compose with the preceding
counit. The induction hypothesis and the affine-line equation identify the two
composites. Finally the inverse-frame exchange, inverse-image composition, Tate
pullback, and compact-support composition comparisons are natural in the coefficient.
Paste these squares with the ordered trace equation. This gives precisely the
local map displayed below. Uniqueness of normalized twist transport and projective
trace data permits every t,D in the statement. Rank zero is the identity tower;
on an empty frame every displayed map is the unique map. No scalar-extension
flatness or finite-field assumption occurs.
-/
theorem vectorIntegrationLocalTrace_exponentTransition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (Dr : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hr tr T hT)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs)
    (Ds : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ (s + 1) : ℕ) : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (Scheme.finiteTateCoefficient l E n)
        (l ^ (s + 1)) hs ts T hT)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n) V.ι).map
      ((Etale.vectorBundlePurityLower (Scheme.finiteTateCoefficient l E n) S d F).map
        ((Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
          (VectorBundleZeroSection.π S d F)).map
            (baseExponentComparison l E n S hS r s hrs hr hs d).hom)) ≫
      Etale.vectorIntegrationLocalTrace (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) _ hr tr Dr S
        (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F V e =
      Etale.vectorIntegrationLocalTrace (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) _ hs ts Ds S
        (by simpa only [Nat.cast_pow] using hS.pow (s + 1)) d F V e := by
  let A := Scheme.finiteTateCoefficient l E n
  let := (Etale.vectorIntegration_geometry S d F).1
  let := (Etale.vectorIntegration_geometry S d F).2.1
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let hV : IsUnit (l : Γ(V.toScheme, ⊤)) := by
    simpa using hS.map V.ι.appTop.hom
  let hSr : IsUnit ((l ^ (r + 1) : ℕ) : Γ(S, ⊤)) := by
    simpa only [Nat.cast_pow] using hS.pow (r + 1)
  let hSs : IsUnit ((l ^ (s + 1) : ℕ) : Γ(S, ⊤)) := by
    simpa only [Nat.cast_pow] using hS.pow (s + 1)
  let hVr := affineTracePullbackInvertible (l ^ (r + 1)) V.ι hSr
  let hVs := affineTracePullbackInvertible (l ^ (s + 1)) V.ι hSs
  let B := (baseExponentComparison l E n S hS r s hrs hr hs d).hom
  let b := (baseExponentComparison l E n V.toScheme hV r s hrs hr hs d).hom
  let q := Etale.vectorIntegrationChart S d F V e
  let p := affineTraceProjection V.toScheme d
  let cfr := Etale.affineLinearCoefficientDescent A (l ^ (r + 1)) hr tr
    V.toScheme hVr d
  let cfs := Etale.affineLinearCoefficientDescent A (l ^ (s + 1)) hs ts
    V.toScheme hVs d
  let z := cfs.hom ≫ (Etale.ordinaryFinitePullback A p).map b ≫ cfr.inv
  let cr := Etale.vectorIntegrationChartCoefficient A (l ^ (r + 1)) hr tr
    S hSr d F V e
  let cs := Etale.vectorIntegrationChartCoefficient A (l ^ (s + 1)) hs ts
    S hSs d F V e
  have hb := baseExponentComparison_pullback l E n V.ι hS r s hrs hr hs tr ts d
  have hc : (Etale.ordinaryFinitePullback A q).map
        ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map B) ≫
      cr.hom = cs.hom ≫ z := by
    exact coefficient_square _ _ _ _
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        q (VectorBundleZeroSection.π S d F)).symm
      (eqToIso (congrArg (Etale.ordinaryFinitePullback A)
        (Etale.vectorIntegrationChart_isPullback S d F V e).w))
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p V.ι)
      B b
      (Etale.vectorIntegrationBaseCoefficientPullback A (l ^ (s + 1)) hs ts
        V.ι hSs d)
      (Etale.vectorIntegrationBaseCoefficientPullback A (l ^ (r + 1)) hr tr
        V.ι hSr d) cfs cfr hb
  let R := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) p
  have he := (Etale.rightDerivedLowerShriekBaseChangeMap A
    (Etale.vectorIntegrationChart_isPullback S d F V e)).naturality
      ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map B)
  simp only [Functor.comp_map] at he
  have hk := compact_comparison_naturality A (l ^ (r + 1)) (l ^ (s + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
    hr hs V.toScheme hVr hVs d z
  have ht := affineTraceCounit_exponentTransition l E n V.toScheme hV
    r s hrs hr hs tr Dr ts Ds d
  change (Etale.ordinaryFinitePullback A V.ι).map
      ((Etale.vectorBundlePurityLower A S d F).map
        ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map B)) ≫
    Etale.vectorIntegrationLocalTrace (l ^ (r + 1)) _ A hr tr Dr S hSr d F V e =
    Etale.vectorIntegrationLocalTrace (l ^ (s + 1)) _ A hs ts Ds S hSs d F V e
  unfold Etale.vectorIntegrationLocalTrace
  change (Etale.ordinaryFinitePullback A V.ι).map
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d F)).map
          ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map B)) ≫
    (Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V e)).app
        (Etale.vectorIntegrationCoefficient A (l ^ (r + 1)) hr S d F) ≫
    R.map cr.hom ≫ (Etale.affineLinearCompactComparison (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hr V.toScheme hVr d).inv ≫
      Etale.affineTraceCounit A (l ^ (r + 1)) hr tr Dr V.toScheme hVr d =
    (Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V e)).app
        (Etale.vectorIntegrationCoefficient A (l ^ (s + 1)) hs S d F) ≫
    R.map cs.hom ≫ (Etale.affineLinearCompactComparison (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hs V.toScheme hVs d).inv ≫
      Etale.affineTraceCounit A (l ^ (s + 1)) hs ts Ds V.toScheme hVs d
  have h := paste_trace_square R (Etale.affineTraceLeft A V.toScheme d)
    ((Etale.ordinaryFinitePullback A V.ι).map
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d F)).map
          ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map B)))
    ((Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V e)).app
        (Etale.vectorIntegrationCoefficient A (l ^ (r + 1)) hr S d F))
    ((Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V e)).app
        (Etale.vectorIntegrationCoefficient A (l ^ (s + 1)) hs S d F))
    ((Etale.ordinaryFinitePullback A q).map
      ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map B))
    cr.hom cs.hom z
    (Etale.affineLinearCompactComparison (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hr V.toScheme hVr d).inv
    (Etale.affineLinearCompactComparison (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hs V.toScheme hVs d).inv
    (Etale.affineTraceCounit A (l ^ (r + 1)) hr tr Dr V.toScheme hVr d)
    (Etale.affineTraceCounit A (l ^ (s + 1)) hs ts Ds V.toScheme hVs d)
    he hc hk ht
  exact h

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
