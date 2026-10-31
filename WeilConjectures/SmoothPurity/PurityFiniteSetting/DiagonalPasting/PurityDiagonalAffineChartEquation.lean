/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
import WeilConjectures.AlgebraicGeometry.DifferenceCoordinateSection.DifferenceFirstInputRestriction
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.EtaleCartesianTensorTowerComparison
import WeilConjectures.AlgebraicGeometry.Section.SectionTensorSquarePasting
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackSquarePrecomposition

/-! # The affine chart equation of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization hiding beta sigma

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

private def bifunctorMapIso {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {K K' M M' : C} (a : K ≅ K') (b : M ≅ M') :
    (T.obj K).obj M ≅ (T.obj K').obj M' :=
  (T.mapIso a).app M ≪≫ (T.obj K').mapIso b

private theorem section_iso_assembly {C D E : Type*}
    [Category C] [Category D] [Category E]
    (T : E ⥤ E ⥤ E) (S : C ⥤ E) (Z : D ⥤ E)
    {K M KM N Q : C} {K₀ M₀ KM₀ N₀ : D} {K₁ M₁ DD EE : E}
    (m : KM ≅ N) (n : KM₀ ≅ N₀)
    (a : K₁ ≅ S.obj K) (b : M₁ ≅ S.obj M) (γ : N ≅ Q)
    (c : S.obj Q ≅ Z.obj N₀)
    (τ : S.obj KM ≅ (T.obj (S.obj K)).obj (S.obj M))
    (ζ : Z.obj KM₀ ≅ (T.obj (Z.obj K₀)).obj (Z.obj M₀))
    (d : Z.obj K₀ ≅ DD) (e : Z.obj M₀ ≅ EE)
    (c₁ : K₁ ≅ DD) (c₂ : M₁ ≅ EE)
    (h : ((T.map a.hom).app M₁ ≫ (T.obj (S.obj K)).map b.hom) ≫
        τ.inv ≫ S.map m.hom ≫ S.map γ.hom ≫ c.hom =
      ((T.map c₁.hom).app M₁ ≫ (T.obj DD).map c₂.hom) ≫
        ((T.map d.inv).app EE ≫ (T.obj (Z.obj K₀)).map e.inv) ≫
          ζ.inv ≫ Z.map n.hom) :
    (bifunctorMapIso T a b ≪≫ τ.symm ≪≫ S.mapIso m).hom ≫
        (S.mapIso γ ≪≫ c).hom =
      (bifunctorMapIso T c₁ c₂).hom ≫
        (bifunctorMapIso T d.symm e.symm ≪≫ ζ.symm ≪≫ Z.mapIso n).hom := by
  simpa only [bifunctorMapIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using h

private theorem bifunctor_postcomp_congr {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) {K K' M M' N : C}
    {a a' : K ⟶ K'} {b b' : M ⟶ M'} (ha : a = a') (hb : b = b')
    (c : (T.obj K').obj M' ⟶ N) :
    ((T.map a).app M ≫ (T.obj K').map b) ≫ c =
      ((T.map a').app M ≫ (T.obj K').map b') ≫ c := by
  cases ha
  cases hb
  rfl

private theorem normalized_restriction (P : PurityFiniteSetting.{u})
    {W X B : Scheme.{u}} (v : W ⟶ X) (h : X ⟶ B) (q' : W ⟶ B)
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated q'] [LocallyOfFiniteType q'] [QuasiCompact q']
    [IsNoetherian W] [IsNoetherian X] [IsNoetherian B]
    [HasCompactification h] [HasCompactification q']
    (hv : q' = v ≫ h) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let : HasCompactification (v ≫ h) := HasCompactification.of_eq hv
    ProEtale.DifferenceCoordinateSection.normalizedE P v h q' hv aB =
      dualizingCongr P.Coefficient P hv ≪≫ etaleRestriction P.Coefficient P v h := by
  dsimp only
  subst q'
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : X.Over (Spec (.of P.field.k)) := ⟨h ≫ aB⟩
  let : W.Over (Spec (.of P.field.k)) := ⟨(v ≫ h) ≫ aB⟩
  let : h.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (v ≫ h).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : v.IsOver (Spec (.of P.field.k)) := ⟨(Category.assoc v h aB).symm⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ aB))
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h ≫ aB))
  let : LocallyOfFiniteType (W ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType ((v ≫ h) ≫ aB))
  let : QuasiCompact (W ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact ((v ≫ h) ≫ aB))
  have he := SectionRestriction.sourceEtale_locality_congr P v h (v ≫ h) rfl
  calc
    _ = (Etale.sectionStructuralLocalityIso P.Coefficient v h (v ≫ h) rfl).symm := he
    _ = _ := by
      let hu := Etale.existsUnique_etaleAmbientAdjointLocalityIso P.Coefficient v h
        (HasCompactification.compactification h)
        (HasCompactification.compactification (v ≫ h))
        (Etale.rightDerivedUpperShriek P.Coefficient h)
        (Etale.rightDerivedUpperShriek P.Coefficient (v ≫ h))
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h)
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (v ≫ h))
      have hE : Classical.choose hu.exists = Classical.choose hu :=
        (Classical.choose_spec hu).2 _ (Classical.choose_spec hu.exists)
      apply Iso.ext
      dsimp only [dualizingCongr, Etale.sectionStructuralLocalityIso,
        etaleRestriction, restrictionUnit, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.refl_hom]
      rw [Category.id_comp, hE]
      rfl

private theorem congr_dualizing (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    (f g : U ⟶ V) [f.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (w : f = g) :
    let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let := compactification P f
    let := compactification P g
    (congr P f g w).hom.app (coefficientUnit (ModuleCat P.Coefficient) V) =
      (dualizingCongr P.Coefficient P w).hom := by
  subst g
  simp only [ProEtale.FiniteEtaleNormalization.congr, dualizingCongr, conjugateIsoEquiv_apply_hom,
    Etale.unboundedEtaleLowerShriekCongr, Iso.refl_hom, conjugateEquiv_id,
    NatTrans.id_app, coefficientUnit, Etale.dualizingComplex]

private theorem square_via_composite
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {R Q D E : Scheme.{u}} (J : R ⟶ D) (r : R ⟶ Q) (q : D ⟶ E) (G : Q ⟶ E)
    (sq : CommSq J r q G) (z : R ⟶ E) (hz : z = J ≫ q) (hz' : z = r ≫ G)
    (K : Etale.DerivedCategoryModule A E) :
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).app K =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r G z hz').app K).symm ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) J q z hz).app K := by
  subst z
  rfl

set_option maxHeartbeats 2000000 in
-- The chart has many canonical compactifications and derived-comparison instances.
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory in
/-- The ordered affine difference-coordinate equation on a single chart triple.
This assertion has neither the global equation nor an open naturality clause.
Source: composition coherence Step 1, diagonal section pasting proof Steps 8--12
(blueprint: lem-route-diagonal-section-pasting-chart).

Proof: affineGeometry constructs the Cartesian block square for q, and nu
is its inverse beta restriction followed by zero-section pullback of sigma.
Affine difference tower factorization supplies the translated etale maps G,
H, J and F = H followed by J, with the Cartesian square defining R. Apply
etale Cartesian tower tensor comparison to q, P_e, G and H. Its final
identity compares sigma_(a,b) followed by E_F with pullback of sigma_(q,P_e),
whose two inputs are H-pullback of inverse beta_(q,G) followed by E_H, and
a-pullback of E_G. Pull this identity along t and precompose with gamma_f
tensor gamma_g. Difference coordinate section identifications identify the
first input with the specified c1 of ChartEquation, the second with c2, and
the output with c3. The identities Ft = z_(d+e) and Gs = z_e, together with
the derived pullback compositor, turn the middle arrow into nu. Naturality
of the tensor pullback comparison gives exactly the two composites in
ChartEquation. The comparisons E agree with etaleSection by the uniqueness
of their counit normalization. The translated coordinate and concatenation
formulas work with empty affine schemes and either empty coordinate block.
No global equality, localization argument, or Tate trivialization is used. -/
theorem diagonalSectionPastingChart (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffine X] [IsAffine Y] [IsAffine Z]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (x : X ⟶ A d Y) (y : Y ⟶ A e Z) [Etale x] [Etale y]
    (hx : x ≫ pr d Y = f) (hy : y ≫ pr e Z = g) :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    ChartEquation P.Coefficient P d e f g aZ x y hx hy := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let aX := (f ≫ g) ≫ aZ
  let aY := g ≫ aZ
  let : X.Over (Spec (.of P.field.k)) := ⟨aX⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aX)
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aX)
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aY)
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aY)
  let : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aZ)
  let : QuasiCompact (Z ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aZ)
  let : f.IsOver (Spec (.of P.field.k)) := ⟨(Category.assoc f g aZ).symm⟩
  let : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have hfirst := difference_first_input_restriction P f g d e x y hx hy
  let fac := AlgebraicGeometry.AffineDifferenceTower.factorization
    (k := P.field.k) f g d e x y hx hy
  let hHJ := fac.1
  let hHa := fac.2.1
  let hGpr := fac.2.2.1
  let hJq := fac.2.2.2.1
  let hGs := fac.2.2.2.2.1
  let hFt := fac.2.2.2.2.2.1
  let fac1 := fac.2.2.2.2.2.2.2.2
  let hFpr := fac1.1
  let hGe := fac1.2.1
  let hGsep := fac1.2.2.1
  let hGlft := fac1.2.2.2.1
  let hGqc := fac1.2.2.2.2.1
  let hHe := fac1.2.2.2.2.2.1
  let hHsep := fac1.2.2.2.2.2.2.1
  let hHlft := fac1.2.2.2.2.2.2.2.1
  let fac2 := fac1.2.2.2.2.2.2.2.2
  let hHqc := fac2.1
  let hJe := fac2.2.1
  let hJsep := fac2.2.2.1
  let hJlft := fac2.2.2.2.1
  let hJqc := fac2.2.2.2.2.1
  let hFe := fac2.2.2.2.2.2.1
  let hFsep := fac2.2.2.2.2.2.2.1
  let hFlft := fac2.2.2.2.2.2.2.2.1
  let fac3 := fac2.2.2.2.2.2.2.2.2
  let hFqc := fac3.1
  let hQa := fac3.2.1
  let hWa := fac3.2.2.1
  let hRa := fac3.2.2.2.1
  let hWfa := fac3.2.2.2.2.1
  let hWga := fac3.2.2.2.2.2.1
  let hAda := fac3.2.2.2.2.2.2.1
  let hAea := fac3.2.2.2.2.2.2.2.1
  let fac4 := fac3.2.2.2.2.2.2.2.2
  let hAdea := fac4.1
  let hAdVa := fac4.2.1
  let hAeTa := fac4.2.2.1
  let hAeVa := fac4.2.2.2.1
  let fac5 := fac4.2.2.2.2.2.2.2.2
  let hRsq := fac5.1
  let hAffsq := fac5.2.1
  let hsq := fac5.2.2.1
  let hPe := fac5.2.2.2.1
  let hPde := fac5.2.2.2.2.1
  let hqQ := fac5.2.2.2.2.2.1
  let fac6 := fac5.2.2.2.2.2.2.2.2
  let hHfe := fac6.1
  let hGge := fac6.2.1
  let hHfz := fac6.2.2.1
  let := hGe
  let := hGsep
  let := hGlft
  let := hGqc
  let := hHe
  let := hHsep
  let := hHlft
  let := hHqc
  let := hJe
  let := hJsep
  let := hJlft
  let := hJqc
  let := hFe
  let := hFsep
  let := hFlft
  let := hFqc
  let := hQa
  let := hWa
  let := hRa
  let := hWfa
  let := hWga
  let := hAda
  let := hAea
  let := hAdea
  let := hAdVa
  let := hAeTa
  let := hAeVa
  let := hsq
  let := hPe
  let := hPde
  let := hqQ
  let := hHfe
  let := hGge
  let := (geometryProperties d e f g).1
  let := (geometryProperties d e f g).2.1
  let := (geometryProperties d e f g).2.2.1
  let := (geometryProperties d e f g).2.2.2.1
  let := (geometryProperties d e f g).2.2.2.2
  let := affineDimension d X
  let := affineDimension e Y
  let := affineDimension (d + e) X
  let := (affineGeometry d e X).2.2.2.2.2.1
  let := (affineGeometry d e X).2.2.2.2.2.2.1
  let := (affineGeometry d e X).2.2.2.2.2.2.2.1
  let Q₀ := AlgebraicGeometry.AffineDifferenceTower.Q f g
  let R₀ := AlgebraicGeometry.AffineDifferenceTower.R d f g
  let W₀ := AlgebraicGeometry.AffineDifferenceTower.W f g
  let t := pullback.diagonal (f ≫ g)
  let s₀ := s f g
  let G := differenceSecond e f g y
  let HH := AlgebraicGeometry.AffineDifferenceTower.H f g x
  let JJ := AlgebraicGeometry.AffineDifferenceTower.J d f g y
  let FF := differenceTotal d e f g x y
  let r : R₀ ⟶ Q₀ := R₀ ↘ Q₀
  let aQ := pullback.fst (f ≫ g) g ≫ aX
  let : Q₀.Over (Spec (.of P.field.k)) := ⟨aQ⟩
  let : R₀.Over (Spec (.of P.field.k)) := ⟨r ≫ aQ⟩
  let : W₀.Over (Spec (.of P.field.k)) := ⟨pullback.fst (f ≫ g) (f ≫ g) ≫ aX⟩
  let : (A e X).Over (Spec (.of P.field.k)) := ⟨pr e X ≫ aX⟩
  let : (A (d + e) X).Over (Spec (.of P.field.k)) := ⟨pr (d + e) X ≫ aX⟩
  let : r.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (pr e X).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (q d e X).IsOver (Spec (.of P.field.k)) :=
    ⟨(Category.assoc _ _ _).symm.trans
      (congrArg (fun u ↦ u ≫ aX) (affineGeometry d e X).2.2.2.1)⟩
  let : G.IsOver (Spec (.of P.field.k)) :=
    ⟨(Category.assoc _ _ _).symm.trans (congrArg (fun u ↦ u ≫ aX) hGpr)⟩
  let : JJ.IsOver (Spec (.of P.field.k)) := by
    constructor
    change JJ ≫ (pr (d + e) X ≫ aX) = r ≫ aQ
    rw [← (affineGeometry d e X).2.2.2.1]
    simp only [← Category.assoc]
    rw [hJq]
    simp only [Category.assoc, hGpr]
    rfl
  let : (a f g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change a f g ≫ aQ = pullback.fst (f ≫ g) (f ≫ g) ≫ aX
    rw [← Category.assoc, (geometry f g).2.2.1]
  let : HH.IsOver (Spec (.of P.field.k)) := by
    constructor
    change HH ≫ (r ≫ aQ) = pullback.fst (f ≫ g) (f ≫ g) ≫ aX
    rw [← Category.assoc, hHa, ← Category.assoc, (geometry f g).2.2.1]
  let : FF.IsOver (Spec (.of P.field.k)) :=
    ⟨(Category.assoc _ _ _).symm.trans (congrArg (fun u ↦ u ≫ aX) hFpr)⟩
  let : (pullback.fst (f ≫ g) (f ≫ g)).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (pr (d + e) X).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (pullback.fst (f ≫ g) g).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (Q₀ ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aQ)
  let : QuasiCompact (Q₀ ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aQ)
  let : LocallyOfFiniteType (R₀ ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (r ≫ aQ))
  let : QuasiCompact (R₀ ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (r ≫ aQ))
  let : LocallyOfFiniteType (W₀ ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst (f ≫ g) (f ≫ g) ≫ aX))
  let : QuasiCompact (W₀ ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.fst (f ≫ g) (f ≫ g) ≫ aX))
  let : LocallyOfFiniteType ((A e X) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pr e X ≫ aX))
  let : QuasiCompact ((A e X) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pr e X ≫ aX))
  let : LocallyOfFiniteType ((A (d + e) X) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pr (d + e) X ≫ aX))
  let : QuasiCompact ((A (d + e) X) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pr (d + e) X ≫ aX))
  let β := beta P.Coefficient P d hRsq (pr (d + e) X ≫ aX)
  let β₀ := beta P.Coefficient P d hAffsq (pr d X ≫ aX)
  let sqF : CommSq FF (a f g) (q d e X) G := ⟨by
    calc
      FF ≫ q d e X = (HH ≫ JJ) ≫ q d e X :=
        congrArg (fun v ↦ v ≫ q d e X) hHJ.symm
      _ = HH ≫ (r ≫ G) := by rw [Category.assoc, hJq]
      _ = (HH ≫ r) ≫ G := (Category.assoc HH r G).symm
      _ = a f g ≫ G := congrArg (fun v ↦ v ≫ G) hHa⟩
  let Eₐ := normalizedE P HH r (a f g) hHa.symm aQ
  let Eᵦ := normalizedE P G (pr e X) (pullback.fst (f ≫ g) g) hGpr.symm aX
  let E_F := normalizedE P FF (pr (d + e) X)
    (pullback.fst (f ≫ g) (f ≫ g)) hFpr.symm aX
  let A₁ := Eₐ ≪≫ (pull P HH).mapIso β.symm ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) HH JJ FF hHJ.symm).app
      (Etale.dualizingComplex P.Coefficient (q d e X))).symm
  let B₁ := (pull P (a f g)).mapIso Eᵦ ≪≫
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sqF).app
      (Etale.dualizingComplex P.Coefficient (pr e X))
  let m := sigma P.Coefficient P d (a f g) (pullback.fst (f ≫ g) g)
      (pullback.fst (f ≫ g) (f ≫ g) ≫ aX) ≪≫
    dualizingCongr P.Coefficient P (geometry f g).2.2.1
  let n := sigma P.Coefficient P d (q d e X) (pr e X)
      (pr (d + e) X ≫ aX) ≪≫
    dualizingCongr P.Coefficient P (affineGeometry d e X).2.2.2.1
  have htower := etale_cartesian_tensor_tower P r (q d e X) d G JJ (pr e X) e
    HH (a f g) (pullback.fst (f ≫ g) g) FF (pr (d + e) X)
    (pullback.fst (f ≫ g) (f ≫ g)) hHa.symm hGpr.symm hHJ.symm
    (affineGeometry d e X).2.2.2.1.symm (geometry f g).2.2.1.symm
    hRsq sqF β rfl
  simp only [congr_dualizing] at htower
  have htop : m.hom ≫ E_F.hom = (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) A₁.hom
    B₁.hom) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) FF _ _).inv ≫
        (pull P FF).map n.hom := by
    -- Keep the native tensor bifunctor abstract while exposing the isomorphism fields.
    dsimp only [m, n, E_F, A₁, B₁, Eₐ, Eᵦ, normalizedE,
      sigma, AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.sigma,
      thetaIso, finiteThetaIso, compositionUnit, exceptionalUnit,
      finiteExceptionalComposition, comp, Iso.trans, Iso.symm, Iso.app,
      Functor.mapIso, asIso] at htower ⊢
    simp only [congr_dualizing, Category.assoc] at htower ⊢
    exact htower.trans
      (bifunctor_postcomp_congr
        (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) W₀)
        (Category.assoc (dualizingCongr P.Coefficient P hHa.symm).hom _ _).symm rfl _)
  let cₜ := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) t FF (zero (d + e) X)
    hFt.symm
  let cₐ := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) t (a f g) s₀
    (geometry f g).2.2.2.1.symm
  let c_q := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) (zero (d + e) X) (q d
    e X)
    (zero e X) (affineGeometry d e X).2.2.1.symm
  let c_G := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) s₀ G (zero e X)
    hGs.symm
  let γ₁ := gammaF P.Coefficient P d f g aZ
  let γ₂ := gammaG P.Coefficient P e f g aZ ≪≫ cₐ.app
    (Etale.dualizingComplex P.Coefficient (pullback.fst (f ≫ g) g))
  let δ₁ := (pull P (zero (d + e) X)).mapIso β₀.symm ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) (zero (d + e) X) (first d e
      X) (zero d X)
      (affineGeometry d e X).2.1.symm).app _).symm
  let δ₂ := (c_q.app (Etale.dualizingComplex P.Coefficient (pr e X))).symm
  let ch := chartGeometry d e f g x y hx hy
  let c₁ := etaleSection P.Coefficient P (differenceFirst d f x) (pr d X)
    (pullback.fst f f) (pullback.diagonal f) (zero d X)
    ch.2.2.2.1.symm ch.2.2.2.2.1.symm
  let c₂ := gammaG P.Coefficient P e f g aZ ≪≫
    etaleSection P.Coefficient P G (pr e X) (pullback.fst (f ≫ g) g) s₀ (zero e X)
      hGpr.symm hGs.symm
  let c₃ := etaleSection P.Coefficient P FF (pr (d + e) X)
    (pullback.fst (f ≫ g) (f ≫ g)) t (zero (d + e) X) hFpr.symm hFt.symm
  have hi₁ : γ₁.hom ≫ (pull P t).map A₁.hom ≫ cₜ.inv.app _ ≫ δ₁.hom =
      c₁.hom := by
    have hh : γ₁.hom ≫ (pull P t).map A₁.hom ≫ cₜ.inv.app _ ≫ δ₁.hom =
        (pull P (pullback.diagonal f)).map
          (normalizedE P (differenceFirst d f x) (pr d X) (pullback.fst f f)
            ch.2.2.2.1.symm aX).hom ≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            (pullback.diagonal f) (differenceFirst d f x) (zero d X)
            ch.2.2.2.2.1.symm).inv.app _ := hfirst.symm
    rw [normalized_restriction P (differenceFirst d f x) (pr d X)
      (pullback.fst f f) ch.2.2.2.1.symm aX] at hh
    exact hh
  have hi₂ : γ₂.hom ≫ (pull P t).map B₁.hom ≫ cₜ.inv.app _ ≫ δ₂.hom =
      c₂.hom := by
    let sq₀ : CommSq (zero (d + e) X) s₀ (q d e X) G :=
      ⟨(affineGeometry d e X).2.2.1.trans hGs.symm⟩
    have hp := Etale.pullback_square_precomposition P.Coefficient t FF (a f g)
      (q d e X) G sqF (zero (d + e) X) s₀ hFt.symm
      (geometry f g).2.2.2.1.symm sq₀
      (Etale.dualizingComplex P.Coefficient (pr e X))
    have hz : (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sq₀).app
        (Etale.dualizingComplex P.Coefficient (pr e X)) =
      (c_G.app (Etale.dualizingComplex P.Coefficient (pr e X))).symm ≪≫
        c_q.app (Etale.dualizingComplex P.Coefficient (pr e X)) := by
      exact square_via_composite P.Coefficient (zero (d + e) X) s₀ (q d e X) G
        sq₀ (zero e X) (affineGeometry d e X).2.2.1.symm hGs.symm _
    dsimp only [γ₂, B₁, c₂, etaleSection, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    have hn := cₐ.hom.naturality Eᵦ.hom
    simp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, reassoc_of% hp]
    have hzh := congrArg Iso.hom hz
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv] at hzh
    rw [reassoc_of% hzh]
    simp only [δ₂, Iso.symm_hom, Iso.app_inv, Iso.hom_inv_id_app, Category.comp_id]
    dsimp only [Eᵦ]
    rw [normalized_restriction P G (pr e X) (pullback.fst (f ≫ g) g) hGpr.symm aX]
    rfl
  have hpaste := Etale.section_tensor_square_pasting (ModuleCat.{u + 1} P.Coefficient) t FF (zero (d
    + e) X) hFt.symm
    _ _ _ _ _ _ _ _ _ _ m.hom n.hom γ₁ γ₂ A₁ B₁ E_F δ₁ δ₂ htop
  dsimp only at hpaste
  have hpaste := hpaste.trans
    (bifunctor_postcomp_congr (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
      hi₁ hi₂ _)
  have heq : (kappa P.Coefficient P d e f g aZ).hom ≫ c₃.hom =
      (tensorComparison P.Coefficient P c₁ c₂).hom ≫
        (nu P.Coefficient P d e X (f ≫ g ≫ aZ)).hom := by
    have hiso := section_iso_assembly
      (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
      (pull P t) (pull P (zero (d + e) X))
      m n γ₁ γ₂ E_F (cₜ.app _).symm
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) t _ _)
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
        (zero (d + e) X) _ _) δ₁ δ₂ c₁ c₂ hpaste
    dsimp only [E_F] at hiso
    rw [normalized_restriction P FF (pr (d + e) X)
      (pullback.fst (f ≫ g) (f ≫ g)) hFpr.symm aX] at hiso
    exact hiso
  exact congrArg
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map heq

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
