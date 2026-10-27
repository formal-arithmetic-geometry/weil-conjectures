/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.EtaleSumCounitScalar
public import Sheaf.Paper.AffineCounitScalar
public import Sheaf.Paper.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry

/-! # Scalar factorization and the raw chart counit

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, sum then ordered affine integration
(blueprint: lem-sp-raw-chart-scalar-counit-pasting).

The affine space is the published ordered coordinate model `affineTraceTower Y d`.
Its right functor is the ordered model of p* K(d)[2d]. Exact etale inverse image
is used for the sum adjunction. The canonical scalar identification is transported
from the published derived-pullback model; it is not specified by a counit equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.Etale

/-- The explicit raw right functor: ordered affine pullback/twist/shift, then e*.
Source: blueprint Charts, explicit right functor
(blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
def rawChartRight (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    {U Y : Scheme.{u}} (d : ℕ) (e : U ⟶ affineTraceTower Y d) :
    DerivedCategoryModule R Y ⥤ DerivedCategoryModule R U :=
  affineTraceRight R N hR Y d ⋙ (upperStar (ModuleCat.{u + 1} R) e).mapDerivedCategory

/-- The canonical tensor/pullback, ordered Tate and shift identification for hG.
Only the canonical exact/left-derived pullback identification changes presentations.
Source: blueprint Charts, canonical right comparison
(blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
def rawChartScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) (K : DerivedCategoryModule A Y) :
    (scalarExtension φ U).obj ((rawChartRight A N hA d e).obj K) ≅
      (rawChartRight B N hB d e).obj ((scalarExtension φ Y).obj K) :=
  (scalarExtension φ U).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm.app
        ((affineTraceRight A N hA Y d).obj K)) ≪≫
    ProEtale.reductionEtaleChartScalarIso φ N hA hB hY d e K ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e).app
      ((affineTraceRight B N hB Y d).obj ((scalarExtension φ Y).obj K))

/-- Unpack the canonical chart comparison and use naturality of the presentation iso.
Source: blueprint Charts, Step 2 (blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
private theorem rawChartScalarIso_factor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) (K : DerivedCategoryModule A Y) :
    (rawChartScalarIso φ N hA hB hY d e K).hom =
      (properOpenCoefficientPullbackIso φ e).inv.app
          ((affineTraceRight A N hA Y d).obj K) ≫
        (upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategory.map
          (ProEtale.reductionEtaleAffineScalarIso φ Y N hA hB hY d K).hom := by
  dsimp only [rawChartScalarIso, ProEtale.reductionEtaleChartScalarIso,
    properOpenCoefficientPullbackIso, rawChartRight, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  congr 2
  exact (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) e).hom.naturality _

/-- Transport constructible homology, its bounds, and finite Tor amplitude along an iso.
Source: blueprint Charts, Step 1 (blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
private theorem chartProperty_of_iso (R : Type (u + 1)) [CommRing R] [Finite R]
    (T : Scheme.{u}) {K L : DerivedCategoryModule R T} (e : K ≅ L)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty R T K) :
    ProEtale.AdjunctionTransfer.etaleProperty R T L := by
  refine ⟨⟨?_, ?_⟩,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e hK.2⟩
  · intro i
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (hK.1.1 i)
    exact Scheme.IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e)
  · obtain ⟨a, b, hab, hz⟩ := hK.1.2
    exact ⟨a, b, hab, fun i hi ↦ (hz i hi).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩

/-- Apply chart-domain preservation in the published ordered affine presentation.
Source: blueprint Charts, Step 1 (blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
private theorem rawChart_domains
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (n : ℕ) (hR : ((ell ^ n : ℕ) : R) = 0)
    {U Y : Scheme.{u}} [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] (hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (he : e ≫ affineTraceProjection Y d ≫ (Y ↘ Spec (.of k)) = (U ↘ Spec (.of k)))
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (affineTraceProjection Y d)) :
    (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R Y K →
      ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower Y d)
        ((affineTraceRight R (ell ^ n) hR Y d).obj K)) ∧
    (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower Y d) K →
      ProEtale.AdjunctionTransfer.etaleProperty R U
        ((upperStar (ModuleCat.{u + 1} R) e).mapDerivedCategory.obj K)) ∧
    (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R U K →
      ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower Y d)
        ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory.obj K)) ∧
    (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower Y d) K →
      ProEtale.AdjunctionTransfer.etaleProperty R Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K)) := by
  let : (affineTraceTower Y d).Over (Spec (.of k)) :=
    ⟨affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : (affineTraceProjection Y d).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : e.IsOver (Spec (.of k)) := ⟨he⟩
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian
    (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  have := affineTraceNoetherian Y d
  have := HasCompactification.of_isOver (S := Spec (.of k)) e
  let ce := HasCompactification.compactification e
  have hd := ProEtale.AdjunctionTransfer.etaleCtfChartDomain
    ell k R n hR (affineTraceProjection Y d) c (affineTraceProjection Y d)
  have hedom := ProEtale.AdjunctionTransfer.etaleCtfChartDomain ell k R n hR e ce e
  refine ⟨?_, ?_, ?_, hd.1⟩
  · intro K hK
    obtain ⟨η⟩ := (affineTraceRight_normalForm R (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hR Y hY d).1
    have h := hd.2.2.2.1 d (2 * (d : ℤ)) K hK
    apply chartProperty_of_iso R _ _ h
    exact ((η.app K) ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((derivedTensorRight (ModuleCat.{u + 1} R) _ _).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} R) (affineTraceProjection Y d)).app K) ≪≫
          ((derivedTensorSymmetry (ModuleCat.{u + 1} R) _).app _).app _)).symm
  · intro K hK
    have h := hedom.2.2.2.1 0 0 K hK
    apply chartProperty_of_iso R _ _ h
    exact (shiftFunctorZero _ ℤ).app _ ≪≫
      derivedTensorLeftUnitor (ModuleCat.{u + 1} R) U _
  · intro K hK
    obtain ⟨M⟩ := nonempty_etaleCompactSupportNormalization R
    exact chartProperty_of_iso R _ ((M.comparison e ce).app K) (hedom.1 K hK)

/-- The specified left scalar arrow s: beta at E(M), followed by P_B of sigma_e(M).
Source: blueprint Charts, sum then affine scalar comparison
(blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
def rawChartLeftScalarMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Y : Scheme.{u}} (d : ℕ)
    (e : U ⟶ affineTraceTower Y d) [Etale e]
    (c : Compactification (affineTraceProjection Y d)) (M : DerivedCategoryModule A U) :
    (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M)) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.obj
          ((scalarExtension φ U).obj M)) :=
  etaleCoefficientMap φ c
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
      ((sumCoefficientIso φ e).hom.app M)

/-- The raw composite counit w = P(v at G(K)) followed by u at K. The first counit
is the actual sum/evaluation counit, and the second is the specified ordered affine
counit in the chosen compact-support presentation.
Source: blueprint Charts, raw composite adjunction
(blueprint: lem-sp-raw-chart-scalar-counit-pasting). -/
def rawChartCounit (N : ℕ) (hN : 0 < N) (R : Type (u + 1))
    [CommRing R] [Finite R] (hR : (N : R) = 0)
    {U Y : Scheme.{u}} [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) [Etale e]
    (c : Compactification (affineTraceProjection Y d)) (K : DerivedCategoryModule R Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory.obj
          ((rawChartRight R N hR d e).obj K)) ⟶ K :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} R) e inferInstance).counit.app
          ((affineTraceRight R N hR Y d).obj K)) ≫
    affineScalarCompactificationCounit N hN R hR Y hY d c K

/-- The canonical right factorization and the scalar equation for the actual raw
sum-then-ordered-affine counit, with all functors preserving the indicated finite-Tor
constructible domains. No flatness or finite projective dimension of B/A is assumed.

Source: blueprint Charts, raw chart expansion, Steps 1--4
(blueprint: lem-sp-raw-chart-scalar-counit-pasting).

Proof:
1. Apply lem-sp-etale-ctf-chart-domain to compact support, pullback, Tate powers,
shifts and scalar extension. For sum extension use a compactification in the standing
setting, sk-def-sfb-dc-setting, then lem-asd-etale-compact-support-normalization.
All schemes involved are Noetherian by lem-weil-pbc-finite-type-over-noetherian.
2. Expand the canonical right comparison on flat-term K-flat models. The composition
and tensor comparisons of lem-sfb-ringed-derived-monoidal-comparisons identify the
pullbacks. Apply lem-sp-finite-tate-balanced-scalar-pullback in each ordered Tate
factor and lem-asd-etale-finite-twist-pullback for the roots-induced composition
identifications. Apply lem-weil-pbc-cochain-pullback-tensor-shift to the shifts.
Both paths send the same pulled-back x and ordered roots to the same tensor with b;
on a Tate factor the coefficient rule is (z tensor c) tensor b to z tensor phi(c)b.
Localization gives the displayed factorization, including the unit case d=0.
3. Set J=G_A K and t=a_d(K). Naturality of the actual sum counit at t rewrites the
left side of the scalar equation as u_B P_B(t) P_B(v_B E_B(a_e(J)) sigma_e(h_A J))
beta_d(E_A h_A J). Apply lem-sp-etale-sum-counit-scalar at the allowed input J.
4. Naturality of beta_d at v_A(J) moves T_V(v_A(J)) across beta_d. The first three
remaining factors are precisely the affine counit equation of lem-sp-affine-counit-scalar.
Functoriality of T_Y gives T_Y(u_A P_A(v_A)), as required. In dimension zero the
affine adjunction is the identity, so this reduces to the actual sum-counit equation.
-/
theorem rawChartScalarCounitPasting
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0)
    {U Y : Scheme.{u}} [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (_he : e ≫ affineTraceProjection Y d ≫ (Y ↘ Spec (.of k)) = (U ↘ Spec (.of k)))
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (affineTraceProjection Y d)) :
    ∃ (hNoeth : IsNoetherian Y) (hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤))),
      (∀ (K : DerivedCategoryModule A Y) (_hK : ProEtale.AdjunctionTransfer.etaleProperty A Y K),
        (rawChartScalarIso φ (ell ^ n) hA hB hY d e K).hom =
          (properOpenCoefficientPullbackIso φ e).inv.app
              ((affineTraceRight A (ell ^ n) hA Y d).obj K) ≫
            (upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategory.map
              (ProEtale.reductionEtaleAffineScalarIso φ Y (ell ^ n) hA hB hY d K).hom) ∧
      (∀ (K : DerivedCategoryModule A Y) (_hK : ProEtale.AdjunctionTransfer.etaleProperty A Y K),
        rawChartLeftScalarMap φ d e c ((rawChartRight A (ell ^ n) hA d e).obj K) ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
            ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
              (rawChartScalarIso φ (ell ^ n) hA hB hY d e K).hom) ≫
          @rawChartCounit.{u} (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
            B _ _ hB U Y hNoeth hY d e _ c ((scalarExtension φ Y).obj K) =
        (scalarExtension φ Y).map
          (@rawChartCounit.{u} (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
            A _ _ hA U Y hNoeth hY d e _ c K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A Y K →
        ProEtale.AdjunctionTransfer.etaleProperty A (affineTraceTower Y d)
          ((affineTraceRight A (ell ^ n) hA Y d).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A (affineTraceTower Y d) K →
        ProEtale.AdjunctionTransfer.etaleProperty A U
          (((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A U K →
        ProEtale.AdjunctionTransfer.etaleProperty A (affineTraceTower Y d)
          (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A (affineTraceTower Y d) K →
        ProEtale.AdjunctionTransfer.etaleProperty A Y
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty B Y K →
        ProEtale.AdjunctionTransfer.etaleProperty B (affineTraceTower Y d)
          ((affineTraceRight B (ell ^ n) hB Y d).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty B (affineTraceTower Y d) K →
        ProEtale.AdjunctionTransfer.etaleProperty B U
          (((upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategory).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty B U K →
        ProEtale.AdjunctionTransfer.etaleProperty B (affineTraceTower Y d)
          (((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty B (affineTraceTower Y d) K →
        ProEtale.AdjunctionTransfer.etaleProperty B Y
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A Y K →
        ProEtale.AdjunctionTransfer.etaleProperty B Y ((scalarExtension φ Y).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A (affineTraceTower Y d) K →
        ProEtale.AdjunctionTransfer.etaleProperty B (affineTraceTower Y d)
          ((scalarExtension φ (affineTraceTower Y d)).obj K)) ∧
      (∀ K, ProEtale.AdjunctionTransfer.etaleProperty A U K →
        ProEtale.AdjunctionTransfer.etaleProperty B U ((scalarExtension φ U).obj K))  := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have hNoeth : IsNoetherian Y := ⟨⟩
  have hk : IsUnit ((ell ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.2
      (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) _hEll)).pow n
  have hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using
      hk.map ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop).hom
  have : Fact (ringChar k).Prime :=
    ⟨by rw [ringChar.eq k p]; exact
      (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt _hp)⟩
  have : Fact (ringChar k ≠ ell) := ⟨by simpa only [ringChar.eq k p] using _hEll⟩
  let : (affineTraceTower Y d).Over (Spec (.of k)) :=
    ⟨affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : e.IsOver (Spec (.of k)) := ⟨_he⟩
  have : (affineTraceProjection Y d).IsOver (Spec (.of k)) := ⟨rfl⟩
  have ha := rawChart_domains ell p _hp _hEll k A n hA hY d e _he c
  have hb := rawChart_domains ell p _hp _hEll k B n hB hY d e _he c
  have hsY := (ProEtale.AdjunctionTransfer.etaleCtfChartScalarDomain
    ell k φ n hA hB Y).1
  have hsV := (ProEtale.AdjunctionTransfer.etaleCtfChartScalarDomain
    ell k φ n hA hB (affineTraceTower Y d)).1
  have hsU := (ProEtale.AdjunctionTransfer.etaleCtfChartScalarDomain
    ell k φ n hA hB U).1
  refine ⟨hNoeth, hY, ?_, ?_, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2,
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hsY, hsV, hsU⟩
  · intro K _hK
    exact rawChartScalarIso_factor φ (ell ^ n) hA hB hY d e K
  · intro K hK
    let J := (affineTraceRight A (ell ^ n) hA Y d).obj K
    let J' := (affineTraceRight B (ell ^ n) hB Y d).obj ((scalarExtension φ Y).obj K)
    let PB := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let EB := (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory
    let vA := (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).counit.app J
    let vB := (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).counit
    let t := (ProEtale.reductionEtaleAffineScalarIso φ Y (ell ^ n) hA hB hY d K).hom
    have hsum := (etaleSumCounitScalar ell p _hp _hEll k n
      (by simpa only [Nat.cast_pow] using hA) (by simpa only [Nat.cast_pow] using hB)
      φ e J (ha.1 K hK)).1
    have hinner : (sumCoefficientIso φ e).hom.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj J) ≫
        EB.map (rawChartScalarIso φ (ell ^ n) hA hB hY d e K).hom ≫ vB.app J' =
        (scalarExtension φ (affineTraceTower Y d)).map vA ≫ t := by
      let σ := (sumCoefficientIso φ e).hom.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj J)
      let a := (properOpenCoefficientPullbackIso φ e).inv.app J
      have hn := (derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) e inferInstance).counit_naturality t
      have hf := congrArg (fun z ↦ σ ≫ EB.map z ≫ vB.app J')
        (rawChartScalarIso_factor φ (ell ^ n) hA hB hY d e K)
      refine hf.trans ?_
      simp only [Functor.map_comp, Category.assoc]
      calc
        _ = σ ≫ EB.map a ≫ vB.app ((scalarExtension φ (affineTraceTower Y d)).obj J) ≫ t := by
          simpa only [Category.assoc, Functor.comp_map, Functor.id_map] using
            congrArg (fun z ↦ σ ≫ EB.map a ≫ z) hn
        _ = _ := by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ t) hsum
    have hnat := etaleProEtaleCoefficientCompatibility_naturality
      ell p _hp _hEll k
      ⟨n, fun x ↦ by rw [← Nat.cast_smul_eq_nsmul A, hA, zero_smul]⟩
      ⟨n, fun x ↦ by rw [← Nat.cast_smul_eq_nsmul B, hB, zero_smul]⟩
      φ (affineTraceProjection Y d) c _ J
      (ha.2.2.1 _ (ha.2.1 _ (ha.1 K hK))) (ha.1 K hK) vA
    obtain ⟨_, _, haff⟩ := affine_counit_scalar ell p _hp _hEll k A B φ n hA hB Y d c K hK
    let uB := affineScalarCompactificationCounit (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) B hB Y hY d c ((scalarExtension φ Y).obj K)
    have hinner' := congrArg (fun z ↦ etaleCoefficientMap φ c _ ≫ PB.map z ≫ uB) hinner
    dsimp only [rawChartLeftScalarMap, rawChartCounit, rawChartRight]
    simp only [Functor.map_comp, Category.assoc] at hinner' ⊢
    refine hinner'.trans ?_
    calc
      _ = (etaleCoefficientMap φ c _ ≫
          PB.map ((scalarExtension φ (affineTraceTower Y d)).map vA)) ≫ PB.map t ≫ uB :=
        (Category.assoc _ _ _).symm
      _ = ((scalarExtension φ Y).map
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map vA) ≫
          etaleCoefficientMap φ c J) ≫ PB.map t ≫ uB :=
        congrArg (fun z ↦ z ≫ PB.map t ≫ uB) hnat.symm
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun z ↦ (scalarExtension φ Y).map
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map vA) ≫ z)
          haff

end AlgebraicGeometry.Etale
