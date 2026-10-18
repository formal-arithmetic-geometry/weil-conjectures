/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.Algebra.Ring.ULift

import Sheaf.Paper.EtaleSupportAisleGenerators
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.PseudoOpenStrictLocalFibre
import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Pointwise perversity and its localization calculus

Source: ILO, Travaux de Gabber, Exposé XVII, §5.2, Definition 5.2.1,
Proposition 5.2.2(a)--(d), and the strict-local reduction of §5.3.1(a), pp. 287--288
(blueprint: lem-per-perversity-localization-calculus).

The costalk is derived sections supported at the closed point of the actual strict
localization. The coefficient ring is the universe lift of Z/ell^n, with no change of
coefficients. The records below package the parameters and the clauses of this one lemma.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The finite coefficient ring in the universe of the etale coefficient category.
Source: ILO XVII §5.2 (blueprint: lem-per-perversity-localization-calculus). -/
abbrev PointwisePerverseCoefficients (ell n : ℕ) := ULift.{u + 1} (ZMod (ell ^ n))

/-- The ordinary bounded below small etale derived category with the specified coefficients.
Source: ILO XVII §5.2 (blueprint: lem-per-perversity-localization-calculus). -/
abbrev PointwisePerverseDerived (ell n : ℕ) (X : Scheme.{u}) :=
  DerivedCategory.Plus
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n)))

/-- The exact inverse image on the ordinary bounded below derived categories.
Source: ILO XVII 5.2.2(a) (blueprint: lem-per-perversity-localization-calculus). -/
noncomputable def pointwisePerversePull (ell n : ℕ) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    PointwisePerverseDerived ell n X ⥤ PointwisePerverseDerived ell n Y :=
  (upperStar (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n)) f).mapDerivedCategoryPlus

/-- The right derived direct image on the ordinary bounded below derived categories.
Source: ILO XVII 5.2.2(a) (blueprint: lem-per-perversity-localization-calculus). -/
noncomputable def pointwisePerversePush (ell n : ℕ) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    PointwisePerverseDerived ell n Y ⥤ PointwisePerverseDerived ell n X :=
  rightDerivedLowerStarPlus
    (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n)) f

/-- The canonical bounded below inverse/direct image adjunction.
Source: ILO XVII proof of 5.2.2 (blueprint: lem-per-perversity-localization-calculus). -/
noncomputable def pointwisePerverseAdjunction (ell n : ℕ)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    pointwisePerversePull ell n f ⊣ pointwisePerversePush ell n f :=
  (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n)) f).derivedPlus

/-- The punctured strict localization, as the complement of its closed point.
Source: ILO XVII 1.1.1 and §5.2
(blueprint: lem-per-perversity-localization-calculus). -/
noncomputable def pointwisePerversePuncture {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    (Scheme.strictLocalization s).Opens :=
  ⟨{IsLocalRing.closedPoint (Scheme.strictHenselization s)}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

/-- The geometric costalk, computed by derived closed-supported sections on the strict
localization. This is a construction, with no arbitrary costalk parameter.
Source: ILO XVII 1.1.1 and §5.2
(blueprint: lem-per-perversity-localization-calculus). -/
noncomputable def pointwisePerverseCostalk (ell n : ℕ) {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :=
  pointwisePerversePull ell n (Scheme.strictLocalizationToBase s) ⋙
    derivedSupportedEtaleSections (PointwisePerverseCoefficients.{u} ell n)
      (Scheme.strictLocalization s) (pointwisePerversePuncture s)

/-- The pointwise support condition, in every degree above the perversity.
Source: ILO XVII §5.2 (blueprint: lem-per-perversity-localization-calculus). -/
def PointwisePerverseLE (ell n : ℕ) (X : Scheme.{u}) (p : X → ℤ)
    (M : PointwisePerverseDerived ell n X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) (a : ℤ),
    p (s (IsLocalRing.closedPoint Ω)) < a →
      IsZero (pointedEtaleStalk
        ((DerivedCategory.homologyFunctor _ a).obj M.obj) s)

/-- The pointwise cosupport condition, in every degree below the perversity.
Source: ILO XVII §5.2 (blueprint: lem-per-perversity-localization-calculus). -/
def PointwisePerverseGE (ell n : ℕ) (X : Scheme.{u}) (p : X → ℤ)
    (M : PointwisePerverseDerived ell n X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) (a : ℤ),
    a < p (s (IsLocalRing.closedPoint Ω)) →
      IsZero ((DerivedCategory.homologyFunctor _ a).obj
        ((pointwisePerverseCostalk ell n s).obj M))

/-- Parameters of the lemma, including the source's specialization inequality.
Source: ILO XVII §5.2 (blueprint: lem-per-perversity-localization-calculus). -/
structure PointwisePerverseContext (ell : ℕ) where
  X : Scheme.{u}
  noetherian : IsNoetherian X
  invertible : ∀ x : X, IsUnit (ell : X.presheaf.stalk x)
  p : X → ℤ
  monotone : ∀ x y : X, Specializes x y → p x ≤ p y

/-- Pseudo-open means an embedding on spaces and an isomorphism on structure sheaves.
The latter is tested on all stalks of the canonical inverse-image structural map.
Source: ILO XVII Definition 5.2.1
(blueprint: lem-per-perversity-localization-calculus). -/
def IsPointwisePseudoOpen {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  Topology.IsEmbedding f.base ∧ ∀ y : Y, IsIso (f.stalkMap y)

/-- The three restrictions used by the locality clause, with their canonical base maps.
Source: ILO XVII §2.2.1 and §5.3.1(a)
(blueprint: lem-per-perversity-localization-calculus). -/
def IsPointwisePerverseRestriction {Y X : Scheme.{u}} (h : Y ⟶ X) : Prop :=
  Etale h ∨
    (∃ (x : X) (e : Y ≅ Spec (X.presheaf.stalk x)),
      h = e.hom ≫ X.fromSpecStalk x) ∨
    (∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (s : Spec (.of Ω) ⟶ X) (e : Y ≅ Scheme.strictLocalization s),
      h = e.hom ≫ Scheme.strictLocalizationToBase s)

/-- The heart adjunction and its normalization by ambient adjunction and truncation maps.
The ambient categories and functors are parameters to keep the equations readable.
Source: ILO XVII 5.2.2(b)--(c)
(blueprint: lem-per-perversity-localization-calculus). -/
structure PointwisePerverseHeartAdjunctionData
    {DX : Type u₁} {DY : Type u₂} {HX : Type u₃} {HY : Type u₄}
    [Category.{v₁} DX] [Category.{v₂} DY] [Category.{v₃} HX] [Category.{v₄} HY]
    (iX : HX ⥤ DX) (iY : HY ⥤ DY) (pull : DX ⥤ DY) (push : DY ⥤ DX)
    (trunc : DX ⥤ DX) (ι : trunc ⟶ 𝟭 DX) (derivedAdj : pull ⊣ push) where
  inverse : HX ⥤ HY
  extension : HY ⥤ HX
  inverseFactors : inverse ⋙ iY ≅ iX ⋙ pull
  extensionFactors : extension ⋙ iX ≅ iY ⋙ push ⋙ trunc
  adj : inverse ⊣ extension
  unit_eq : ∀ (M : HX),
    iX.map (adj.unit.app M) ≫
        extensionFactors.hom.app (inverse.obj M) ≫
        ι.app (push.obj (iY.obj (inverse.obj M))) ≫
        push.map (inverseFactors.hom.app M) = derivedAdj.unit.app (iX.obj M)
  counit_eq : ∀ (N : HY),
    iY.map (adj.counit.app N) =
      inverseFactors.hom.app (extension.obj N) ≫
        pull.map (extensionFactors.hom.app N) ≫
        pull.map (ι.app (push.obj (iY.obj N))) ≫ derivedAdj.counit.app (iY.obj N)
  counit_isIso : IsIso adj.counit
  full_extension : extension.Full
  faithful_extension : extension.Faithful

set_option maxHeartbeats 800000 in
-- Elaborating the derived-category and heart instances exceeds the default heartbeat budget.
/-- The normalized heart adjunction for the actual small etale derived functors.
Source: ILO XVII 5.2.2(b)--(c)
(blueprint: lem-per-perversity-localization-calculus). -/
abbrev PointwisePerverseHeartAdjunction (ell n : ℕ) {Y X : Scheme.{u}}
    (f : Y ⟶ X) (tX : Triangulated.TStructure (PointwisePerverseDerived ell n X))
    (tY : Triangulated.TStructure (PointwisePerverseDerived ell n Y)) :=
  PointwisePerverseHeartAdjunctionData tX.heart.ι tY.heart.ι
    (pointwisePerversePull ell n f) (pointwisePerversePush ell n f)
    (tX.truncLE 0) (tX.truncLEι 0) (pointwisePerverseAdjunction ell n f)

set_option maxHeartbeats 800000 in
-- The nested heart comparisons need the same instance-elaboration budget as their abbreviation.
set_option genInjectivity false in
/-- All clauses of pointwise perversity localization, with canonical comparisons.
Source: ILO XVII §5.2 and §5.3.1(a)
(blueprint: lem-per-perversity-localization-calculus). -/
structure PerversityLocalizationCalculus (ell n : ℕ) where
  t : ∀ B : PointwisePerverseContext.{u} ell,
    Triangulated.TStructure (PointwisePerverseDerived ell n B.X)
  upper_iff : ∀ B M, (t B).le 0 M ↔ PointwisePerverseLE ell n B.X B.p M
  lower_iff : ∀ B M, (t B).ge 0 M ↔ PointwisePerverseGE ell n B.X B.p M
  pseudo_exact : ∀ (B C : PointwisePerverseContext.{u} ell) (f : C.X ⟶ B.X),
    IsPointwisePseudoOpen f → C.p = B.p ∘ f →
    ∀ M, ((t B).le 0 M → (t C).le 0 ((pointwisePerversePull ell n f).obj M)) ∧
      ((t B).ge 0 M → (t C).ge 0 ((pointwisePerversePull ell n f).obj M))
  pseudo_lower : ∀ (B C : PointwisePerverseContext.{u} ell) (f : C.X ⟶ B.X),
    IsPointwisePseudoOpen f → C.p = B.p ∘ f →
    ∀ M, (t C).ge 0 M → (t B).ge 0 ((pointwisePerversePush ell n f).obj M)
  heartAdjunction : ∀ (B C : PointwisePerverseContext.{u} ell) (f : C.X ⟶ B.X),
    IsPointwisePseudoOpen f → C.p = B.p ∘ f →
    PointwisePerverseHeartAdjunction ell n f (t B) (t C)
  composition : ∀ (B C D : PointwisePerverseContext.{u} ell)
    (f : C.X ⟶ B.X) (g : D.X ⟶ C.X)
    (hf : IsPointwisePseudoOpen f) (hg : IsPointwisePseudoOpen g)
    (hfg : IsPointwisePseudoOpen (g ≫ f))
    (hp : C.p = B.p ∘ f) (hq : D.p = C.p ∘ g) (hr : D.p = B.p ∘ (g ≫ f)),
    ∃ e : (heartAdjunction B D (g ≫ f) hfg hr).inverse ≅
        (heartAdjunction B C f hf hp).inverse ⋙ (heartAdjunction C D g hg hq).inverse,
      (∀ M,
        (t D).heart.ι.map (e.hom.app M) ≫
            (heartAdjunction C D g hg hq).inverseFactors.hom.app
              ((heartAdjunction B C f hf hp).inverse.obj M) ≫
            (pointwisePerversePull ell n g).map
              ((heartAdjunction B C f hf hp).inverseFactors.hom.app M) =
          (heartAdjunction B D (g ≫ f) hfg hr).inverseFactors.hom.app M ≫
            (upperStarCompDerivedPlus
              (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n)) g f).hom.app
                ((t B).heart.ι.obj M)) ∧
      ∃ eR : (heartAdjunction C D g hg hq).extension ⋙
          (heartAdjunction B C f hf hp).extension ≅
            (heartAdjunction B D (g ≫ f) hfg hr).extension,
        eR = conjugateIsoEquiv
          ((heartAdjunction B C f hf hp).adj.comp (heartAdjunction C D g hg hq).adj)
          (heartAdjunction B D (g ≫ f) hfg hr).adj e
  restriction_exact : ∀ (B C : PointwisePerverseContext.{u} ell) (h : C.X ⟶ B.X),
    IsPointwisePerverseRestriction h → C.p = B.p ∘ h →
    ∀ M, ((t B).le 0 M → (t C).le 0 ((pointwisePerversePull ell n h).obj M)) ∧
      ((t B).ge 0 M → (t C).ge 0 ((pointwisePerversePull ell n h).obj M))
  generic_locality : ∀ (B C E : PointwisePerverseContext.{u} ell)
    (h : C.X ⟶ B.X), IsPointwisePerverseRestriction h → C.p = B.p ∘ h →
    ∀ (eta : B.X), IsGenericPoint eta Set.univ → IsIntegral B.X →
    (∀ x : B.X, IsDomain (B.X.presheaf.stalk x) ∧
      IsIntegrallyClosed (B.X.presheaf.stalk x)) →
    ∀ (j : E.X ⟶ B.X) (eeta : E.X ≅ Spec (B.X.residueField eta)),
    j = eeta.hom ≫ B.X.fromSpecResidueField eta → E.p = B.p ∘ j →
    ∃ (beta : pointwisePerversePush ell n j ⋙ pointwisePerversePull ell n h ≅
        pointwisePerversePull ell n (pullback.fst j h) ⋙
          pointwisePerversePush ell n (pullback.snd j h))
      (e : (t E).heart.ι ⋙ pointwisePerversePush ell n j ⋙ (t B).truncLE 0 ⋙
          pointwisePerversePull ell n h ≅
        (t E).heart.ι ⋙ pointwisePerversePull ell n (pullback.fst j h) ⋙
          pointwisePerversePush ell n (pullback.snd j h) ⋙ (t C).truncLE 0),
      (∀ M,
        (pointwisePerverseAdjunction ell n (pullback.snd j h)).homEquiv _ _
          ((upperStarCompDerivedPlus
            (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n))
            (pullback.snd j h) h).inv.app ((pointwisePerversePush ell n j).obj M) ≫
          (upperStarCompDerivedPlus
            (ModuleCat.{u + 1} (PointwisePerverseCoefficients.{u} ell n))
            (pullback.fst j h) j (pullback.snd j h ≫ h) pullback.condition.symm).hom.app
              ((pointwisePerversePush ell n j).obj M) ≫
          (pointwisePerversePull ell n (pullback.fst j h)).map
            ((pointwisePerverseAdjunction ell n j).counit.app M)) = beta.hom.app M) ∧
      (∀ M : (t E).heart.FullSubcategory,
        (pointwisePerversePull ell n h).map
            (((t B).truncLEι 0).app ((pointwisePerversePush ell n j).obj M.obj)) ≫
              beta.hom.app M.obj =
          e.hom.app M ≫ ((t C).truncLEι 0).app
            ((pointwisePerversePush ell n (pullback.snd j h)).obj
              ((pointwisePerversePull ell n (pullback.fst j h)).obj M.obj)))
  generic_components : ∀ (B C : PointwisePerverseContext.{u} ell)
    (h : C.X ⟶ B.X), IsPointwisePerverseRestriction h →
    ∀ (eta : B.X), IsGenericPoint eta Set.univ → IsIntegral B.X →
    (∀ x : B.X, IsDomain (B.X.presheaf.stalk x) ∧
      IsIntegrallyClosed (B.X.presheaf.stalk x)) →
      Set.range (pullback.snd (B.X.fromSpecResidueField eta) h) =
        {y : C.X | IsGenericPoint y (irreducibleComponent y)}
  punctured_local : ∀ (B C : PointwisePerverseContext.{u} ell)
    (A : Type u) [CommRing A] [IsStrictlyHenselianLocalRing A] (eX : B.X ≅ Spec (.of A))
    (x : B.X), eX.hom x = IsLocalRing.closedPoint A →
    ∀ (U : B.X.Opens), (U : Set B.X) = {x}ᶜ →
    ∀ (eU : C.X ≅ U.toScheme) (g : C.X ⟶ B.X), g = eU.hom ≫ U.ι →
    ∀ (hg : IsPointwisePseudoOpen g) (hp : C.p = B.p ∘ g)
      (L : (t C).heart.FullSubcategory),
    DerivedCategory.IsLE L.obj.obj (B.p x) →
      ∃ e : (t B).heart.ι.obj ((heartAdjunction B C g hg hp).extension.obj L) ≅
        ((DerivedCategory.TStructure.t.onPlus).truncLE (B.p x)).obj
          ((pointwisePerversePush ell n g).obj L.obj),
        (e.hom ≫ (DerivedCategory.TStructure.t.onPlus.truncLEι (B.p x)).app
            ((pointwisePerversePush ell n g).obj L.obj) =
          (heartAdjunction B C g hg hp).extensionFactors.hom.app L ≫
            ((t B).truncLEι 0).app ((pointwisePerversePush ell n g).obj L.obj)) ∧
        IsIso ((pointwisePerversePull ell n g).map
          ((DerivedCategory.TStructure.t.onPlus.truncLEι (B.p x)).app
            ((pointwisePerversePush ell n g).obj L.obj)))

/-- Pointwise perversities define t-structures and satisfy the full localization calculus.
Source: ILO XVII §5.2, Definition 5.2.1, Proposition 5.2.2(a)--(d), and §5.3.1(a)
(blueprint: lem-per-perversity-localization-calculus).

Proof:
1. On a nonempty Noetherian scheme, the finitely many component generic points give a
lower bound for p. The sets Phi^a = {x | p(x) >= a} are a descending specialization-closed
filtration. Apply lem-per-etale-support-aisle-generators and
lem-per-set-generated-sheaf-aisle to their supported generators. The empty scheme has
zero derived category and zero functors, so needs no minimum over an empty set.
2. Apply lem-per-supported-generators-costalk-detection to identify the orthogonal class
with costalk vanishing. Ordinary orthogonality bounds the lower truncation below, and the
cohomology sequence bounds the upper truncation below. Thus both remain in D+.
Use def-sbc-standard-tstructure-derived-category and lem-weil-heart-short-exact-triangles.
3. Pseudo-open pullback preserves stalks by lem-weil-pbc-inverse-image-stalk-germ and
costalks by lem-per-pseudo-open-strict-local-fibre. The inverse image is exact by
prop-weil-pbc-inverse-image-modules-exact. The supported-kernel interpretation agrees by
lem-per-ind-etale-closed-support-base-change, applied to the Noetherian local and strict
local schemes using lem-sc-strict-henselization-noetherian.
4. Derived adjunction (lem-trf-bounded-below-derived-adjunction) and t-orthogonality imply
that direct image preserves the lower class. Module sheaves have enough injectives by
lem-weil-pbc-module-sheaves-enough-injectives.
5. Upper truncation of direct image therefore lands in the heart. Truncation adjunction
and derived adjunction induce its Hom bijections and the two displayed normalization
identities. T-exact inverse image commutes with truncation and acts exactly on hearts.
6. Check the derived counit on stalks using prop-weil-pbc-strict-henselization-stalk-formula,
lem-per-pseudo-open-strict-local-fibre, and lem-weil-pbc-strictly-henselian-sections-stalk.
The formula is the actual module-coefficient counit by lem-weil-pbc-exchange-forget-coefficients.
Then lem-weil-pbc-derived-stalk-conservative gives its invertibility, and hence full faithfulness.
7. Composition of inverse images is lem-weil-pbc-derived-inverse-image-composition.
Its adjoint mate (lem-cat-right-adjoint-composition) is the displayed extension isomorphism;
mate normalization gives compatibility with both units and counits.
8. Etale maps, localizations, and strict localizations are locally ind-etale. Use
lem-weil-pbc-localization-colimit-principal-localizations and
lem-weil-pbc-strict-henselization-affine-chart-ind-etale. Strict localizations at corresponding
points are identical by lem-trf-ind-etale-strict-local-invariance, giving both vanishing tests.
9. Compare the two strict-local stalk formulas for the base-change square of the generic
inclusion. Their spaces are canonically the same; the exchange is its adjunction mate.
Conservativity gives beta; t-exactness then gives e with its truncation-map equation.
10. By lem-fin-etale-normal-components and lem-weil-pbc-etale-colimit-normal-local-domain,
the components remain normal integral. The generic fibre rings are domains ind-etale over
a field, hence fields by lem-weil-pbc-weak-etale-field and lem-weil-pbc-ind-etale-stability.
Thus the base-changed generic scheme gives exactly the component generic points.
11. On the strictly henselian local scheme, ordinarily truncate Rg_*L at p(x). The bound
on L makes its restriction unchanged. Its remaining cone is supported at x. Apply the
closed-support triangle (lem-exc-closed-support-triangle), exact closed direct image, and
exact strict-local global sections to check the two perverse conditions at x. This identifies
it with the perverse upper truncation, compatibly with its map to Rg_*L. -/
theorem perversity_localization_calculus (ell : ℕ) (hell : Nat.Prime ell)
    (n : ℕ) (hn : 1 ≤ n) : Nonempty (PerversityLocalizationCalculus.{u} ell n) := by
  sorry

end AlgebraicGeometry.Etale
