/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ProEtaleLisseOrigin
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Topology.Stratification
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import all Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.IntrinsicRealizationOriginComparison
import Sheaf.Paper.IntrinsicRealizationFlat
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import all Sheaf.SixFunctors.FlatModelGeneration
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all Sheaf.SixFunctors.OpenClosedFlatness
import all Sheaf.Paper.ProEtaleFiniteModelStalks
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Flat models and generators

Source: Weil conjectures blueprint, main-20261015, `sec-six-functors-basics/`
`sk-lem-sf-flat-model`, statement and complement (blueprint: sk-lem-sf-flat-model).

## Main statements

* `proEtaleFlatModel`: bounded flat constructible representatives.
* `proEtaleFlatStratification`: finite projective constant local models on strata.
* `proEtaleThickGeneration`, `etaleThickGeneration`: the Noetherian complement.
* `proEtaleThickGeneration_eq`: equality with the thick envelope in the standing setting.

The generator predicates below spell out the statement's locally closed extension by zero.
They use the scheme-theoretic image of the actual stratum immersion, not an arbitrary closed
subscheme with the same underlying set. Closed direct image is exact here, so its value on
`L[0]` also represents `Rg_*j_!L`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

-- Fix the auxiliary universe of the imported max-universe instance at zero.
local instance sf_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

private theorem sf_lisse_of_iso
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)} (e : F ≅ G)
    (h : IsLisseProEtaleFixedModuleSheaf X A F) :
    IsLisseProEtaleFixedModuleSheaf X A G := by
  constructor
  · obtain ⟨I, U, f, hf, hm⟩ := h.1
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨em⟩⟩ := hm i
    exact ⟨M, ⟨(((ProEt.topology X).overPullback _ (U i)).mapIso e).symm ≪≫ em⟩⟩
  · intro Ω _ _ x
    have := h.2 Ω x
    let es := colim.mapIso
      (Functor.isoWhiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
        ((sheafToPresheaf _ _).mapIso e))
    exact Finite.of_equiv (proEtaleGeometricFixedModuleStalk x A F)
      (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso es.hom))

private theorem sf_restriction_flat
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F) :
    ObjectProperty.flat ((proEtaleModuleRestriction X A).obj F) := by
  apply (intrinsic_flat_iff X A _).mpr
  exact site_flat_of_iso A (intrinsicRealizationRestrictionIso X A F) hF

private theorem sf_projective_models
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (hl : IsLocallyConstantProEtaleFixedModuleSheaf X A F)
    (hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricFixedModuleStalk x A F))
    (hf : ObjectProperty.flat F) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      ∀ i : I, ∃ M : ModuleCat.{u + 1} A,
        Finite M ∧ Module.Projective A M ∧
        Nonempty (F.over (U i) ≅
          (constantSheaf ((ProEt.topology X).over (U i)) (ModuleCat.{u + 1} A)).obj M) := by
  classical
  obtain ⟨I, U, f, hcover, hmodels⟩ := hl
  let I' := {i : I // Nonempty (U i).left}
  have hcover' : Presieve.ofArrows (fun i : I' ↦ U i.1) (fun i ↦ f i.1) ∈
      (ProEt.precoverage X).coverings _ := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hcover ⊢
    change Presieve.ofArrows (fun i : I ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at hcover
    change Presieve.ofArrows (fun i : I' ↦ (U i.1).left) (fun i ↦ (f i.1).left) ∈
      proetalePrecoverage X
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 X = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simp only [hw] at hcover ⊢
    let E : PreZeroHypercover X := ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom⟩
    have : QuasiCompactCover E := presieve₀_mem_qcPrecoverage_iff.mp hcover.1
    let E' : PreZeroHypercover X := ⟨I', fun i ↦ (U i.1).left, fun i ↦ (U i.1).hom⟩
    have : QuasiCompactCover E' := by
      constructor
      intro V hV
      obtain ⟨n, a, W, hW, hcov⟩ :=
        QuasiCompactCover.exists_isAffineOpen_of_isCompact E hV.isCompact
      refine IsCompactOpenCovered.of_finite
        (fun j : {j : Fin n // Nonempty (U (a j)).left} ↦ ⟨a j.1, j.2⟩)
        (fun j ↦ W j.1) (fun j ↦ (hW j.1).isCompact) ?_
      rw [← hcov]
      ext x
      simp only [Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨j, y, hy, rfl⟩
        exact ⟨j.1, y, hy, rfl⟩
      · rintro ⟨j, y, hy, rfl⟩
        exact ⟨⟨j, ⟨y⟩⟩, y, hy, rfl⟩
    refine ⟨presieve₀_mem_qcPrecoverage_iff.mpr ‹QuasiCompactCover E'›, ?_⟩
    rw [Scheme.ofArrows_mem_precoverage_iff]
    have hweak := hcover.2
    rw [Scheme.ofArrows_mem_precoverage_iff] at hweak
    exact ⟨fun x ↦ by
      obtain ⟨i, y, hy⟩ := hweak.1 x
      exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩, fun i ↦ (U i.1).prop⟩
  refine ⟨I', fun i ↦ U i.1, fun i ↦ f i.1, hcover', ?_⟩
  rintro ⟨i, hi⟩
  obtain ⟨M, ⟨e⟩⟩ := hmodels i
  let w : (U i).left := Classical.choice hi
  let Ω := AlgebraicClosure ((U i).left.residueField w)
  let y : Spec (.of Ω) ⟶ (U i).left := (SpecToEquivOfField Ω _).2
    ⟨w, CommRingCat.ofHom (algebraMap ((U i).left.residueField w) Ω)⟩
  let x := y ≫ (U i).hom
  let Φ := ProEtale.geometricPoint x
  let z : Φ.fiber.obj (U i) := ⟨Over.homMk y rfl⟩
  let es : proEtaleGeometricFixedModuleStalk x A F ≅ M :=
    ProEtale.geometricStalkIsoFiber x A F ≪≫
    (ProEtale.sheafFiberOverIso Φ z A F).symm ≪≫
    (Φ.over z).sheafFiber.mapIso e ≪≫ (Φ.over z).sheafFiberConstantSheafIso M
  have : Finite (proEtaleGeometricFixedModuleStalk x A F) := hs Ω x
  have hM : Finite M := Finite.of_equiv _ es.toLinearEquiv.toEquiv
  have hflat : Module.Flat A M := by
    apply (ModuleCat.flat_iff_flat M).mp
    exact ObjectProperty.prop_of_iso _
      (ProEtale.geometricStalkIsoFiber x A F).symm (Φ.flat_sheafFiber_obj hf) |>
      ObjectProperty.prop_of_iso _ es
  have : Module.Finite A M := Module.Finite.of_finite
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Module.Flat A M := hflat
  exact ⟨M, hM, Module.Flat.projective_of_finitePresentation, ⟨e⟩⟩

private theorem sf_comparison_constructible
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (hG : IsConstructibleEtaleModuleSheaf G) :
    IsConstructibleProEtaleModuleSheaf X A
      ((ProEtale.finiteCoefficientIntrinsicComparison X A).obj G) := by
  let R := ProEtale.finiteCoefficientIntrinsicRealization X A
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  obtain ⟨e⟩ := ProEtale.intrinsicRealization_restriction X A
  rw [proEtaleModuleRestriction_constructible_iff]
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mp hG
  exact ProEtale.isConstructible_of_iso (e.app (C.obj G)).symm
    (ProEtale.isConstructible_comparisonUpperStar_obj G)

private theorem sf_comparison_reflects_flat
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h : ObjectProperty.flat
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L)) :
    ObjectProperty.flat L := by
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft (C.obj L)) := h.1.1
  have : PreservesFiniteLimits (C ⋙ MonoidalCategory.tensorLeft (C.obj L)) :=
    Limits.comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft L ⋙ C) :=
    preservesFiniteLimits_of_natIso (Functor.Monoidal.commTensorLeft C L)
  exact preservesFiniteLimits_of_reflects_of_preserves _ C

private theorem sf_comparison_ctf_full
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).ι ⋙
        (ProEtale.finiteCoefficientIntrinsicComparison X A).mapDerivedCategory).Full := by
  let E := Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  let B := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) X
  let F := (ProEtale.finiteCoefficientIntrinsicComparison X A).mapDerivedCategory
  have : (B.ι ⋙ F).Full := (finiteRing_constructibleDerived_origin X A).1
  refine ⟨fun {K L} f ↦ ?_⟩
  have hK := (flatModel_etale_ctf_iff X (ULift.{u + 1, u} A) K.obj).mpr K.property
  have hL := (flatModel_etale_ctf_iff X (ULift.{u + 1, u} A) L.obj).mpr L.property
  let K' : B.FullSubcategory := ⟨K.obj, hK.1, hK.2.1⟩
  let L' : B.FullSubcategory := ⟨L.obj, hL.1, hL.2.1⟩
  obtain ⟨g, hg⟩ := (B.ι ⋙ F).map_surjective (X := K') (Y := L') f
  exact ⟨ObjectProperty.homMk g.hom, hg⟩

private theorem sf_comparison_ctf_faithful
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).ι ⋙
        (ProEtale.finiteCoefficientIntrinsicComparison X A).mapDerivedCategory).Faithful := by
  let B := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) X
  let F := (ProEtale.finiteCoefficientIntrinsicComparison X A).mapDerivedCategory
  have : (B.ι ⋙ F).Faithful := (finiteRing_constructibleDerived_origin X A).2.1
  refine ⟨fun {K L} f g h ↦ ?_⟩
  have hK := (flatModel_etale_ctf_iff X (ULift.{u + 1, u} A) K.obj).mpr K.property
  have hL := (flatModel_etale_ctf_iff X (ULift.{u + 1, u} A) L.obj).mpr L.property
  let K' : B.FullSubcategory := ⟨K.obj, hK.1, hK.2.1⟩
  let L' : B.FullSubcategory := ⟨L.obj, hL.1, hL.2.1⟩
  have ht : (B.ι ⋙ F).map (show K' ⟶ L' from ObjectProperty.homMk f.hom) =
      (B.ι ⋙ F).map (show K' ⟶ L' from ObjectProperty.homMk g.hom) := h
  have he : (show K' ⟶ L' from ObjectProperty.homMk f.hom) =
      (show K' ⟶ L' from ObjectProperty.homMk g.hom) :=
    (B.ι ⋙ F).map_injective ht
  exact ObjectProperty.hom_ext _ (congrArg (fun (a : K' ⟶ L') ↦ a.hom) he)

/-- The pro-etale closure generators of the statement: `g_*j_!L` in degree zero, where
`j` is the open factor of an actual stratum immersion through its scheme-theoretic image,
and `L` is lisse with flat stalks. The canonical intrinsic realization transports the
fixed-module extension and direct image, including their scalar actions. Lisse and flat
are equivalently locally finite projective over the finite ring.
Source: blueprint `sk-lem-sf-flat-model`, paragraph 1 and complement
(blueprint: sk-lem-sf-flat-model). -/
def sfProEtaleClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : proEtaleRingModules (str.domain i) (proEtaleConstantRing (str.domain i) A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsLisseProEtaleFixedModuleSheaf (str.domain i) (ULift.{u + 1, u} A)
      ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L) ∧
    SheafOfModules.IsFlatOnSite (J := ProEt.topology (str.domain i))
      (R := proEtaleConstantRing (str.domain i) A) L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L)))))

/-- The etale closure generators `Rg_*j_!L`: the closed direct image is exact, so the
ordinary sheaf in degree zero is its derived value. The equation on `j` fixes the open
factor through the scheme-theoretic image of the stratum immersion. Lisse flat sheaves
have finite projective constant local models over the finite coefficient ring.
Source: blueprint `sk-lem-sf-flat-model`, complement
(blueprint: sk-lem-sf-flat-model). -/
def sfEtaleClosureGenerators (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (str.immersion i).imageι).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)))

/-- Every finite-Tor bounded constructible pro-etale object in the standing setting has
an actual bounded complex of flat constructible sheaves as representative.
Source: blueprint `sk-lem-sf-flat-model`, first paragraph
(blueprint: sk-lem-sf-flat-model).

Proof plan (the node's steps 1--3): finite type over the standing field makes `X`
Noetherian (lem-weil-pbc-finite-type-over-noetherian), hence qcqs by
lem-weil-pbc-locally-noetherian-quasi-separated. The finite ring is Noetherian.
Use det-pe-finite-tor-comparison-noetherian to descend `K` with its Tor interval to the
etale site. Apply lem-sf-etale-flat-constructible. Apply the exact comparison pullback
termwise (lem-sf-comparison-pullback-exact). It preserves zero terms and the representing
quasi-isomorphism; flatness follows from lem-exc-constant-inverse-image-flat and
constructibility from lem-weil-pbc-finite-ring-constructible-sheaf-origin. The canonical
intrinsic coefficient realization identifies the resulting ordinary module sheaves. -/
theorem proEtaleFlatModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : proEtaleDerivedCategory X A)
    (hbc : (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K))
    (hTor : HasFiniteProEtaleTorAmplitude X A K) :
    ∃ (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
      (a b : ℤ), a ≤ b ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
      (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := proEtaleConstantRing X A) (P.X q)) ∧
      (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A (P.X q)) ∧
      Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  have _ := hl
  have _ := hlp
  have _ := hA
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  let F := ProEtale.finiteCoefficientIntrinsicComparison X A
  obtain ⟨K₀, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin X A).2.2.1 K |>.mpr hbc
  obtain ⟨a, b, ht⟩ := hTor
  obtain ⟨c, d, _, hbound⟩ := K₀.property.2
  have hplus : DerivedCategory.TStructure.t.plus K₀.obj :=
    ⟨c, (DerivedCategory.isGE_iff K₀.obj c).mpr
      (fun q hq ↦ hbound q (.inl hq))⟩
  let Kplus : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨K₀.obj, hplus⟩
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  let R := ProEtale.finiteCoefficientIntrinsicRealization X A
  let ecomp := (Functor.mapDerivedCategoryCompIso C R).app K₀.obj
  have htcomp : HasProEtaleTorAmplitude X A
      (R.mapDerivedCategory.obj (C.mapDerivedCategory.obj K₀.obj)) a b := by
    refine ⟨ht.1, ?_⟩
    intro L Q hL f hf hQ M i hi
    obtain ⟨eL⟩ := hL
    exact ht.2 L Q ⟨eL ≪≫ ecomp.symm ≪≫ e⟩ f hf hQ M i hi
  have htE := (ProEtale.comparison_torAmplitudeIn_iff A X a b ht.1 Kplus).mpr htcomp
  obtain ⟨P, hf, hc, hz, ⟨eP⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      (ULift.{u + 1, u} A) X a b ht.1 K₀.obj K₀.property).mp htE
  refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj P, a, b, ht.1,
    fun q hq ↦ F.map_isZero (hz q hq), ?_, ?_, ?_⟩
  · intro q
    exact ProEtale.intrinsicRealization_flat X A _
      (ProEtale.flat_comparisonUpperStar_obj (hf q))
  · intro q
    exact sf_comparison_constructible X A (P.X q) (hc q)
  · exact ⟨e.symm ≪≫ F.mapDerivedCategory.mapIso eP.symm ≪≫
      F.mapDerivedCategoryFactors.app P⟩

/-- A flat constructible sheaf admits finite projective constant module local models
on a finite stratification. Finiteness and projectivity of the local modules are explicit.
Source: blueprint `sk-lem-sf-flat-model`, first paragraph, stratification clause
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1 and 4): finite type over the standing field is Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Every subset is quasi-compact, using
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal as in step 1. Apply clause 1 of
det-sf-flat-model-generation to the flat constructible sheaf. This supplies an ordered
finite stratification on which the restrictions are locally constant with finite projective
stalks. Refine each trivializing pro-etale covering; its constant module is isomorphic to
a stalk, hence finite projective. Empty members may use the zero projective module.
These module-sheaf isomorphisms give the displayed finite projective local models. -/
theorem proEtaleFlatStratification
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : IsConstructibleProEtaleModuleSheaf X A F)
    (hflat : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F) :
    ∃ str : LocallyClosedStratification X, ∀ i : Fin str.n,
      ∃ (I : Type (u + 1)) (U : I → (str.domain i).ProEt)
        (f : ∀ t : I, U t ⟶ ProEt.mk (𝟙 (str.domain i))),
        Presieve.ofArrows U f ∈ (ProEt.precoverage (str.domain i)).coverings _ ∧
        ∀ t : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          Finite M ∧ Module.Projective (ULift.{u + 1, u} A) M ∧
          Nonempty ((proEtaleConstantModulePullback (str.immersion i) A F).over (U t) ≅
            proEtaleConstantModuleSheafOver (str.domain i) A (U t) M) := by
  have _ := hl
  have _ := hlp
  have _ := hA
  obtain ⟨str, hn, hstr⟩ := hF
  refine ⟨str, fun i ↦ ?_⟩
  let S := str.domain i
  let L := proEtaleConstantModulePullback (str.immersion i) A F
  let R := proEtaleModuleRestriction S A
  have hloc := (localConstancy_iff S A L).mp (hstr i).1
  have hfin := fun Ω (_ : Field Ω) (_ : IsAlgClosed Ω) (x : Spec (.of Ω) ⟶ S) ↦
    (finite_stalk_iff S A L Ω x).mp ((hstr i).2 Ω x)
  have hflat' : ObjectProperty.flat (R.obj L) := by
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (str.immersion i) A F
    exact ObjectProperty.prop_of_iso ObjectProperty.flat e.symm
      (Functor.PreservesFlat.flat_obj (sf_restriction_flat X A F hflat))
  obtain ⟨I, U, f, hf, hm⟩ := sf_projective_models S (ULift.{u + 1, u} A)
    (R.obj L) hloc hfin hflat'
  refine ⟨I, U, f, hf, fun t ↦ ?_⟩
  obtain ⟨M, hM, hp, ⟨e⟩⟩ := hm t
  let a := Functor.whiskerLeft (Over.forget (U t)).op (proEtaleModuleScalarUnit S A)
  have : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U t)) a :=
    (proEtaleConstantRingUnit_over_locallyBijective S A (U t)).1
  have : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U t)) a :=
    (proEtaleConstantRingUnit_over_locallyBijective S A (U t)).2
  have hc := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U t)) (ULift.{u + 1, u} A)
    (((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing S A)).over (U t)) a M
  exact ⟨M, hM, hp, ⟨(ConstantScalarComparison.restrictionFullyFaithful
    ((ProEt.topology S).over (U t)) (ULift.{u + 1, u} A)
      (((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing S A)).over (U t)) a).preimageIso
      (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U t)) (ULift.{u + 1, u} A)
      (((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing S A)).over (U t)) a M))⟩⟩

/-- The Noetherian complement on the etale site, with the recorded finite-value
constructibility and the recorded Tor tests on every module sheaf in degree zero.
Source: blueprint `sk-lem-sf-flat-model`, complement
(blueprint: sk-lem-sf-flat-model).

Proof (node steps 1 and 3--7): use lem-sf-etale-flat-constructible directly, without
comparison descent. Clauses 1--2 of det-sf-flat-model-generation give an ordered
stratification and a finite extension filtration of each flat constructible term.
Finite stalks give finite generation on each locally constant restriction, and inverse
image preserves flatness. The canonical open factor through the scheme-theoretic image
therefore identifies each filtration factor with an sfEtaleClosureGenerators object.
The short exact sequences give distinguished single-object triangles, so finite
induction proves the property for each term, starting with the zero filtration member.
Apply HomotopyCategory.mem_subcategory_of_strictly_bounded to the inverse image of P
under Qh; this implements the bounded stupid-tail induction. Finally transport across
the quotient-comparison and representing isomorphisms. -/
theorem etaleThickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (P : ObjectProperty (Etale.DerivedCategoryModule A X))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : sfEtaleClosureGenerators X A ≤ P)
    (K : Etale.DerivedCategoryModule A X)
    (hbc : Etale.DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K) :
    P K := by
  obtain ⟨a, b, hab, ht⟩ := hTor
  obtain ⟨Pc, hf, hc, hz, ⟨e⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A X a b hab K hbc).1 ht
  have hterm (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (hFc : IsConstructibleEtaleModuleSheaf F) (hFf : ObjectProperty.flat F) :
      P ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    obtain ⟨str, ho, hp⟩ := etale_flatConstructible_orderedStratification X A F hFc hFf
    obtain ⟨M, hM0, ⟨eM⟩, hM⟩ :=
      (etale_flatConstructible_extensionFiltration X A F hFc hFf str ho hp).1
    have hG (k : Fin str.n) :
        P ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
            ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F))) := by
      let L := (Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F
      have hL : IsFiniteLocallyConstantSheaf L := by
        have : IsLocallyConstantSheaf L := (hp k).1
        refine { isFinitelyGenerated_sheafFiber := ?_ }
        intro Ω _ _ x
        have := ((hp k).2 Ω x).1
        rw [ModuleCat.isFinitelyGenerated_iff]
        exact Module.Finite.of_finite
      have hLf : ObjectProperty.flat L :=
        Functor.PreservesFlat.flat_obj (F := Etale.upperStar _ (str.immersion k)) hFf
      have : TopologicalSpace.NoetherianSpace (str.domain k) :=
        (str.immersion k).isEmbedding.isInducing.noetherianSpace
      apply hP
      exact ⟨str, k, (str.immersion k).toImage, inferInstance, L,
        Scheme.Hom.toImage_imageι _, hL, hLf, ⟨Iso.refl _⟩⟩
    have hm : ∀ k : Fin (str.n + 1),
        P ((_root_.DerivedCategory.singleFunctor _ 0).obj (M k)) := by
      intro k
      induction k using Fin.induction with
      | zero =>
        exact P.prop_of_isZero (Functor.map_isZero _ hM0)
      | succ k ih =>
        obtain ⟨f, g, h, hs⟩ := hM k
        exact P.ext_of_isTriangulatedClosed₂ _ hs.singleTriangle_distinguished ih (hG k)
    exact P.prop_of_iso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso eM)
      (hm (Fin.last str.n))
  have : Pc.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ hz q (.inl hq)
  have : Pc.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ hz q (.inr hq)
  have hPc := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (P.inverseImage _root_.DerivedCategory.Qh) Pc a b
    (fun n _ _ ↦ hterm (Pc.X n) (hc n) (hf n))
  exact P.prop_of_iso e (P.prop_of_iso
    ((_root_.DerivedCategory.quotientCompQhIso _).app Pc) hPc)

/-- The Noetherian complement on the pro-etale site, in its property formulation.
Source: blueprint `sk-lem-sf-flat-model`, complement
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1--7): finite rings are Noetherian; `X` is qcqs and all its strata
are quasi-compact by step 1. Descend through det-pe-finite-tor-comparison-noetherian,
resolve by lem-sf-etale-flat-constructible and pull back using
lem-sf-comparison-pullback-exact, lem-exc-constant-inverse-image-flat and
lem-weil-pbc-finite-ring-constructible-sheaf-origin. The result is a bounded flat
constructible model. Clauses 1--2 of det-sf-flat-model-generation give a finite ordered
stratification and an open--closed filtration of each term by locally closed extensions
of lisse flat sheaves. Factor the quasi-compact stratum immersions through their
scheme-theoretic images using lemma-nagata-immersion-open-in-scheme-image. By
lem-weil-pbc-proetale-ringed-open-closed closed direct image is exact; the complement is
quasi-compact by Noetherianity. By lem-weil-pbc-exact-functor-derived-functor it agrees
with its right derived functor on degree-zero objects. Hence the factors are exactly
the displayed closure generators. Convert sheaf short exact sequences to triangles by
lem-weil-pbc-complex-ses-triangle and induct over the finite filtration. For the model,
the degreewise split sequences of stupid tails give triangles with third term
`P^q[-q]`; start at the zero tail above the last degree and induct downwards. Shift,
extension and isomorphism stability give `P K`. Retract stability gives the thick
formulation; the empty scheme and zero complex use only its zero-object base case. -/
theorem proEtaleThickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (P : ObjectProperty (proEtaleDerivedCategory X A))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : sfProEtaleClosureGenerators X A ≤ P)
    (K : proEtaleDerivedCategory X A)
    (hbc : (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K))
    (hTor : HasFiniteProEtaleTorAmplitude X A K) : P K := by
  let B := ULift.{u + 1, u} A
  let F := ProEtale.finiteCoefficientIntrinsicComparison X A
  obtain ⟨K₀, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin X A).2.2.1 K |>.mpr hbc
  obtain ⟨a, b, ht⟩ := hTor
  obtain ⟨c, d, _, hbound⟩ := K₀.property.2
  have hplus : DerivedCategory.TStructure.t.plus K₀.obj :=
    ⟨c, (DerivedCategory.isGE_iff K₀.obj c).mpr
      (fun q hq ↦ hbound q (.inl hq))⟩
  let Kplus : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) := ⟨K₀.obj, hplus⟩
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X
  let R := ProEtale.finiteCoefficientIntrinsicRealization X A
  let ecomp := (Functor.mapDerivedCategoryCompIso C R).app K₀.obj
  have htcomp : HasProEtaleTorAmplitude X A
      (R.mapDerivedCategory.obj (C.mapDerivedCategory.obj K₀.obj)) a b := by
    refine ⟨ht.1, ?_⟩
    intro L Q hL f hf hQ M i hi
    obtain ⟨eL⟩ := hL
    exact ht.2 L Q ⟨eL ≪≫ ecomp.symm ≪≫ e⟩ f hf hQ M i hi
  have htE := (ProEtale.comparison_torAmplitudeIn_iff A X a b ht.1 Kplus).mpr htcomp
  have hgenerators : sfEtaleClosureGenerators X B ≤ P.inverseImage F.mapDerivedCategory := by
    rintro G ⟨str, i, j, hj, L, heq, hL, hLf, ⟨eG⟩⟩
    let : IsOpenImmersion j := hj
    let Cs := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) (str.domain i)
    let Es := sfIntrinsicModuleEquivalence (str.domain i) A
    let Lp := Es.functor.obj (Cs.obj L)
    have hLp : IsLisseProEtaleFixedModuleSheaf (str.domain i) B
        (Es.inverse.obj Lp) := sf_lisse_of_iso _ _ (Es.unitIso.app (Cs.obj L))
      ((proEtale_lisse_origin (str.domain i) B).1 L hL)
    have hLpf : SheafOfModules.IsFlatOnSite (J := ProEt.topology (str.domain i))
        (R := proEtaleConstantRing (str.domain i) A) Lp :=
      ProEtale.intrinsicRealization_flat _ A _
        (ProEtale.flat_comparisonUpperStar_obj hLf)
    let g := (str.immersion i).imageι
    have : IsIso (ProEtale.lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} B)) :=
      ProEtale.isIso_lowerStarComparisonUpperStarBaseChange g _
    let es := R.mapIso
      ((asIso (ProEtale.lowerStarComparisonUpperStarBaseChange g
        (ModuleCat.{u + 1} B))).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj L) ≪≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} B) g).mapIso
          ((ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} B) j).app L) ≪≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} B) g).mapIso
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapIso
            (Es.unitIso.app (Cs.obj L))))
    apply hP
    refine ⟨str, i, j, hj, Lp, heq, hLp, hLpf, ?_⟩
    exact ⟨F.mapDerivedCategory.mapIso eG ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso es⟩
  let : (P.inverseImage F.mapDerivedCategory).IsStableUnderRetracts :=
    ⟨fun r h ↦ P.prop_of_retract (r.map F.mapDerivedCategory) h⟩
  have hk := etaleThickGeneration X B (P.inverseImage F.mapDerivedCategory)
    hgenerators K₀.obj K₀.property ⟨a, b, ht.1, htE⟩
  exact P.prop_of_iso e hk


/-- In the standing setting the pro-etale finite-Tor constructible category equals
its thick generator envelope, including reverse containment of the generators.
Source: blueprint `sk-lem-sf-flat-model`, first paragraph, generation clause
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1--7): the model, finite sheaf filtration and stupid-tail
triangles in steps 1--6 prove containment in the thick envelope, equivalently step 7
with the envelope as the property. Clause 3 of det-sf-flat-model-generation supplies
reverse containment and stability under direct summands: each lisse flat stratum sheaf
extended by zero is constructible of finite Tor amplitude, and this object class is
closed under shifts, extensions, isomorphisms and retracts. The scheme-theoretic closure
factorization and exact closed pushforward identify these extensions with our canonical
closure generators. These two containments give equality of object properties. -/
theorem proEtaleThickGeneration_eq
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (fun K : proEtaleDerivedCategory X A ↦
      ((∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
        ((_root_.DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor
            (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
      HasFiniteProEtaleTorAmplitude X A K) =
      (sfProEtaleClosureGenerators X A).triangEnvelope := by
  have _ := hl
  have _ := hlp
  have _ := hA
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  let B := ULift.{u + 1, u} A
  let F := ProEtale.finiteCoefficientIntrinsicComparison X A
  let E := Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) X
  let H := E.ι ⋙ F.mapDerivedCategory
  have : H.Full := sf_comparison_ctf_full X A
  have : H.Faithful := sf_comparison_ctf_faithful X A
  let Q := H.essImage
  have : Q.IsTriangulated := inferInstance
  have : Q.IsStableUnderRetracts := by
    constructor
    intro Y Z r hZ
    obtain ⟨K, ⟨e⟩⟩ := hZ
    let s : Retract Y (H.obj K) := r.trans (Retract.ofIso e.symm)
    let p : K ⟶ K := H.preimage (s.r ≫ s.i)
    have hp : p ≫ p = p := by
      apply H.map_injective
      simp only [Functor.map_comp, p, Functor.map_preimage]
      simp only [Category.assoc, s.retract_assoc]
    have hK := (flatModel_etale_ctf_iff X B K.obj).mpr K.property
    obtain ⟨a, b, hab, hz⟩ := hK.2.1
    have : DerivedCategory.IsGE K.obj a :=
      (DerivedCategory.isGE_iff _ a).mpr (fun q hq ↦ hz q (.inl hq))
    have : DerivedCategory.IsLE K.obj b :=
      (DerivedCategory.isLE_iff _ b).mpr (fun q hq ↦ hz q (.inr hq))
    have : DerivedCategory.IsLE K.obj (a + ((b - a).toNat : ℕ)) :=
      DerivedCategory.TStructure.t.isLE_of_le K.obj b _ (by omega)
    obtain ⟨L, i, π, hiπ, hπi⟩ :=
      DerivedCategory.TStructure.t.isSplit_of_isGE_of_isLE (b - a).toNat K.obj a p.hom
        (congrArg InducedCategory.Hom.hom hp)
    have hL : E L := E.prop_of_retract ⟨i, π, hiπ⟩ K.property
    have hmap : F.mapDerivedCategory.map (π ≫ i) = s.r ≫ s.i := by
      rw [hπi]
      exact H.map_preimage _
    refine ⟨⟨L, hL⟩, ⟨⟨F.mapDerivedCategory.map i ≫ s.r,
      s.i ≫ F.mapDerivedCategory.map π, ?_, ?_⟩⟩⟩
    · dsimp only [H, Functor.comp_obj, ObjectProperty.ι_obj]
      simp only [Category.assoc]
      rw [← Category.assoc s.r s.i _, ← hmap]
      simp only [← Functor.map_comp, ← Category.assoc, hiπ, Category.id_comp]
      exact F.mapDerivedCategory.map_id L
    · change (s.i ≫ F.mapDerivedCategory.map π) ≫
        F.mapDerivedCategory.map i ≫ s.r = 𝟙 _
      rw [Category.assoc, ← Functor.map_comp_assoc, hmap]
      simp [← Category.assoc]
  have hQ (K : proEtaleDerivedCategory X A) (hK : Q K) :
      ((∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      HasFiniteProEtaleTorAmplitude X A K := by
    obtain ⟨L, ⟨e⟩⟩ := hK
    have hL := (flatModel_etale_ctf_iff X B L.obj).mpr L.property
    have hbc := (finiteRing_constructibleDerived_origin X A).2.2.1 K |>.mp
      ⟨⟨L.obj, hL.1, hL.2.1⟩, ⟨e⟩⟩
    obtain ⟨a, b, hab, ht⟩ := hL.2.2
    obtain ⟨c, d, _, hz⟩ := hL.2.1
    let Lplus : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
      ⟨L.obj, c, (DerivedCategory.isGE_iff _ c).mpr (fun q hq ↦ hz q (.inl hq))⟩
    let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X
    let R := ProEtale.finiteCoefficientIntrinsicRealization X A
    have ht' := (ProEtale.comparison_torAmplitudeIn_iff A X a b hab Lplus).mp ht
    refine ⟨hbc, a, b, ht'.1, ?_⟩
    intro N P hN f hf hP M q hq
    obtain ⟨eN⟩ := hN
    exact ht'.2 N P
      ⟨eN ≪≫ e.symm ≪≫ (Functor.mapDerivedCategoryCompIso C R).app L.obj⟩
      f hf hP M q hq
  have hgen : sfProEtaleClosureGenerators X A ≤ Q := by
    rintro K ⟨str, k, j, hj, Lp, heq, hLp, hLpf, ⟨eK⟩⟩
    let : IsOpenImmersion j := hj
    let S := str.domain k
    let Es := sfIntrinsicModuleEquivalence S A
    let Cs := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) S
    obtain ⟨L, hL, ⟨eL⟩⟩ := (proEtale_lisse_origin S B).2 (Es.inverse.obj Lp) hLp
    have hfixed : ObjectProperty.flat (Es.inverse.obj Lp) :=
      (intrinsic_flat_iff S A _).mpr
        (site_flat_of_iso A (Es.counitIso.app Lp) hLpf)
    have hLf : ObjectProperty.flat L := sf_comparison_reflects_flat S B L
      (ObjectProperty.prop_of_iso ObjectProperty.flat eL.symm hfixed)
    let G := (Etale.lowerStar (ModuleCat.{u + 1} B) (str.immersion k).imageι).obj
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj L)
    have hG : E ((_root_.DerivedCategory.singleFunctor _ 0).obj G) := by
      have hE := etale_flatConstructible_thickGeneration X B
      apply (flatModel_etale_ctf_iff X B _).mp
      apply (congrFun hE ((_root_.DerivedCategory.singleFunctor _ 0).obj G)).mpr
      apply ObjectProperty.le_triangEnvelope
      have : TopologicalSpace.NoetherianSpace S :=
        (str.immersion k).isEmbedding.isInducing.noetherianSpace
      have hjcan : j = (str.immersion k).toImage := by
        apply (cancel_mono (str.immersion k).imageι).mp
        exact heq.trans (Scheme.Hom.toImage_imageι _).symm
      subst hjcan
      refine ⟨S, str.immersion k, str.isImmersion k, L, ?_, ⟨Iso.refl _⟩⟩
      refine ⟨hL.toIsLocallyConstantSheaf, fun Ω _ _ x ↦ ?_⟩
      let M := ((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B)).obj L
      have : Module.Finite B M := (ModuleCat.isFinitelyGenerated_iff M).mp
        (hL.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω x)
      have : Finite M := Module.finite_of_finite B
      have : Module.Flat B M := (ModuleCat.flat_iff_flat M).mp
        (ObjectProperty.prop_of_iso ObjectProperty.flat
          (((pointSmallEtale x).uliftSheafFiberIso.{u + 1}
            (ModuleCat.{u + 1} B)).app L)
          ((Etale.flat_iff_forall_flat_sheafFiber_obj L).mp hLf x))
      have : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
      exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
    let g := (str.immersion k).imageι
    have : IsIso (ProEtale.lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} B)) :=
      ProEtale.isIso_lowerStarComparisonUpperStarBaseChange g _
    let es := (ProEtale.finiteCoefficientIntrinsicRealization X A).mapIso
      ((asIso (ProEtale.lowerStarComparisonUpperStarBaseChange g
        (ModuleCat.{u + 1} B))).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj L) ≪≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} B) g).mapIso
          ((ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} B) j).app L) ≪≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} B) g).mapIso
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapIso eL))
    exact ⟨⟨_, hG⟩, ⟨(F.mapDerivedCategorySingleFunctor 0).app G ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso es ≪≫ eK.symm⟩⟩
  have hnonempty : (sfProEtaleClosureGenerators X A).Nonempty := by
    let str := identityStratification X
    let k : Fin str.n := ⟨0, by change 0 < 1; decide⟩
    let a := str.immersion k
    have : IsImmersion a := str.isImmersion k
    have : TopologicalSpace.NoetherianSpace (str.domain k) :=
      a.isEmbedding.isInducing.noetherianSpace
    let j := a.toImage
    let : Zero (Sheaf (str.domain k).smallEtaleTopology (ModuleCat.{u + 1} B)) :=
      HasZeroObject.zero' _
    let L : Sheaf (str.domain k).smallEtaleTopology (ModuleCat.{u + 1} B) := 0
    have hL : IsFiniteLocallyConstantSheaf L :=
      IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _)
    let Es := sfIntrinsicModuleEquivalence (str.domain k) A
    let Cs := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) (str.domain k)
    let Lp := Es.functor.obj (Cs.obj L)
    have hlp : IsLisseProEtaleFixedModuleSheaf (str.domain k) B
        (Es.inverse.obj Lp) := sf_lisse_of_iso _ _ (Es.unitIso.app (Cs.obj L))
      ((proEtale_lisse_origin _ B).1 L hL)
    have hlf : SheafOfModules.IsFlatOnSite (J := ProEt.topology (str.domain k))
        (R := proEtaleConstantRing (str.domain k) A) Lp :=
      ProEtale.intrinsicRealization_flat _ A _
        (ProEtale.flat_comparisonUpperStar_obj
          (ObjectProperty.flat_of_isZero (isZero_zero _)))
    exact ⟨_, str, k, j, inferInstance, Lp, Scheme.Hom.toImage_imageι _, hlp, hlf,
      ⟨Iso.refl _⟩⟩
  apply le_antisymm
  · intro K hK
    exact proEtaleThickGeneration X A
      (sfProEtaleClosureGenerators X A).triangEnvelope
      (sfProEtaleClosureGenerators X A).le_triangEnvelope K hK.1 hK.2
  · intro K hK
    exact hQ K ((ObjectProperty.triangEnvelope_le_iff (P := sfProEtaleClosureGenerators X A)
      (Q := Q)).mpr hgen K hK)

end AlgebraicGeometry
