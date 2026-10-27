/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Constructible
import all Sheaf.Paper.FiniteConstantStratifiedZariskiLocality
import all Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Order.CompletePartialOrder

/-!
# Quasi-compact open extension preserves constant-model constructibility and Tor intervals

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
`det-sf-comp-coherence-refinement.proof.md`, (2), bounded constructible generator input;
Stacks Tags 005H, 09YD, 01J3, 03DJ, 09BN, 09AH
(blueprint: lem-sfb-qc-open-extension-ctf).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] upperStar upperStarComp upperStarFromPoint
  openImmersionLowerShriek openImmersionLowerShriekUpperStarAdjunction

private theorem model_zero {X : Scheme.{u}} (M : supportModules Λ X)
    (h : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  have (Y : Scheme.{u}) : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint Y) := by
    unfold upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).leftAdjoint_preservesColimits
  have (Y : Scheme.{u}) : ((upperStarFromPoint Y).mapMod Λ).Additive := by
    have : PreservesBinaryBiproducts ((upperStarFromPoint Y).mapMod Λ) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact ⟨0, Mod.IsFinitelyPresented.of_isZero (isZero_zero _),
    ⟨((upperStar Λ _).map_isZero h).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))⟩⟩

private theorem constructible_affine {X : Scheme.{u}} (M : supportModules Λ X)
    (hM : IsConstantModelConstructible Λ X M) (V : X.Opens) (hV : IsAffineOpen V) :
    IsFiniteConstantStratified Λ V.toScheme ((upperStar Λ V.ι).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM
  split_ifs at hM with h
  · exact stratified_pullback Λ V.ι M hM
  · exact hM V hV

private theorem constructible_qc_open {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace U] [QuasiSeparatedSpace U]
    (M : supportModules Λ X) (hM : IsConstantModelConstructible Λ X M) :
    IsFiniteConstantStratified Λ U ((upperStar Λ j).obj M) := by
  apply stratified_of_affine_neighborhoods Λ
  intro x
  obtain ⟨V, hV, hxV, _⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens)
      (show x ∈ (⊤ : U.Opens) from trivial)
  refine ⟨V, hV, hxV, ?_⟩
  have h := stratified_pullback Λ (j.isoImage V).hom _
    (constructible_affine Λ M hM (j ''ᵁ V) (hV.image_of_isOpenImmersion j))
  exact stratified_of_iso Λ
    ((squarePullbackIso Λ (j.isoImage V).hom (Scheme.Opens.ι V) (j ''ᵁ V).ι j
      (j.isoImage_hom_ι V)).app M) h

private theorem openClosed_property {Z U X : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (S : Scheme.Stratification U) (T : Scheme.Stratification Z)
    (P : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hS : ∀ a, P (S.domain a) (S.immersion a ≫ j))
    (hT : ∀ a, P (T.domain a) (T.immersion a ≫ i)) :
    ∀ k, P ((Scheme.Stratification.openClosed j i hij S T).domain k)
      ((Scheme.Stratification.openClosed j i hij S T).immersion k) := by
  intro k
  change P (Sum.elim S.domain T.domain (finSumFinEquiv.symm k))
    (Sum.rec (motive := fun s ↦ Sum.elim S.domain T.domain s ⟶ X)
      (fun a ↦ S.immersion a ≫ j) (fun a ↦ T.immersion a ≫ i)
      (finSumFinEquiv.symm k))
  generalize finSumFinEquiv.symm k = a
  rcases a with a | a
  · exact hS a
  · exact hT a

private theorem stratified_open_closed {Z U X : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : supportModules Λ X)
    (hU : IsFiniteConstantStratified Λ U ((upperStar Λ j).obj M))
    (hZ : IsZero ((upperStar Λ i).obj M)) : IsFiniteConstantStratified Λ X M := by
  obtain ⟨S, hS⟩ := hU
  let T := Scheme.Stratification.trivial Z
  refine ⟨Scheme.Stratification.openClosed j i hij S T, ?_⟩
  apply openClosed_property j i hij S T
    (fun Y f ↦ HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M))
  · intro a
    exact model_of_iso Λ ((upperStarComp Λ (S.immersion a) j).app M).symm (hS a)
  · intro a
    exact model_of_iso Λ ((upperStarComp Λ (T.immersion a) i).app M).symm
      (model_zero Λ _ ((upperStar Λ (T.immersion a)).map_isZero hZ))

private theorem extension_constructible {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (M : supportModules Λ U) (hM : IsConstantModelConstructible Λ U M) :
    IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M) := by
  classical
  have := openUnit Λ j
  let N := (openImmersionLowerShriek Λ j).obj M
  have haff (V : X.Opens) (hV : IsAffineOpen V) :
      IsFiniteConstantStratified Λ V.toScheme ((upperStar Λ V.ι).obj N) := by
    let D := j ⁻¹ᵁ V
    let d : D.toScheme ⟶ V.toScheme := j ∣_ V
    let : IsAffine V.toScheme := hV
    let : CompactSpace D.toScheme :=
      isCompact_iff_compactSpace.mp (j.isCompact_preimage hV.isCompact)
    let : QuasiSeparatedSpace D.toScheme := quasiSeparatedSpace_of_quasiSeparated d
    let C : TopologicalSpace.Closeds V.toScheme :=
      ⟨(Set.range d.base)ᶜ, d.isOpenEmbedding.isOpen_range.isClosed_compl⟩
    let I := Scheme.IdealSheafData.vanishingIdeal C
    have hC : Set.range I.subschemeι.base = (Set.range d.base)ᶜ := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    apply stratified_open_closed Λ d I.subschemeι hC
    · have h := constructible_qc_open Λ D.ι M hM
      have e : (upperStar Λ d).obj ((upperStar Λ V.ι).obj N) ≅
          (upperStar Λ D.ι).obj M :=
        ((squarePullbackIso Λ D.ι d j V.ι
          (morphismRestrict_ι j V).symm).app N).symm ≪≫
        (upperStar Λ D.ι).mapIso
          (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)).symm
      exact stratified_of_iso Λ e.symm h
    · have hd : Disjoint (Set.range j.base) (Set.range (I.subschemeι ≫ V.ι).base) := by
        rw [Set.disjoint_left]
        rintro _ ⟨u, hu⟩ ⟨z, rfl⟩
        have hz : I.subschemeι z ∈ (Set.range d.base)ᶜ := hC ▸ Set.mem_range_self z
        apply hz
        refine ⟨⟨u, ?_⟩, ?_⟩
        · change j u ∈ V
          rw [hu]
          exact (I.subschemeι z).property
        · apply Subtype.ext
          exact (morphismRestrict_base_coe j V _).trans hu
      exact (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j
        (I.subschemeι ≫ V.ι) hd M).of_iso
          ((upperStarComp Λ I.subschemeι V.ι).app N).symm
  unfold IsConstantModelConstructible
  split_ifs with hX
  · exact (finiteConstantStratified_zariski_locality Λ X N).2.2 hX.1 hX.2 |>.2 haff
  · exact haff

private theorem constructible_iso {X : Scheme.{u}} {M N : supportModules Λ X}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · exact stratified_of_iso Λ e hM
  · intro V hV
    exact stratified_of_iso Λ ((upperStar Λ V.ι).mapIso e) (hM V hV)

private theorem extension_tor {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (supportModules Λ U)) (a b : ℤ)
    (hK : DerivedCategory.torAmplitudeIn _ a b K) :
    DerivedCategory.torAmplitudeIn _ a b
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) := by
  let C : TopologicalSpace.Closeds X :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hC : Set.range I.subschemeι.base = (Set.range j.base)ᶜ := by
    simp only [I, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let := closedSupport_lowerStarExact Λ I.subschemeι j hC
  have hproj := (openClosedSupportProjectionFormula Λ I.subschemeι j hC).2
  intro F
  let F₀ := (DerivedCategory.singleFunctor (supportModules Λ X) 0).obj F
  have := hproj K F₀
  have hp : DerivedCategory.homologyConcentratedIn a b
      (((derivedTensor Λ U).obj K).obj ((supportPullback Λ j).mapDerivedCategory.obj F₀)) :=
    (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      ((CategoryTheory.MonoidalCategory.tensorLeft K).mapIso
        (((supportPullback Λ j).mapDerivedCategorySingleFunctor 0).app F)).symm
      (hK ((supportPullback Λ j).obj F))
  exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
    (asIso (openSupportProjection Λ j K F₀))
    ((openImmersionLowerShriek Λ j).homologyConcentratedIn_mapDerivedCategory_obj hp)

/-- Quasi-compact open extension preserves the finite constant scalar-model notion,
commutes naturally with cohomology, preserves each cohomological and Tor interval,
and hence sends Dctf into Dctf. All derived categories are ordinary unbounded categories
of modules over the pulled-back condensed coefficient ring.

Source: blueprint main-20261015, `det-sf-comp-coherence-refinement.proof.md` (2),
bounded constructible generator input; Stacks Tags 005H, 09YD, 01J3, 03DJ, 09BN, 09AH
(blueprint: lem-sfb-qc-open-extension-ctf).

Proof:
1. Restrict finite constant stratifications by the proved pullback helpers of
finiteConstantStratified_zariski_locality. For a qcqs open W of an arbitrary scheme,
affine neighborhoods of W identify with affine opens of the ambient scheme; transport
their models along these identifications and assemble them by affine locality.
2. For each affine open V of X, D = j⁻¹(V) is compact by quasi-compactness of j and
quasi-separated as an open of the affine V. The open adjunction unit identifies the
restriction of j_!M to D with M|D, with its finite constant stratification from step 1.
The vanishing-ideal subscheme of V minus D is an actual closed complement. Its
restriction of j_!M is zero by disjoint-support vanishing and pullback composition.
3. Scheme.Stratification.openClosed combines the old strata with the trivial
stratification of that complement. On the old strata retain the given scalar models;
on the complement use zero, with its rank-zero finite presentation and identity cover.
This proves the affine-local condition; affine locality supplies the global finite
stratification when X is qcqs. Empty opens, complements and zero modules are allowed.
4. The exact-functor homology isomorphism gives natural commutation with every H^n.
Exactness also preserves each cohomological interval and boundedness. Applying the
module assertion to each cohomology module, then transporting along that isomorphism,
proves preservation of bounded constructibility.
5. For any degree-zero module F on X, exact support pullback identifies its derived
pullback with the degree-zero module j^*F. The unbounded support projection formula
identifies (JK) tensor^L F with J(K tensor^L j^*F). A Tor interval [a,b] for K gives
that cohomological interval inside J, and step 4 preserves it. Quantifying over F gives
the same Tor interval for JK; combine it with bounded constructibility for Dctf.
No Noetherian, field, characteristic or global qcqs hypothesis is used. -/
theorem qcOpenExtension_constantModelConstructible_finiteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
      IsConstantModelConstructible Λ U M →
        IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M)) ∧
    (∀ n : ℤ, Nonempty
      ((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ n ≅
        DerivedCategory.homologyFunctor _ n ⋙ openImmersionLowerShriek Λ j)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
        (a b : ℤ),
      DerivedCategory.homologyConcentratedIn a b K →
        DerivedCategory.homologyConcentratedIn a b
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
        (a b : ℤ),
      DerivedCategory.torAmplitudeIn _ a b K →
        DerivedCategory.torAmplitudeIn _ a b
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
      (constantModelBoundedConstructible Λ U ⊓ DerivedCategory.finiteTorAmplitude _) K →
        (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) := by
  have hcons := extension_constructible Λ j
  have htor := extension_tor Λ j
  refine ⟨hcons, fun n ↦
      ⟨((openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).symm⟩,
    fun K a b hK ↦
      (openImmersionLowerShriek Λ j).homologyConcentratedIn_mapDerivedCategory_obj hK,
    htor, ?_⟩
  intro K hK
  refine ⟨⟨(openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj hK.1.1,
    fun n ↦ ?_⟩, ?_⟩
  · exact constructible_iso Λ
      (((openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app K)
      (hcons _ (hK.1.2 n))
  · obtain ⟨a, b, hab⟩ := hK.2
    exact ⟨a, b, htor K a b hab⟩

end AlgebraicGeometry.ProEtale.CondensedRing
