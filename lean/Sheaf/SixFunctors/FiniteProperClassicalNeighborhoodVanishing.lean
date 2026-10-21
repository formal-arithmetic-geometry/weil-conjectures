/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap

/-!
# Classical cohomology on proper weakly contractible neighborhoods

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-ctf-finite-proper-localizing.proof.md`, "Etale statements" and "Transfer";
Stacks Project, Tag 095U
(blueprint: lem-sfb-finite-proper-classical-neighborhood-vanishing).

We use the existing fixed-coefficient module-sheaf presentation of ordinary modules over
constant coefficients. The exact realization `finiteCoefficientRealization` identifies it
with the coefficient-ring-sheaf category of `def-weil-pbc-proetale-modules`.
Both derived functors below are total unbounded K-injective right derived functors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem sectionOfCover
    {X : Scheme.{u}} {W V : X.ProEt} (p : V ⟶ W)
    (hp : Sieve.generate (Presieve.singleton p) ∈ Scheme.ProEt.topology X W)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    ∃ s : W ⟶ V, s ≫ p = 𝟙 W := by
  let J := Scheme.ProEt.topology X
  have hepi : Epi (J.uliftYoneda.{u + 1}.map p) := by
    constructor
    intro Z a b hab
    apply J.uliftYonedaEquiv.injective
    have heq : Z.obj.map p.op (J.uliftYonedaEquiv a) =
        Z.obj.map p.op (J.uliftYonedaEquiv b) := by
      rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality, hab]
    apply Sheaf.isSeparated Z W _ hp
    rintro T f ⟨_, g, _, ⟨⟩, rfl⟩
    simpa only [CategoryTheory.op_comp, Functor.map_comp, types_comp_apply] using
      congrArg (Z.obj.map g.op) heq
  obtain ⟨s, hs⟩ := hW (J.uliftYoneda.{u + 1}.map p)
    ((Sheaf.isLocallySurjective_iff_epi _).mpr hepi) ⟨𝟙 W⟩
  exact ⟨s.down, congrArg ULift.down hs⟩

private theorem weaklyContractible_terminal
    {X : Scheme.{u}} (V : X.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V) :
    (Scheme.ProEt.topology V.left).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 V.left)) := by
  classical
  obtain ⟨S, iS, iA, hind, hff, hw⟩ := exists_isWContractibleRing Γ(V.left, ⊤)
  let φ : Γ(V.left, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap _ _)
  have : WeaklyEtale (Spec.map φ) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 hind)
  have : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 hff)).2
  let p : Spec (.of S) ⟶ V.left := Spec.map φ ≫ V.left.isoSpec.inv
  have : WeaklyEtale p := inferInstance
  have : Surjective p := inferInstance
  let W : X.ProEt := Scheme.ProEt.mk (p ≫ V.hom)
  let a : W ⟶ V := MorphismProperty.Over.homMk p rfl
  have hcov : Sieve.generate (Presieve.singleton a) ∈ Scheme.ProEt.topology X V := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := p)
      inferInstance
  obtain ⟨s, hs⟩ := sectionOfCover a hcov hV
  let W' : V.left.ProEt := Scheme.ProEt.mk p
  let T : V.left.ProEt := Scheme.ProEt.mk (𝟙 V.left)
  let a' : W' ⟶ T := MorphismProperty.Over.homMk p (Category.comp_id _)
  let s' : T ⟶ W' := MorphismProperty.Over.homMk s.left (by
    exact congrArg (fun f ↦ f.left) hs)
  have hsplit : s' ≫ a' = 𝟙 T := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ f.left) hs
  have hW : (Scheme.ProEt.topology V.left).IsWeaklyContractible.{u + 1} W' :=
    Scheme.ProEt.isWeaklyContractible_of_iso (R := CommRingCat.of S) (Iso.refl _)
  intro F G f hf x
  obtain ⟨y, hy⟩ := hW f hf (G.obj.map a'.op x)
  refine ⟨F.obj.map s'.op y, ?_⟩
  rw [NatTrans.naturality_apply, hy]
  have heq := congrArg (fun k : T ⟶ T ↦ G.obj.map k.op x) hsplit
  rw [CategoryTheory.op_comp, Functor.map_comp_apply, CategoryTheory.op_id] at heq
  exact heq.trans (G.obj.map_id_apply _ _)

private theorem exact_sections
    (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}} (V : X.ProEt)
    (hV : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V) :
    PreservesFiniteColimits (sectionsFunctor (ModuleCat.{u + 1} A) V) := by
  let ev := sectionsFunctor (ModuleCat.{u + 1} A) V
  have : ev.PreservesEpimorphisms := by
    constructor
    intro F G f hf
    have h : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' _ _).2 hf
    exact (ModuleCat.epi_iff_surjective (ev.map f)).2
      (hV ((sheafCompose _ (forget _)).map f)
        ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 h))
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  exact Functor.preservesFiniteColimits_of_preservesHomology ev

private noncomputable def lowerStarSectionsIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    lowerStar (ModuleCat.{u + 1} A) f ⋙ globalSectionsFunctor (ModuleCat.{u + 1} A) Y ≅
      globalSectionsFunctor (ModuleCat.{u + 1} A) X := by
  let B := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let hX := MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X
  let hY := MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) Y
  let e := hX.uniqueUpToIso (hY.isTerminalObj B _)
  exact NatIso.ofComponents (fun H ↦ H.obj.mapIso e.op)
    (fun φ ↦ (φ.hom.naturality e.hom.op).symm)

private theorem globalSections_vanishing_of_directImage
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 Y)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (q : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((globalSectionsFunctor (ModuleCat.{u + 1} A) X).rightDerivedFunctor.obj K)) := by
  let G := globalSectionsFunctor (ModuleCat.{u + 1} A) Y
  have : PreservesFiniteColimits G := exact_sections A _ hY
  let R := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K
  let e := (Functor.rightDerivedFunctorCompIso' _ _ (lowerStarSectionsIso A f)).app K
  exact (G.map_isZero h).of_iso
    ((G.mapDerivedCategoryHomologyFunctorIso q).app R ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        (G.rightDerivedFunctorIsoMapDerivedCategory.app R).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e).symm

/-- Every classical module sheaf on the proper neighborhood itself has zero higher
proper direct image and derived global sections in degrees greater than `2 * e`.
Classicality is the essential-image condition for the recorded comparison inverse image.

Source: blueprint main-20261015, `sk-prop-ctf-finite-proper-localizing.proof.md`,
"Etale statements" and "Transfer"; Stacks Project, Tags 095U, 03FD, 0946, 0990 and 090M
(blueprint: lem-sfb-finite-proper-classical-neighborhood-vanishing).

Proof:
1. Proper base change makes the projection proper. The universal fibre bound applies
   to its fibres with the same integer `e`.
2. Choose the etale model supplied by classicality. The cardinality of the finite
   coefficient ring kills every local section, including for the zero ring. Apply the
   proper torsion bound after forgetting coefficients; the forgetful comparison and
   faithfulness recover the etale module bound.
3. Bounded-below/unbounded derived compatibility identifies the etale bound with the
   homology of the total derived direct image. The canonical comparison mate is
   invertible on the etale sheaf in degree zero. Exact comparison inverse image
   commutes with homology and transfers this bound to `H`.
4. Choose a faithfully flat ind-etale w-contractible affine cover of `V`. Its map
   to `V` is a covering epimorphism of representable sheaves on `Y_proet`. Weak
   contractibility of `V` supplies a section. Over `V`, the cover is weakly
   contractible by the existing affine w-contractible evaluation theorem. Restrict
   a section to the cover, lift it there, and restrict along the splitting. Thus
   the final object of `V_proet` is weakly contractible and module sections are exact.
5. Base change carries the terminal object to a terminal object, giving
   `h_*` followed by sections on `V` equal to sections on `Z`. The direct image
   preserves K-injective complexes, so the composition theorem identifies the total
   derived functors. Exact sections commute with homology, giving the second bound. -/
theorem finiteProper_classical_neighborhood_vanishing
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (_hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (H : Sheaf (Scheme.ProEt.topology (pullback f V.hom)) (ModuleCat.{u + 1} A))
    (_hH : ∃ F : Sheaf (pullback f V.hom).smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f V.hom)).obj F ≅ H))
    (q : ℤ) (_hq : 2 * (e : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd f V.hom)).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) ∧
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj
      ((globalSectionsFunctor (ModuleCat.{u + 1} A) (pullback f V.hom)).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  classical
  obtain ⟨F, ⟨i⟩⟩ := _hH
  let g : pullback f V.hom ⟶ V.left := pullback.snd f V.hom
  have : IsProper g := inferInstance
  let UZ := sheafCompose (pullback f V.hom).smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let UV := sheafCompose V.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have ht : (UZ.obj F).IsTorsion := by
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun W x ↦ ?_
    let := Fintype.ofFinite A
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨Fintype.card A, Fintype.card_pos, ?_⟩
    let y : F.obj.obj W := x
    change Fintype.card A • y = 0
    rw [← one_smul A y, ← smul_assoc, card_nsmul_eq_zero, zero_smul]
  have hab := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    g e (_hbound V.left V.hom) (UZ.obj F)
    ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr ht) q _hq
  obtain ⟨ef⟩ := Etale.nonempty_higherDirectImage_forget_iso A g q F
  have : UV.Additive := ⟨rfl⟩
  have hm : IsZero (Etale.higherDirectImage A g q F) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply UV.map_injective
    rw [UV.map_id, UV.map_zero]
    exact (hab.of_iso ef).eq_of_src _ _
  let K : DerivedCategory
      (Sheaf (pullback f V.hom).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    (DerivedCategory.singleFunctor _ 0).obj F
  let Re : DerivedCategory
      (Sheaf (pullback f V.hom).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let Rp : DerivedCategory
      (Sheaf (Scheme.ProEt.topology (pullback f V.hom)) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology V.left) (ModuleCat.{u + 1} A)) :=
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let cZ := comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f V.hom)
  let cV := comparisonUpperStar (ModuleCat.{u + 1} A) V.left
  have he : IsZero ((DerivedCategory.homologyFunctor _ q).obj (Re.obj K)) := by
    exact hm.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm)
  have : IsIso (unboundedDirectImageComparisonMap A g K) :=
    unboundedDirectImageComparison_boundedBelow A g K 0
  let ei : cZ.mapDerivedCategory.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj H :=
    (cZ.mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso i
  have hp : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (Rp.obj ((DerivedCategory.singleFunctor _ 0).obj H))) := by
    exact (cV.map_isZero he).of_iso
      (((cV.mapDerivedCategoryHomologyFunctorIso q).app (Re.obj K)) ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso
          (asIso (unboundedDirectImageComparisonMap A g K)) ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (Rp.mapIso ei)).symm
  exact ⟨hp, globalSections_vanishing_of_directImage A g
    (weaklyContractible_terminal V _hV) _ q hp⟩

end AlgebraicGeometry.ProEtale
