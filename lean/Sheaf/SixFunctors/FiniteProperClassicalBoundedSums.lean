/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts
import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
import all Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves

/-!
# Bounded classical coproduct transport through etale origins

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, Transfer; Stacks Tags 07D9 and 09A6
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

We use the ordinary fixed-ring module-sheaf presentation on both sites. On the
pro-etale site `finiteCoefficientRealization` identifies it with modules over the
recorded continuous-function coefficient sheaf. Classicality below is precisely the
recorded `IsClassicalModuleComplex` after this exact realization. No completion,
constructibility condition, or unbounded essential-image assertion is involved.

The last theorem quantifies over every bounded origin and its identifying isomorphism.
The comparison isomorphisms are pinned down by equality with the canonical derived
mate, and the transport isomorphism by its coprojections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

-- Reuse the existing construction of ambient derived coproducts.
attribute [local instance] CategoryTheory.derived_hasCoproducts

namespace AlgebraicGeometry.ProEtale


private noncomputable def boundedSums_standardHomologyIso (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
          _ _ (HasDerivedCategory.standard _))).inverse ⋙
        @DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
          _ _ (HasDerivedCategory.standard _) q := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let Qs := @DerivedCategory.Q C _ _ (HasDerivedCategory.standard _)
  let Hs := @DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard _) q
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory C _ _ (HasDerivedCategory.standard _))
  let hi : DerivedCategory.Q ⋙ e.inverse ≅ Qs :=
    (Functor.associator Qs e.functor e.inverse).symm ≪≫
      Functor.isoWhiskerLeft Qs e.unitIso.symm ≪≫ Functor.rightUnitor Qs
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) C).preimageIso
  exact DerivedCategory.homologyFunctorFactors C q ≪≫
    (@DerivedCategory.homologyFunctorFactors C _ _ (HasDerivedCategory.standard _) q).symm ≪≫
    (Functor.isoWhiskerRight hi Hs).symm ≪≫ Functor.associator _ _ _


private noncomputable def realizationUnderlyingIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    (SheafOfModules.toSheaf _).obj ((finiteCoefficientRealization T A).obj M) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M := by
  exact asIso ((sheafificationAdjunction (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1}).counit.app
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M))

private theorem realization_classical_iff
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    IsClassicalModuleSheaf ((finiteCoefficientRealization T A).obj M) ↔
      IsClassical ((sheafCompose _ (forget (ModuleCat.{u + 1} A))).obj M) := by
  exact isClassical_iso_iff
    ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).mapIso
      (realizationUnderlyingIso A T M))

private theorem realized_homology_classical_iff
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (q : ℤ) :
    IsClassicalModuleSheaf ((DerivedCategory.homologyFunctor _ q).obj
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj K)) ↔
      IsClassical ((sheafCompose _ (forget (ModuleCat.{u + 1} A))).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  let e := ((finiteCoefficientRealization T A).mapDerivedCategoryHomologyFunctorIso q).app K
  exact (isClassical_iso_iff
    ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).mapIso
      ((SheafOfModules.toSheaf _).mapIso e))).symm.trans
        (realization_classical_iff A T _)


private theorem fixed_classical_iso
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)}
    (e : M ≅ N)
    (hM : IsClassical ((sheafCompose _ (forget (ModuleCat.{u + 1} A))).obj M)) :
    IsClassical ((sheafCompose _ (forget (ModuleCat.{u + 1} A))).obj N) :=
  (isClassical_iso_iff ((sheafCompose _ (forget (ModuleCat.{u + 1} A))).mapIso e)).mp hM

private theorem fixed_classical_zero
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) (hM : IsZero M) :
    IsClassical ((sheafCompose _ (forget (ModuleCat.{u + 1} A))).obj M) := by
  obtain ⟨_, _, _, _, _, he⟩ := proEtaleClassicalSheavesModules T A
  apply (he M).2
  refine ⟨HasZeroObject.zero.choose, ⟨?_⟩⟩
  exact ((comparisonUpperStar (ModuleCat.{u + 1} A) T).map_isZero
    HasZeroObject.zero.choose_spec).iso hM

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem boundedSums_truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T


private theorem boundedSums_truncLE_preservesCoproducts
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] (I : Type*)
    [HasColimitsOfShape (Discrete I) C] [HasExactColimitsOfShape (Discrete I) C]
    (n : ℤ) :
    PreservesColimitsOfShape (Discrete I)
      ((DerivedCategory.TStructure.t (C := C)).truncLE n) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let F := t.truncLE n
  let ι := t.truncLEι n
  have hK (K : I → DerivedCategory C) : PreservesColimit (Discrete.functor K) F := by
    let c := sigmaComparison F K
    have hc : c ≫ ι.app (∐ K) = Limits.Sigma.map (fun i ↦ ι.app (K i)) := by
      apply Sigma.hom_ext
      intro i
      rw [← Category.assoc]
      change (Sigma.ι _ i ≫ sigmaComparison F K) ≫ ι.app (∐ K) = _
      rw [ι_comp_sigmaComparison, Limits.Sigma.ι_map]
      exact ι.naturality (Sigma.ι K i)
    have : IsIso c := by
      rw [DerivedCategory.isIso_iff]
      intro q
      by_cases hq : q ≤ n
      · have hι := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app (∐ K)
          (n + 1) q (by omega)
        have : IsIso ((DerivedCategory.homologyFunctor C q).map (ι.app (∐ K))) := by
          simpa only [ι, t, TStructure.truncLEι] using hι
        have hmap := DerivedCategory.isIso_homologyFunctor_map_sigmaMap
          (fun i ↦ ι.app (K i)) q (fun i ↦
            DerivedCategory.isIso_homologyFunctor_map_truncLTι_app (K i)
              (n + 1) q (by omega))
        have : IsIso ((DerivedCategory.homologyFunctor C q).map c ≫
            (DerivedCategory.homologyFunctor C q).map (ι.app (∐ K))) := by
          rw [← Functor.map_comp, hc]
          exact hmap
        exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor C q).map
          (ι.app (∐ K)))
      · have : (∐ fun i ↦ F.obj (K i)).IsLE n :=
          DerivedCategory.isLE_sigma _ n (fun _ ↦ inferInstance)
        exact (DerivedCategory.isZero_of_isLE _ n q (by omega)).isIso
          (DerivedCategory.isZero_of_isLE _ n q (by omega)) _
    exact PreservesCoproduct.of_iso_comparison F K
  let : ∀ K : I → DerivedCategory C, PreservesColimit (Discrete.functor K) F := hK
  exact preservesColimitsOfShape_of_discrete F

/-- Arbitrary ambient coproducts of classical complexes are classical.
Source: blueprint Transfer; Stacks Tag 07D9 and Bhatt--Scholze, Lemma 5.1.2
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: the module categories are Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck.
Exact small sums are filtered colimits of finite partial sums. Termwise sums compute
ambient derived coproducts by lem-kun-grothendieck-derived-coproducts, including zero
for the empty family. Thus H^q of the sum is the sum of H^q. Each classical sheaf is
an exact comparison inverse image by det-pe-classical-sheaves-modules. That left
adjoint preserves sums, so the sum of these cohomology sheaves is again classical.
The exact coefficient realization gives the same assertion in the recorded encoding. -/
theorem finiteProperClassical_coproduct_closure
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (I : Type (u + 1))
    (L : I → DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hL : ∀ s : I, IsClassicalModuleComplex
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj (L s))) :
    IsClassicalModuleComplex
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj (∐ L)) := by
  classical
  intro q
  apply (realized_homology_classical_iff A T (∐ L) q).2
  obtain ⟨_, _, _, _, _, he⟩ := proEtaleClassicalSheavesModules T A
  have h (s : I) := (he _).1
    ((realized_homology_classical_iff A T (L s) q).1 (_hL s q))
  choose M e using h
  let F := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let H := DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) q
  apply (he _).2
  refine ⟨∐ M, ⟨?_⟩⟩
  exact (asIso (sigmaComparison F M)).symm ≪≫
    Limits.Sigma.mapIso (fun s ↦ (e s).some) ≪≫ asIso (sigmaComparison H L)


/-- Both standard good truncations preserve classical cohomology.
Source: blueprint Transfer; Bhatt--Scholze, Definition 5.1.3; def-kun-truncations
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: good truncation retains each cohomology sheaf on its allowed side and gives
zero on the other side. Zero is the inverse image of zero under the exact comparison
functor. Hence both truncations are classical by sk-def-pe-classical-definition.
The exact realization commutes with cohomology and the standard t-structure. -/
theorem finiteProperClassical_truncation_closure
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hL : IsClassicalModuleComplex
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj L)) (n : ℤ) :
    IsClassicalModuleComplex ((finiteCoefficientRealization T A).mapDerivedCategory.obj
      ((DerivedCategory.TStructure.t.truncLE n).obj L)) ∧
    IsClassicalModuleComplex ((finiteCoefficientRealization T A).mapDerivedCategory.obj
      ((DerivedCategory.TStructure.t.truncGE n).obj L)) := by
  constructor
  · intro q
    apply (realized_homology_classical_iff A T _ q).2
    by_cases hq : q ≤ n
    · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app L (n + 1) q
        (by omega)
      have : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLEι n).app L)) := by
        simpa only [TStructure.truncLEι] using this
      exact fixed_classical_iso A T
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLEι n).app L))).symm
        ((realized_homology_classical_iff A T L q).1 (_hL q))
    · exact fixed_classical_zero A T _ (DerivedCategory.isZero_of_isLE _ n q (by omega))
  · intro q
    apply (realized_homology_classical_iff A T _ q).2
    by_cases hq : n ≤ q
    · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L n q hq
      exact fixed_classical_iso A T
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncGEπ n).app L)))
        ((realized_homology_classical_iff A T L q).1 (_hL q))
    · exact fixed_classical_zero A T _ (DerivedCategory.isZero_of_isGE _ n q (by omega))


/-- Cohomology and both good truncations commute naturally with ambient sums, with the
specified inclusion and quotient maps. Preservation gives the canonical natural sum
comparisons, rather than arbitrary object isomorphisms.
Source: blueprint Transfer, steps 1--2; Stacks Tag 07D9, clauses (1)--(2)
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: termwise coproducts represent ambient derived coproducts by
lem-kun-grothendieck-derived-coproducts. Exactness of sums identifies kernels, images,
and cokernels of the sum differential with sums of those objects. Their quotient is
the natural cohomology comparison. In the boundary degree good truncation uses just
these kernel or cokernel maps; elsewhere its comparison is the identity or the zero
map. These identifications commute with the truncation inclusion and quotient, and
are natural in the family. Localization retains the specified coprojections and maps.
The same computations apply to the empty family. -/
theorem finiteProperClassical_coproduct_cohomology_truncations
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u}) (I : Type (u + 1)) :
    (∀ q : ℤ, PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) q)) ∧
    (∀ n : ℤ,
      PreservesColimitsOfShape (Discrete I)
        ((DerivedCategory.TStructure.t
          (C := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))).truncLE n)) ∧
    (∀ n : ℤ,
      PreservesColimitsOfShape (Discrete I)
        ((DerivedCategory.TStructure.t
          (C := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))).truncGE n)) ∧
    (∀ (L : I → DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) (n : ℤ),
      sigmaComparison (DerivedCategory.TStructure.t.truncLE n) L ≫
          (DerivedCategory.TStructure.t.truncLEι n).app (∐ L) =
        Sigma.desc (fun s : I ↦
          (DerivedCategory.TStructure.t.truncLEι n).app (L s) ≫ Sigma.ι L s)) ∧
    (∀ (L : I → DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) (n : ℤ),
      Sigma.desc (fun s : I ↦
          (DerivedCategory.TStructure.t.truncGEπ n).app (L s) ≫
            Sigma.ι (fun s : I ↦ (DerivedCategory.TStructure.t.truncGE n).obj (L s)) s) ≫
          sigmaComparison (DerivedCategory.TStructure.t.truncGE n) L =
        (DerivedCategory.TStructure.t.truncGEπ n).app (∐ L)) := by
  refine ⟨fun _ ↦ inferInstance, fun n ↦ boundedSums_truncLE_preservesCoproducts I n,
    fun n ↦ boundedSums_truncGE_preservesCoproducts n, ?_, ?_⟩
  · intro L n
    apply Sigma.hom_ext
    intro s
    simp only [← Category.assoc, ι_comp_sigmaComparison, Sigma.ι_desc]
    exact (DerivedCategory.TStructure.t.truncLEι n).naturality (Sigma.ι L s)
  · intro L n
    apply Sigma.hom_ext
    intro s
    rw [Sigma.ι_desc_assoc, Category.assoc, ι_comp_sigmaComparison]
    exact ((DerivedCategory.TStructure.t.truncGEπ n).naturality (Sigma.ι L s)).symm


/-- Exact termwise comparison inverse image preserves all small ambient coproducts.
Source: blueprint Transfer, step 3; Bhatt--Scholze, Lemma 5.1.2; Stacks Tag 07D9
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: comparison inverse image is the exact left adjoint of
 det-pe-classical-sheaves-modules. Its adjunction identifies maps from the image of a
sum with families of maps from the images, including the empty sum. Apply this
preservation termwise to representative complexes, and use
lem-kun-grothendieck-derived-coproducts on both sites. This gives preservation of the
specified ambient coproduct, with its canonical comparison on coprojections. -/
theorem finiteProperClassical_comparison_preservesCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u}) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory := by
  exact (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory_preservesCoproducts I

/-- A family in a common finite cohomological interval has etale origins in that same
interval. The family may be empty.
Source: blueprint Transfer, step 5; Bhatt--Scholze, Corollary 5.1.6
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: sk-prop-sf-comparison supplies the bounded-below derived unit. Apply
 det-pe-classical-derived-equivalence to every classical summand to obtain an etale
origin and its counit isomorphism. Exact inverse image commutes with cohomology by
lem-weil-pbc-exact-functor-bounded-below. Its full faithfulness on sheaves reflects
zero, so the origin has vanishing cohomology below a and above b. Choice assembles
these origins as a family; for the empty family there is nothing to choose. -/
theorem finiteProperClassical_bounded_origins
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (X : Scheme.{u})
    (I : Type (u + 1)) (a b : ℤ) (_hab : a ≤ b)
    (L : I → DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hL : ∀ s : I, IsClassicalModuleComplex
      ((finiteCoefficientRealization X A).mapDerivedCategory.obj (L s)))
    (_hge : ∀ s : I, (L s).IsGE a) (_hle : ∀ s : I, (L s).IsLE b) :
    ∃ B : I → Etale.DerivedCategoryModule A X,
      (∀ s : I, (B s).IsGE a ∧ (B s).IsLE b) ∧
      Nonempty (∀ s : I,
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (B s) ≅ L s) := by
  classical
  let F := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) X
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X).derivedPlus
  let K (s : I) : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
    ⟨L s, a, _hge s⟩
  have hunit : ∀ M, IsIso (adj.unit.app M) := by
    have := (boundedBelowComparison X A).1
    intro M
    infer_instance
  have hK (s : I) : ClassicalPlus X A (K s) := by
    intro q
    apply (AlgebraicGeometry.classicalModuleFor_iff X A _).2
    apply fixed_classical_iso A X
      ((boundedSums_standardHomologyIso X A q).app (L s))
    exact (realized_homology_classical_iff A X (L s) q).1 (_hL s q)
  have hc (s : I) : IsIso (adj.counit.app (K s)) :=
    (classicalDerivedEquivalence X A hunit).2.1 (K s) (hK s)
  let B (s : I) : Etale.DerivedCategoryModule A X :=
    (R.rightDerivedFunctorPlus.obj (K s)).obj
  let e (s : I) : F.mapDerivedCategory.obj (B s) ≅ L s :=
    (F.mapDerivedCategoryPlusCompatibility.app (R.rightDerivedFunctorPlus.obj (K s))).symm ≪≫
      DerivedCategory.Plus.ι.mapIso (asIso (adj.counit.app (K s)))
  refine ⟨B, ?_, ⟨e⟩⟩
  intro s
  apply F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
  have : (L s).IsGE a := _hge s
  have : (L s).IsLE b := _hle s
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso (e s).symm a,
    DerivedCategory.TStructure.t.isLE_of_iso (e s).symm b⟩


/-- For every bounded choice of etale origins, the actual pro-etale coproduct comparison
is the specified composite of the canonical derived mates, etale sum comparison, and
origin identifications. The displayed component equations uniquely determine `t` and
the mate isomorphisms, so the assertion applies to every such canonical choice.
Source: blueprint Transfer, steps 6--9; Stacks Tag 09A6
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof:
1. Properness gives quasi-compactness and quasi-separatedness by
   def-weil-finite-type-morphism and lem-pc-separated-quasi-separated. Exact sums
   retain the common bounds [a,b], so B_s and their sum are bounded below.
2. Apply sk-thm-pe-direct-image-comparison to B_s and their sum. Its canonical
   natural transformation is the unbounded mate restricted to these inputs. The
   resulting isomorphisms are theta and Theta below; their hom equations fix them.
3. Inverse image preserves coproducts by step 3 of the node's proof. Transporting
   along the i_s gives the unique isomorphism t with the displayed coprojections.
   Its inverse is induced by F_X(iota_s) composed with i_s inverse. The Y-side
   canonical comparison is alpha_Y = sigmaComparison F_Y (E B_s).
4. The explicit etale preservation hypothesis makes sigmaComparison E B invertible.
   Thus every factor of the displayed composite is invertible.
5. Test the composite on its s-th coprojection. The definitions of sums of maps,
   alpha_Y and the etale comparison reduce it to
   G(i_s) inverse, theta_s inverse, F_Y(E iota_s), theta_sum, and G(t).
   Naturality of the canonical mate interchanges the middle three maps, leaving
   G(i_s inverse followed by F_X(iota_s) followed by t) = G(iota'_s).
6. The coproduct universal property identifies this composite with sigmaComparison
   G L, proving the factorization, invertibility, and the specified component law.
   For the empty family the sum of origins is zero and lies in every interval;
   the same argument uses the unique map out of the zero source. No unbounded
   classical essential-image equivalence is used. -/
theorem finiteProperClassical_bounded_sum_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (_hE : ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor)
    (I : Type (u + 1)) (a b : ℤ) (_hab : a ≤ b)
    (L : I → DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hL : ∀ s : I, IsClassicalModuleComplex
      ((finiteCoefficientRealization X A).mapDerivedCategory.obj (L s)))
    (_hge : ∀ s : I, (L s).IsGE a) (_hle : ∀ s : I, (L s).IsLE b)
    (B : I → Etale.DerivedCategoryModule A X)
    (_hB : ∀ s : I, (B s).IsGE a ∧ (B s).IsLE b)
    (i : ∀ s : I,
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (B s) ≅ L s) :
    ∃ (theta : ∀ s : I,
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (B s)) ≅
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (B s)))
      (Theta :
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (∐ B)) ≅
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (∐ B)))
      (t : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (∐ B) ≅
        ∐ L),
      (∀ s : I, (theta s).hom = unboundedDirectImageComparisonMap A f (B s)) ∧
      Theta.hom = unboundedDirectImageComparisonMap A f (∐ B) ∧
      (∀ s : I,
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map (Sigma.ι B s) ≫
            t.hom = (i s).hom ≫ Sigma.ι L s) ∧
      sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor L =
        Sigma.desc (fun s : I ↦
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso (i s)).inv ≫
            (theta s).inv ≫
            Sigma.ι (fun s : I ↦
              (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
                ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (B s))) s) ≫
          sigmaComparison (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
            (fun s : I ↦
              (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (B s)) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            (sigmaComparison (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor B) ≫
          Theta.hom ≫ (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map t.hom ∧
      IsIso (sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor L) ∧
      (∀ s : I,
        Sigma.ι (fun s : I ↦
            (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (L s)) s ≫
          sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor L =
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map (Sigma.ι L s)) := by
  classical
  let FX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let FY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let E := (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let G := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  have : PreservesColimitsOfShape (Discrete I) FX :=
    finiteProperClassical_comparison_preservesCoproducts A X I
  have : PreservesColimitsOfShape (Discrete I) FY :=
    finiteProperClassical_comparison_preservesCoproducts A Y I
  have : PreservesColimitsOfShape (Discrete I) E := _hE I
  have hBge (s : I) : (B s).IsGE a := (_hB s).1
  have : (∐ B).IsGE a := DerivedCategory.isGE_sigma B a hBge
  have htheta (s : I) : IsIso (unboundedDirectImageComparisonMap A f (B s)) :=
    unboundedDirectImageComparison_boundedBelow A f (B s) a
  have hTheta : IsIso (unboundedDirectImageComparisonMap A f (∐ B)) :=
    unboundedDirectImageComparison_boundedBelow A f (∐ B) a
  let theta (s : I) := asIso (unboundedDirectImageComparisonMap A f (B s))
  let Theta := asIso (unboundedDirectImageComparisonMap A f (∐ B))
  let t : FX.obj (∐ B) ≅ ∐ L :=
    (asIso (sigmaComparison FX B)).symm ≪≫ Limits.Sigma.mapIso i
  have ht (s : I) : FX.map (Sigma.ι B s) ≫ t.hom = (i s).hom ≫ Sigma.ι L s := by
    dsimp only [t, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    rw [map_ι_comp_inv_sigmaComparison_assoc, Limits.Sigma.ι_mapIso_hom]
  let d : (∐ fun s ↦ G.obj (L s)) ⟶ ∐ fun s ↦ FY.obj (E.obj (B s)) :=
    Sigma.desc (fun s ↦ (G.mapIso (i s)).inv ≫ (theta s).inv ≫
      Sigma.ι (fun s ↦ FY.obj (E.obj (B s))) s)
  have hd : IsIso d := by
    have heq : d = (Limits.Sigma.mapIso
        (fun s ↦ (G.mapIso (i s)).symm ≪≫ (theta s).symm)).hom := by
      apply Sigma.hom_ext
      intro s
      simp only [d, Sigma.ι_desc, Limits.Sigma.ι_mapIso_hom, Iso.trans_hom,
        Iso.symm_hom, Category.assoc]
      rfl
    rw [heq]
    infer_instance
  have hfac : sigmaComparison G L =
      d ≫ sigmaComparison FY (fun s ↦ E.obj (B s)) ≫
        FY.map (sigmaComparison E B) ≫ Theta.hom ≫ G.map t.hom := by
    apply Sigma.hom_ext
    intro s
    rw [ι_comp_sigmaComparison]
    dsimp only [d]
    rw [Sigma.ι_desc_assoc]
    simp only [Category.assoc]
    rw [ι_comp_sigmaComparison_assoc, ← FY.map_comp_assoc,
      ι_comp_sigmaComparison]
    have hn := unboundedDirectImageComparisonMap_naturality A f (Sigma.ι B s)
    change FY.map (E.map (Sigma.ι B s)) ≫ Theta.hom =
      (theta s).hom ≫ G.map (FX.map (Sigma.ι B s)) at hn
    rw [reassoc_of% hn, Iso.inv_hom_id_assoc, ← G.map_comp, ht]
    change G.map (Sigma.ι L s) = G.map (i s).inv ≫
      G.map ((i s).hom ≫ Sigma.ι L s)
    rw [← G.map_comp, Iso.inv_hom_id_assoc]
  refine ⟨theta, Theta, t, (fun _ ↦ rfl), rfl, ht, hfac, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · intro s
    exact ι_comp_sigmaComparison G L s


end AlgebraicGeometry.ProEtale
