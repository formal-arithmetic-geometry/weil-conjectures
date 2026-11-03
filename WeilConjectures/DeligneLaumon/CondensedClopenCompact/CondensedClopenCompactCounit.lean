/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.ProperBaseChange.CondensedQbarFieldEvaluationLinearity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel

/-! # Finite clopen counit decomposition
(blueprint: lem-zl-condensed-clopen-compact-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedClopenCompact

private theorem zero_of_restrictions
    (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}}
    {I : Type w} [Finite I] {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X)
    [∀ i, QuasiCompact (j i)] (hc : ∀ x, ∃ i, x ∈ Set.range (j i))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) X))
    (hM : ∀ i, IsZero ((ProEtale.CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ell) (j i)).obj M)) : IsZero M := by
  apply ProEtale.CondensedRing.isZero_of_isZero_X (Profinite.padicAlgClRingObj ell)
  rw [IsZero.iff_id_eq_zero]
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp j hc
  intro i
  have hz := ((Mod.forget _).map_isZero (hM i)).of_iso
    (ProEtale.CondensedRing.upperStarObjXIso (Profinite.padicAlgClRingObj ell)
      (j i) M).symm
  exact hz.eq_of_src _ _

private theorem restrictions_reflect_isomorphisms
    (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}}
    {I : Type w} [Finite I] {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X)
    [∀ i, QuasiCompact (j i)] (hc : ∀ x, ∃ i, x ∈ Set.range (j i)) :
    JointlyReflectIsomorphisms (fun i ↦ pull ell (j i)) := by
  apply Functor.jointlyReflectIsomorphisms_mapDerivedCategory
  constructor
  intro M N f hf
  have hker (i : I) : IsZero ((ProEtale.CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ell) (j i)).obj (kernel f)) :=
    (isZero_kernel_of_mono ((ProEtale.CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ell) (j i)).map f)).of_iso (PreservesKernel.iso _ f)
  have hcoker (i : I) : IsZero ((ProEtale.CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ell) (j i)).obj (cokernel f)) :=
    (isZero_cokernel_of_epi ((ProEtale.CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ell) (j i)).map f)).of_iso (PreservesCokernel.iso _ f)
  have : Mono f := Preadditive.mono_of_isZero_kernel _
    (zero_of_restrictions ell j hc _ hker)
  have : Epi f := Preadditive.epi_of_isZero_cokernel _
    (zero_of_restrictions ell j hc _ hcoker)
  exact isIso_of_mono_of_epi f

private theorem split_of_restriction_counits
    {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    {I : Type*} [Fintype I] [DecidableEq I] {D : I → Type*}
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    (L : ∀ i, D i ⥤ C) (R : ∀ i, C ⥤ D i) [∀ i, (R i).Additive]
    (a : ∀ i, L i ⊣ R i) (ha : ∀ i, IsIso (a i).unit)
    (hz : ∀ i r, i ≠ r → ∀ M, IsZero ((R r).obj ((L i).obj M)))
    (hr : JointlyReflectIsomorphisms R) :
    ∃ p : ∀ i, 𝟭 C ⟶ R i ⋙ L i,
      (∀ i r, (a i).counit ≫ p r =
        if h : i = r then eqToHom (congrArg (fun i ↦ R i ⋙ L i) h) else 0) ∧
      (∑ i, p i ≫ (a i).counit) = 𝟙 _ := by
  classical
  let : HasFiniteBiproducts (C ⥤ C) := HasFiniteBiproducts.of_hasFiniteProducts
  let G (i : I) := R i ⋙ L i
  let t : ⨁ G ⟶ 𝟭 C := biproduct.desc (fun i ↦ (a i).counit)
  have ht : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro K
    apply (hr.isIso_iff (t.app K)).2
    intro r
    have hi : IsIso ((R r).map ((biproduct.ι G r).app K)) := by
      refine ⟨⟨(R r).map ((biproduct.π G r).app K), ?_, ?_⟩⟩
      · rw [← Functor.map_comp]
        have h := congrArg (fun f ↦ f.app K) (biproduct.ι_π_self G r)
        simpa only [NatTrans.comp_app, NatTrans.id_app, CategoryTheory.Functor.map_id]
          using congrArg (fun f ↦ (R r).map f) h
      · have h := congrArg (fun f ↦ (R r).map (f.app K)) (IsBilimit.total (biproduct.isBilimit G))
        simp only [NatTrans.app_sum, NatTrans.comp_app, Functor.map_sum,
          Functor.map_comp, NatTrans.id_app, CategoryTheory.Functor.map_id] at h
        rw [Finset.sum_eq_single r] at h
        · exact h
        · intro i _ hir
          have hzi := hz i r hir ((R i).obj K)
          have h0 : (R r).map ((biproduct.π G i).app K) = 0 := hzi.eq_of_tgt _ _
          rw [h0, zero_comp]
        · simp
    have hc : IsIso ((R r).map ((a r).counit.app K)) := by
      have := ha r
      have h := (a r).right_triangle_components K
      have : IsIso ((a r).unit.app ((R r).obj K) ≫
          (R r).map ((a r).counit.app K)) := by
        rw [h]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left ((a r).unit.app _) _
    have h : (R r).map ((biproduct.ι G r).app K) ≫ (R r).map (t.app K) =
        (R r).map ((a r).counit.app K) := by
      rw [← Functor.map_comp]
      have hdesc : biproduct.ι G r ≫ t = (a r).counit :=
        biproduct.ι_desc (fun i ↦ (a i).counit) r
      exact congrArg (fun f : G r ⟶ 𝟭 C ↦ (R r).map (f.app K)) hdesc
    have : IsIso ((R r).map ((biproduct.ι G r).app K) ≫ (R r).map (t.app K)) := by
      rw [h]; exact hc
    exact IsIso.of_isIso_comp_left ((R r).map ((biproduct.ι G r).app K)) _
  let p (i : I) : 𝟭 C ⟶ G i := inv t ≫ biproduct.π G i
  refine ⟨p, ?_, ?_⟩
  · intro i r
    have hi : (a i).counit ≫ inv t = biproduct.ι G i := by
      calc
        _ = (biproduct.ι G i ≫ t) ≫ inv t := by rw [biproduct.ι_desc]
        _ = biproduct.ι G i := by
          rw [Category.assoc, IsIso.hom_inv_id t, Category.comp_id]
    simpa only [p, ← Category.assoc, hi] using biproduct.ι_π G i r
  · have hdesc : (∑ i, biproduct.π G i ≫ (a i).counit) = t := by
      calc
        _ = (∑ i, biproduct.π G i ≫ biproduct.ι G i) ≫ t := by
          simp only [Preadditive.sum_comp, Category.assoc, t, biproduct.ι_desc]
        _ = t := by rw [IsBilimit.total (biproduct.isBilimit G), Category.id_comp]
    simp only [p, Category.assoc, ← Preadditive.comp_sum, hdesc, IsIso.inv_hom_id]

/-- Canonical compact-support inclusions for a finite clopen partition admit projections.
Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph and empty-curve clause;
compact-decomposition argument, steps 3--5.
(blueprint: lem-zl-condensed-clopen-compact-counit).

Proof: finite quasi-compact cover detection for abelian sheaves detects zero native
modules after forgetting scalars. Exact restriction therefore jointly reflects
isomorphisms, first on modules by kernels and cokernels, then on derived categories.
Form the finite biproduct of restriction followed by extension by zero, mapping to
the identity by the actual open-adjunction counits. Restricting to any component
annihilates the other summands. On its own summand the adjunction unit is invertible,
so the triangle identity makes the restricted counit invertible. Joint reflection
makes the biproduct counit invertible. Compose its inverse with the biproduct
projections to obtain the orthogonality and sum identities. Postcompose by compact
sections and conjugate through extensionComp; this identifies the inclusions with
componentInclusion and preserves both identities by additivity. The same finite
biproduct argument includes the empty index type and empty components.
-/
theorem compact_clopen_counit_decomposition
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (I : Type w) [Fintype I] [DecidableEq I]
    (U : I → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k)))
    (hc : (⋃ i, Set.range (j i)) = Set.univ) :
    ∃ pi : ∀ i, condensedQbarCompactSections ell k c ⟶
        pull ell (j i) ⋙ condensedQbarCompactSections ell k (c.precomp (j i)),
      (∀ i r, componentInclusion ell k c (j i) ≫ pi r =
        if h : i = r then eqToHom (congrArg
          (fun i ↦ pull ell (j i) ⋙ condensedQbarCompactSections ell k (c.precomp (j i))) h)
        else 0) ∧
      (∑ i, pi i ≫ componentInclusion ell k c (j i)) = 𝟙 _ := by
  classical
  have hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
    intro x
    have hx : x ∈ ⋃ i, Set.range (j i) := by rw [hc]; trivial
    exact Set.mem_iUnion.mp hx
  have hz (i r : I) (hir : i ≠ r) (M : DMod ell (U i)) :
      IsZero ((pull ell (j r)).obj ((extension ell (j i)).obj M)) := by
    apply IsZero.of_iso
      (ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
        (Profinite.padicAlgClRingObj ell) (j i) (j r) (hd hir) M)
    exact ((ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.padicAlgClRingObj ell) (j r)).app _).symm
  have hu (i : I) : IsIso (openAdj ell (j i)).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  obtain ⟨p, hp, hs⟩ := split_of_restriction_counits
    (fun i ↦ extension ell (j i)) (fun i ↦ pull ell (j i))
    (fun i ↦ openAdj ell (j i)) hu hz
    (restrictions_reflect_isomorphisms ell j hcover)
  let F := condensedQbarCompactSections ell k c
  let G (i : I) := pull ell (j i) ⋙ extension ell (j i)
  let H (i : I) := pull ell (j i) ⋙
    condensedQbarCompactSections ell k (c.precomp (j i))
  have : F.Additive := by
    dsimp [F, condensedQbarCompactSections,
      ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification]
    infer_instance
  let W := (Functor.whiskeringRight (DMod ell X) (DMod ell X) _).obj F
  let e (i : I) : G i ⋙ F ≅ H i :=
    Functor.isoWhiskerLeft (pull ell (j i))
      (Functor.isoWhiskerRight (extensionComp ell (j i) c.i)
        (push ell c.g ⋙ condensedQbarDerivedPointSections ell k))
  have he (i : I) : componentInclusion ell k c (j i) =
      (e i).inv ≫ W.map (openAdj ell (j i)).counit := by
    ext K
    simp only [componentInclusion, e, W, Functor.whiskeringRight_obj_map,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.comp_map, Functor.map_comp]
    rfl
  let pi (i : I) : F ⟶ H i := W.map (p i) ≫ (e i).hom
  refine ⟨pi, ?_, ?_⟩
  · intro i r
    by_cases h : i = r
    · subst r
      simp only [dite_true, eqToHom_refl]
      rw [he]
      change ((e i).inv ≫ W.map (openAdj ell (j i)).counit) ≫
        (W.map (p i) ≫ (e i).hom) = 𝟙 _
      rw [Category.assoc, ← Category.assoc (W.map _), ← W.map_comp]
      rw [hp]
      simp only [dite_true, eqToHom_refl]
      rw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id]
    · simp only [dif_neg h]
      rw [he]
      change ((e i).inv ≫ W.map (openAdj ell (j i)).counit) ≫
        (W.map (p r) ≫ (e r).hom) = 0
      rw [Category.assoc, ← Category.assoc (W.map _), ← W.map_comp, hp,
        dif_neg h, W.map_zero, zero_comp, comp_zero]
  · have hterm (i : I) : pi i ≫ componentInclusion ell k c (j i) =
        W.map (p i ≫ (openAdj ell (j i)).counit) := by
      rw [he]
      simp only [pi, Category.assoc, Iso.hom_inv_id_assoc, W.map_comp]
    simp_rw [hterm]
    rw [← W.map_sum, hs, W.map_id]
    rfl

end WeilConjectures.CondensedClopenCompact
