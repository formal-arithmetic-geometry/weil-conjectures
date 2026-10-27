/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.Triangulated.FixedPairTruncationCohomologyFunctors
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Transfer

/-! # Exact hearts and cohomology on fixed pairs

Source: BBD 1.3.3–1.3.6 and 1.3.16–1.3.17; blueprint restriction and Part 2 of
`lem-zl-morphism-open-closed-reduction.proof.md`, with the fixed-pair calculations
in the twelve-step DAG proof (blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

We reuse `IsoAlgebra.mapOfNatIso`, the canonical truncation lifts, and full subcategories.
No shift or triangulated structure is imposed on a fixed-pair category.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD uE vE

namespace CategoryTheory.Triangulated.TStructure

open Limits Endofunctor

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]

/-- The full subcategory of fixed pairs with carrier in the heart.
Source: BBD 1.3.6, fixed-pair heart in the node's statement
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
abbrev fixedPairHeart (t : TStructure C) (P : C ⥤ C) :=
  (t.heart.inverseImage (IsoAlgebra.forget P)).FullSubcategory

/-- Forget a heart fixed pair to its carrier in the ordinary heart.
Source: BBD 1.3.6, node's kernel and cokernel clause
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
def fixedPairHeartForget (t : TStructure C) (P : C ⥤ C) :
    fixedPairHeart t P ⥤ t.heart.FullSubcategory :=
  t.heart.lift ((t.heart.inverseImage (IsoAlgebra.forget P)).ι ⋙ IsoAlgebra.forget P)
    (fun K ↦ K.property)

/-- Restriction of the existing fixed-pair transport to the full hearts.
Source: BBD 1.3.16–1.3.17, node's last paragraph
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
noncomputable def fixedPairHeartMap (tC : TStructure C) (tD : TStructure D)
    (P : C ⥤ C) (Q : D ⥤ D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (α : F ⋙ Q ≅ P ⋙ F) : fixedPairHeart tC P ⥤ fixedPairHeart tD Q :=
  (tD.heart.inverseImage (IsoAlgebra.forget Q)).lift
    ((tC.heart.inverseImage (IsoAlgebra.forget P)).ι ⋙ IsoAlgebra.mapOfNatIso α)
    (fun K ↦
      have : tC.IsLE K.obj.carrier 0 := ⟨K.property.1⟩
      have : tC.IsGE K.obj.carrier 0 := ⟨K.property.2⟩
      (tD.mem_heart_iff (F.obj K.obj.carrier)).2
        ⟨Functor.IsTExact.isLE_obj tC tD F K.obj.carrier 0,
          Functor.IsTExact.isGE_obj tC tD F K.obj.carrier 0⟩)

/-- The component of the canonical comparison `F(HᵃK) ≅ Hᵃ(FK)`.
This abbreviates `truncationCohomologyComparison`, owned by
`def-per-truncation-cohomology-comparison`, with its specified shift and truncation data.
Source: BBD 1.3.3–1.3.6 and 1.3.16, node proof step 2
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
noncomputable abbrev fixedPairCohomologyCarrierComparison
    (tC : TStructure C) (tD : TStructure D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] (a : ℤ) (K : C) :
    F.obj ((tC.truncGELE a a ⋙ shiftFunctor C a).obj K) ≅
      (tD.truncGELE a a ⋙ shiftFunctor D a).obj (F.obj K) :=
  (truncationCohomologyComparison tC tD F a).app K

/-- The composite intertwiner, including the functor associators.
Source: the node's proof step 6 (blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
def fixedPairCompositeIntertwiner
    {E : Type uE} [Category.{vE} E] (P : C ⥤ C) (Q : D ⥤ D) (R : E ⥤ E)
    (F : C ⥤ D) (G : D ⥤ E) (α : F ⋙ Q ≅ P ⋙ F) (β : G ⋙ R ≅ Q ⋙ G) :
    (F ⋙ G) ⋙ R ≅ P ⋙ (F ⋙ G) :=
  Functor.associator F G R ≪≫ Functor.isoWhiskerLeft F β ≪≫
    (Functor.associator F Q G).symm ≪≫ Functor.isoWhiskerRight α G ≪≫
    Functor.associator P F G

/-- Canonical cohomology comparison for a composite, using the induced t-exactness proof.
The construction is the same normalized truncation construction for the composite functor.
Source: BBD 1.3.3 and 1.3.16, node proof steps 4 and 6
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
noncomputable def fixedPairCompositeCohomologyComparison
    {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] [IsTriangulated E]
    (tC : TStructure C) (tD : TStructure D) (tE : TStructure E)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tD tE]
    (a : ℤ) (K : C) :
    G.obj (F.obj ((tC.truncGELE a a ⋙ shiftFunctor C a).obj K)) ≅
      (tE.truncGELE a a ⋙ shiftFunctor E a).obj (G.obj (F.obj K)) :=
  letI : (F ⋙ G).IsTExact tC tE :=
    { isLE X n :=
        have := Functor.IsTExact.isLE_obj tC tD F X n
        Functor.IsTExact.isLE_obj tD tE G (F.obj X) n
      isGE X n :=
        have := Functor.IsTExact.isGE_obj tC tD F X n
        Functor.IsTExact.isGE_obj tD tE G (F.obj X) n }
  fixedPairCohomologyCarrierComparison tC tE (F ⋙ G) a K

/-- Canonical comparison for the identity, with its canonical shift and t-exactness data.
Source: BBD 1.3.3, node proof steps 4 and 6
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
noncomputable def fixedPairIdentityCohomologyComparison (t : TStructure C) (a : ℤ) (K : C) :
    (t.truncGELE a a ⋙ shiftFunctor C a).obj K ≅
      (t.truncGELE a a ⋙ shiftFunctor C a).obj K :=
  letI : (𝟭 C).IsTExact t t :=
    { isLE X n := inferInstanceAs (t.IsLE X n)
      isGE X n := inferInstanceAs (t.IsGE X n) }
  fixedPairCohomologyCarrierComparison t t (𝟭 C) a K

private noncomputable def liftComparison
    (P H : C ⥤ C) (Q J : D ⥤ D) (F : C ⥤ D)
    (α : F ⋙ Q ≅ P ⋙ F) (bP : H ⋙ P ≅ P ⋙ H)
    (bQ : J ⋙ Q ≅ Q ⋙ J) (e : H ⋙ F ≅ F ⋙ J)
    (h : ∀ K : C, α.hom.app (H.obj K) ≫ F.map (bP.hom.app K) ≫
      e.hom.app (P.obj K) = Q.map (e.hom.app K) ≫ bQ.hom.app (F.obj K) ≫
        J.map (α.hom.app K)) :
    IsoAlgebra.mapOfNatIso α ⋙ IsoAlgebra.mapOfNatIso bQ ≅
      IsoAlgebra.mapOfNatIso bP ⋙ IsoAlgebra.mapOfNatIso α := by
  let eLift : IsoAlgebra.mapOfNatIso bP ⋙ IsoAlgebra.mapOfNatIso α ≅
      IsoAlgebra.mapOfNatIso α ⋙ IsoAlgebra.mapOfNatIso bQ :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
      (Algebra.isoMk (e.app K.carrier) (by
        change Q.map (e.hom.app K.carrier) ≫
            (bQ.hom.app (F.obj K.carrier) ≫ J.map (α.hom.app K.carrier ≫
              F.map K.str.hom)) =
          (α.hom.app (H.obj K.carrier) ≫
            F.map (bP.hom.app K.carrier ≫ H.map K.str.hom)) ≫ e.hom.app K.carrier
        simp only [Functor.map_comp, Category.assoc]
        calc
          _ = α.hom.app (H.obj K.carrier) ≫ F.map (bP.hom.app K.carrier) ≫
              e.hom.app (P.obj K.carrier) ≫ J.map (F.map K.str.hom) := by
            simpa only [Category.assoc] using
              congrArg (· ≫ J.map (F.map K.str.hom)) (h K.carrier).symm
          _ = _ := by
            have hn := e.hom.naturality K.str.hom
            simp only [Functor.comp_map] at hn
            rw [← hn])))
      (fun {K L} u ↦ ObjectProperty.hom_ext _
        (Algebra.Hom.ext (e.hom.naturality u.hom.f)))
  exact eLift.symm

private noncomputable def cohomologyLiftIso (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (a : ℤ) :
    fixedPairCohomology t P a ≅
      IsoAlgebra.mapOfNatIso (truncationCohomologyComparison t t P a) :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (Iso.refl _) (by
      simp [fixedPairCohomology, fixedPairTruncLE, fixedPairTruncGE, fixedPairShift,
        IsoAlgebra.mapOfNatIso, Algebra.mapOfNatTrans, truncationCohomologyComparison,
        Functor.map_comp, Category.assoc, truncLE, truncGELE])))
    (by
      intro K L u
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      simp [truncLE])

private def heartMap (tC : TStructure C) (tD : TStructure D) (F : C ⥤ D)
    [F.IsTExact tC tD] : tC.heart.FullSubcategory ⥤ tD.heart.FullSubcategory :=
  tD.heart.lift (tC.heart.ι ⋙ F) (fun X ↦ by
    have : tC.IsLE X.obj 0 := ⟨X.property.1⟩
    have : tC.IsGE X.obj 0 := ⟨X.property.2⟩
    exact (tD.mem_heart_iff _).2
      ⟨Functor.IsTExact.isLE_obj tC tD F X.obj 0,
        Functor.IsTExact.isGE_obj tC tD F X.obj 0⟩)

private instance heartMap_additive (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.IsTExact tC tD] [F.Additive] : (heartMap tC tD F).Additive where
  map_add := by
    intro X Y f g
    exact ObjectProperty.hom_ext _ F.map_add

private theorem heartMap_exact (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] :
    PreservesFiniteLimits (heartMap tC tD F) ∧
      PreservesFiniteColimits (heartMap tC tD F) := by
  apply ((Functor.exact_tfae (heartMap tC tD F)).out 0 3).1
  intro S hS
  let := tC.hasHeartFullSubcategory
  let := tD.hasHeartFullSubcategory
  obtain ⟨δ, hδ⟩ := (tC.shortExact_iff_exists_distTriang S).1 hS
  apply (tD.shortExact_iff_exists_distTriang _).2
  exact ⟨F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _, F.map_distinguished _ hδ⟩

private noncomputable def heartPairEquivalence (t : TStructure C) (P : C ⥤ C)
    [P.IsTExact t t] : fixedPairHeart t P ≌ IsoAlgebra (heartMap t t P) where
  functor :=
    { obj K := IsoAlgebra.mk ⟨K.obj.carrier, K.property⟩
        (ObjectProperty.isoMk _ K.obj.str)
      map u := ObjectProperty.homMk
        { f := ObjectProperty.homMk u.hom.hom.f
          h := ObjectProperty.hom_ext _ u.hom.hom.h } }
  inverse :=
    { obj K := ⟨IsoAlgebra.mk K.carrier.obj ((t.heart.ι).mapIso K.str),
        K.carrier.property⟩
      map u := ObjectProperty.homMk (ObjectProperty.homMk
        { f := u.hom.f.hom
          h := congrArg (fun f ↦ f.hom) u.hom.h }) }
  unitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ (Algebra.isoMk (Iso.refl _))))
    (by
      intro K L u
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (ObjectProperty.isoMk _ (Iso.refl _))
      (by
        apply ObjectProperty.hom_ext
        change P.map (𝟙 K.carrier.obj) ≫ K.obj.str.hom = K.obj.str.hom ≫ 𝟙 _
        simp)))
    (by
      intro K L u
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      apply ObjectProperty.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

  functor_unitIso_comp K := by
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    exact Category.id_comp _

private theorem heartPair_abelian (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] :
    Nonempty (Abelian (fixedPairHeart t P)) := by
  let := (heartMap_exact t t P).1
  let := (heartMap_exact t t P).2
  let e := heartPairEquivalence t P
  let : HasFiniteProducts (fixedPairHeart t P) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact ⟨abelianOfEquivalence e.functor⟩

private theorem heartPairForget_exact (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] :
    PreservesFiniteLimits (fixedPairHeartForget t P) ∧
      PreservesFiniteColimits (fixedPairHeartForget t P) := by
  let := (heartMap_exact t t P).1
  let := (heartMap_exact t t P).2
  let e := heartPairEquivalence t P
  let i : e.functor ⋙ IsoAlgebra.forget (heartMap t t P) ≅
      fixedPairHeartForget t P := Iso.refl _
  exact ⟨preservesFiniteLimits_of_natIso i, preservesFiniteColimits_of_natIso i⟩

private instance heartPairForget_reflectsIso (t : TStructure C) (P : C ⥤ C)
    [P.Additive] : (fixedPairHeartForget t P).ReflectsIsomorphisms := by
  have : (fixedPairHeartForget t P ⋙ t.heart.ι).ReflectsIsomorphisms :=
    inferInstanceAs
      (((t.heart.inverseImage (IsoAlgebra.forget P)).ι ⋙
        IsoAlgebra.forget P).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp (fixedPairHeartForget t P) t.heart.ι

private theorem heartPairMap_exact (tC : TStructure C) (tD : TStructure D)
    (P : C ⥤ C) (Q : D ⥤ D)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact tC tC]
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact tD tD]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (α : F ⋙ Q ≅ P ⋙ F) :
    PreservesFiniteLimits (fixedPairHeartMap tC tD P Q F α) ∧
      PreservesFiniteColimits (fixedPairHeartMap tC tD P Q F α) := by
  let := (heartPair_abelian tC P).some
  let := (heartPair_abelian tD Q).some
  let := (heartPairForget_exact tC P).1
  let := (heartPairForget_exact tC P).2
  let := (heartPairForget_exact tD Q).1
  let := (heartPairForget_exact tD Q).2
  let := (heartMap_exact tC tD F).1
  let := (heartMap_exact tC tD F).2
  let : ReflectsFiniteLimits (fixedPairHeartForget tD Q) :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  let : ReflectsFiniteColimits (fixedPairHeartForget tD Q) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  let i : fixedPairHeartForget tC P ⋙ heartMap tC tD F ≅
      fixedPairHeartMap tC tD P Q F α ⋙ fixedPairHeartForget tD Q := Iso.refl _
  let := preservesFiniteLimits_of_natIso i
  let := preservesFiniteColimits_of_natIso i
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (fixedPairHeartForget tD Q),
    preservesFiniteColimits_of_reflects_of_preserves _ (fixedPairHeartForget tD Q)⟩

private theorem heartPairForget_creates (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t]
    (A B : fixedPairHeart t P) (u : A ⟶ B) :
    Nonempty (CreatesLimit (parallelPair u 0) (fixedPairHeartForget t P)) ∧
      Nonempty (CreatesColimit (parallelPair u 0) (fixedPairHeartForget t P)) := by
  let := (heartPair_abelian t P).some
  let := (heartPairForget_exact t P).1
  let := (heartPairForget_exact t P).2
  exact ⟨⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩,
    ⟨createsColimitOfReflectsIsomorphismsOfPreserves⟩⟩

private noncomputable def heartPairDiagramIso (t : TStructure C) (P : C ⥤ C)
    [P.IsTExact t t] [P.Additive] (A B : fixedPairHeart t P) (u : A ⟶ B) :
    parallelPair ((heartMap t t P).map ((fixedPairHeartForget t P).map u)) 0 ≅
      parallelPair ((fixedPairHeartForget t P).map u) 0 :=
  parallelPairIsoMk (ObjectProperty.isoMk _ A.obj.str)
    (ObjectProperty.isoMk _ B.obj.str)
    (ObjectProperty.hom_ext _ u.hom.hom.h) (by simp)

private theorem heartPair_kernel (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t]
    (A B : fixedPairHeart t P) (u : A ⟶ B)
    (c : KernelFork ((fixedPairHeartForget t P).map u)) (hc : IsLimit c) :
    ∃! κ : P.obj c.pt.obj ≅ c.pt.obj,
      κ.hom ≫ c.ι.hom = P.map c.ι.hom ≫ A.obj.str.hom ∧
      κ.inv ≫ P.map c.ι.hom = c.ι.hom ≫ A.obj.str.inv := by
  let := (heartMap_exact t t P).1
  let hcP := c.mapIsLimit hc (heartMap t t P)
  let κ := IsLimit.conePointsIsoOfNatIso hcP hc (heartPairDiagramIso t P A B u)
  refine ⟨(t.heart.ι).mapIso κ, ⟨?_, ?_⟩, ?_⟩
  · exact congrArg (fun f ↦ f.hom)
      (IsLimit.conePointsIsoOfNatIso_hom_comp hcP hc
        (heartPairDiagramIso t P A B u) WalkingParallelPair.zero)
  · exact congrArg (fun f ↦ f.hom)
      (IsLimit.conePointsIsoOfNatIso_inv_comp hcP hc
        (heartPairDiagramIso t P A B u) WalkingParallelPair.zero)
  · intro κ' hκ'
    apply Iso.ext
    change (ObjectProperty.homMk κ'.hom : (c.map (heartMap t t P)).pt ⟶ c.pt).hom =
      κ.hom.hom
    apply congrArg (fun f : (c.map (heartMap t t P)).pt ⟶ c.pt ↦ f.hom)
    apply Fork.IsLimit.hom_ext hc
    apply ObjectProperty.hom_ext
    exact hκ'.1.trans (congrArg (fun f ↦ f.hom)
      (IsLimit.conePointsIsoOfNatIso_hom_comp hcP hc
        (heartPairDiagramIso t P A B u) WalkingParallelPair.zero)).symm

private theorem heartPair_cokernel (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t]
    (A B : fixedPairHeart t P) (u : A ⟶ B)
    (c : CokernelCofork ((fixedPairHeartForget t P).map u)) (hc : IsColimit c) :
    ∃! γ : P.obj c.pt.obj ≅ c.pt.obj,
      P.map c.π.hom ≫ γ.hom = B.obj.str.hom ≫ c.π.hom ∧
      c.π.hom ≫ γ.inv = B.obj.str.inv ≫ P.map c.π.hom := by
  let := (heartMap_exact t t P).2
  let hcP := c.mapIsColimit hc (heartMap t t P)
  let γ := IsColimit.coconePointsIsoOfNatIso hcP hc
    (heartPairDiagramIso t P A B u)
  refine ⟨(t.heart.ι).mapIso γ, ⟨?_, ?_⟩, ?_⟩
  · exact congrArg (fun f ↦ f.hom)
      (IsColimit.comp_coconePointsIsoOfNatIso_hom hcP hc
        (heartPairDiagramIso t P A B u) WalkingParallelPair.one)
  · exact congrArg (fun f ↦ f.hom)
      (IsColimit.comp_coconePointsIsoOfNatIso_inv hcP hc
        (heartPairDiagramIso t P A B u) WalkingParallelPair.one)
  · intro γ' hγ'
    apply Iso.ext
    change (ObjectProperty.homMk γ'.hom : (c.map (heartMap t t P)).pt ⟶ c.pt).hom =
      γ.hom.hom
    apply congrArg (fun f : (c.map (heartMap t t P)).pt ⟶ c.pt ↦ f.hom)
    apply Cofork.IsColimit.hom_ext hcP
    apply ObjectProperty.hom_ext
    exact hγ'.1.trans (congrArg (fun f ↦ f.hom)
      (IsColimit.comp_coconePointsIsoOfNatIso_hom hcP hc
        (heartPairDiagramIso t P A B u) WalkingParallelPair.one)).symm


/-- Transport, canonical cohomology comparison, and exactness on fixed-pair hearts.
Source: BBD 1.3.3–1.3.6 and 1.3.16–1.3.17; blueprint restriction and Part 2 of
`lem-zl-morphism-open-closed-reduction.proof.md`
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Proof plan (the node's twelve steps):
1. Naturality of α and equivariance of u show F(u) is equivariant for F(θ)α.
   Identity and composition laws are those of F (def-weil-endofunctor-fixed-pair-category).
2. Use lem-pod-texact-truncation-comparison, normalized by the truncation unit/counit.
   Compose its lower and upper comparisons, then the given shift comparison, to obtain e.
3. lem-pod-fixed-pair-postnikov-identifications supplies the lifted truncations and
   shifted cohomology, with structure Hᵃ(θ)e_P and carrier in the heart.
4. Naturality and composition of normalized truncation comparisons, together with
   CommShift coherence, give Hᵃ(η)e_F = e_G η_H and e_GF = e_G G(e_F).
5. Apply step 4 to α : QF ≅ FP and naturality to θ. The resulting equation says e_F
   is equivariant. Multiply by inverses for the asserted opposite direction. Naturality
   in equivariant arrows follows from naturality on carriers and faithful forgetting.
6. The transported composite has structure GF(θ)G(α)β. Step 4 gives composition,
   identity, and shift-compatible natural-isomorphism coherence of the comparisons.
7. By lem-weil-heart-short-exact-triangles, heart short exact sequences are triangles.
   Their images are triangles with heart terms; hence P, Q and F restrict exactly.
   lem-sp-exact-functor-preserves-homology gives preservation of kernels and cokernels.
8. The kernel universal property gives κ with κ;k = P(k);θ_A and its inverse λ with
   λ;P(k) = k;θ_A⁻¹. Cancellation proves inverse identities and equivariant factorization.
9. Dually construct γ with P(q);γ = θ_B;q and δ with q;δ = θ_B⁻¹;P(q).
   Epimorphism cancellation gives inverse identities and equivariant cokernel factors.
10. Addition and zero of arrows are inherited. Biproduct structure is the diagonal
    sum i_A θ_A P(p_A) + i_B θ_B P(p_B), with inverse diagonal sum using θ⁻¹.
11. Created kernels show a mono of pairs has monic carrier; created cokernels give
    the dual assertion. Normality in the heart and equivariant unique factors prove
    normality in pairs, so both full hearts are abelian (def-sp-abelian).
12. F(κ)α satisfies the defining Q-kernel equation, by naturality of α; similarly
    F(γ)α satisfies the cokernel equation. Uniqueness identifies both structures.
    The additive restriction therefore preserves kernels and cokernels and is exact. -/
theorem texact_fixedPair_heart_cohomology
    (tC : TStructure C) (tD : TStructure D)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (P : C ≌ C) (Q : D ≌ D)
    [P.functor.CommShift ℤ] [P.functor.IsTriangulated]
    [P.functor.IsTExact tC tC] [P.inverse.IsTExact tC tC]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated]
    [Q.functor.IsTExact tD tD] [Q.inverse.IsTExact tD tD]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (α : F ⋙ Q.functor ≅ P.functor ⋙ F) [α.hom.CommShift ℤ] :
    (∀ K : IsoAlgebra P.functor,
      ((IsoAlgebra.mapOfNatIso α).obj K).str = α.app K.carrier ≪≫ F.mapIso K.str) ∧
    (∀ (K L : IsoAlgebra P.functor) (u : K ⟶ L),
      ((IsoAlgebra.mapOfNatIso α).map u).hom.f = F.map u.hom.f) ∧
    (∀ m : ℤ, ∃ e :
        IsoAlgebra.mapOfNatIso α ⋙ fixedPairTruncLE tD Q.functor m ≅
          fixedPairTruncLE tC P.functor m ⋙ IsoAlgebra.mapOfNatIso α,
      ∀ K : IsoAlgebra P.functor,
        (e.hom.app K).hom.f = (F.eTruncLTIso tC tD (m + 1 : ℤ)).inv.app K.carrier) ∧
    (∀ m : ℤ, ∃ e :
        IsoAlgebra.mapOfNatIso α ⋙ fixedPairTruncGE tD Q.functor m ≅
          fixedPairTruncGE tC P.functor m ⋙ IsoAlgebra.mapOfNatIso α,
      ∀ K : IsoAlgebra P.functor,
        (e.hom.app K).hom.f = (F.eTruncGEIso tC tD m).inv.app K.carrier) ∧
    (∀ a : ℤ, ∃ e :
        IsoAlgebra.mapOfNatIso α ⋙ fixedPairCohomology tD Q.functor a ≅
          fixedPairCohomology tC P.functor a ⋙ IsoAlgebra.mapOfNatIso α,
      ∀ K : IsoAlgebra P.functor,
        (e.hom.app K).hom.f =
          (fixedPairCohomologyCarrierComparison tC tD F a K.carrier).inv) ∧
    Nonempty (Abelian (fixedPairHeart tC P.functor)) ∧
    Nonempty (Abelian (fixedPairHeart tD Q.functor)) ∧
    PreservesFiniteLimits (fixedPairHeartMap tC tD P.functor Q.functor F α) ∧
    PreservesFiniteColimits (fixedPairHeartMap tC tD P.functor Q.functor F α) ∧
    (∀ (A B : fixedPairHeart tC P.functor) (u : A ⟶ B),
      Nonempty (CreatesLimit (parallelPair u 0) (fixedPairHeartForget tC P.functor)) ∧
      Nonempty (CreatesColimit (parallelPair u 0) (fixedPairHeartForget tC P.functor))) ∧
    (∀ (A B : fixedPairHeart tD Q.functor) (u : A ⟶ B),
      Nonempty (CreatesLimit (parallelPair u 0) (fixedPairHeartForget tD Q.functor)) ∧
      Nonempty (CreatesColimit (parallelPair u 0) (fixedPairHeartForget tD Q.functor))) ∧
    (∀ (A B : fixedPairHeart tC P.functor) (u : A ⟶ B)
      (c : KernelFork ((fixedPairHeartForget tC P.functor).map u)) (_hc : IsLimit c),
      ∃! κ : P.functor.obj c.pt.obj ≅ c.pt.obj,
        κ.hom ≫ c.ι.hom = P.functor.map c.ι.hom ≫ A.obj.str.hom ∧
        κ.inv ≫ P.functor.map c.ι.hom = c.ι.hom ≫ A.obj.str.inv) ∧
    (∀ (A B : fixedPairHeart tC P.functor) (u : A ⟶ B)
      (c : CokernelCofork ((fixedPairHeartForget tC P.functor).map u))
      (_hc : IsColimit c),
      ∃! γ : P.functor.obj c.pt.obj ≅ c.pt.obj,
        P.functor.map c.π.hom ≫ γ.hom = B.obj.str.hom ≫ c.π.hom ∧
        c.π.hom ≫ γ.inv = B.obj.str.inv ≫ P.functor.map c.π.hom) ∧
    (∀ (A B : fixedPairHeart tD Q.functor) (u : A ⟶ B)
      (c : KernelFork ((fixedPairHeartForget tD Q.functor).map u)) (_hc : IsLimit c),
      ∃! κ : Q.functor.obj c.pt.obj ≅ c.pt.obj,
        κ.hom ≫ c.ι.hom = Q.functor.map c.ι.hom ≫ A.obj.str.hom ∧
        κ.inv ≫ Q.functor.map c.ι.hom = c.ι.hom ≫ A.obj.str.inv) ∧
    (∀ (A B : fixedPairHeart tD Q.functor) (u : A ⟶ B)
      (c : CokernelCofork ((fixedPairHeartForget tD Q.functor).map u))
      (_hc : IsColimit c),
      ∃! γ : Q.functor.obj c.pt.obj ≅ c.pt.obj,
        Q.functor.map c.π.hom ≫ γ.hom = B.obj.str.hom ≫ c.π.hom ∧
        c.π.hom ≫ γ.inv = B.obj.str.inv ≫ Q.functor.map c.π.hom) ∧
    (∀ (a : ℤ) (K : IsoAlgebra P.functor),
      tC.heart (((fixedPairCohomology tC P.functor a).obj K).carrier)) ∧
    (∀ (a : ℤ) (K : IsoAlgebra Q.functor),
      tD.heart (((fixedPairCohomology tD Q.functor a).obj K).carrier)) := by
  classical
  have hs (m a : ℤ) (K : C) :=
    truncationCohomologyComparison_square tC tD F _hC _hD tC tD _hC _hD
      P.functor Q.functor F α m a K
  have hF := heartPairMap_exact tC tD P.functor Q.functor F α
  refine ⟨fun K ↦ IsoAlgebra.mapOfNatIso_obj_str α K, fun _ _ _ ↦ rfl,
    ?_, ?_, ?_, heartPair_abelian tC P.functor, heartPair_abelian tD Q.functor,
    hF.1, hF.2, heartPairForget_creates tC P.functor,
    heartPairForget_creates tD Q.functor, heartPair_kernel tC P.functor,
    heartPair_cokernel tC P.functor, heartPair_kernel tD Q.functor,
    heartPair_cokernel tD Q.functor, ?_, ?_⟩
  · intro m
    exact ⟨liftComparison P.functor (tC.truncLE m) Q.functor (tD.truncLE m) F α
      (P.functor.eTruncLTIso tC tC (m + 1 : ℤ))
      (Q.functor.eTruncLTIso tD tD (m + 1 : ℤ))
      (F.eTruncLTIso tC tD (m + 1 : ℤ)) (fun K ↦ (hs m 0 K).1), fun _ ↦ rfl⟩
  · intro m
    exact ⟨liftComparison P.functor (tC.truncGE m) Q.functor (tD.truncGE m) F α
      (P.functor.eTruncGEIso tC tC m) (Q.functor.eTruncGEIso tD tD m)
      (F.eTruncGEIso tC tD m) (fun K ↦ (hs m 0 K).2.1), fun _ ↦ rfl⟩
  · intro a
    let e := Functor.isoWhiskerLeft (IsoAlgebra.mapOfNatIso α)
        (cohomologyLiftIso tD Q.functor a) ≪≫
      liftComparison P.functor (tC.truncGELE a a ⋙ shiftFunctor C a)
        Q.functor (tD.truncGELE a a ⋙ shiftFunctor D a) F α
        (truncationCohomologyComparison tC tC P.functor a)
        (truncationCohomologyComparison tD tD Q.functor a)
        (truncationCohomologyComparison tC tD F a) (fun K ↦ (hs 0 a K).2.2) ≪≫
      Functor.isoWhiskerRight (cohomologyLiftIso tC P.functor a).symm
        (IsoAlgebra.mapOfNatIso α)
    refine ⟨e, ?_⟩
    intro K
    change 𝟙 _ ≫ (fixedPairCohomologyCarrierComparison tC tD F a K.carrier).inv ≫
      F.map (𝟙 _) = _
    simp
  · intro a K
    exact (cohomology_comparison_pasting tC tC P.functor _hC _hC a K.carrier).1
  · intro a K
    exact (cohomology_comparison_pasting tD tD Q.functor _hD _hD a K.carrier).1



/-- Composition and identity coherence of the canonical fixed-pair comparison.
The isomorphism of the lifted composite functors has identity carrier; the displayed
cohomology equation determines composition coherence also in the fixed-pair category,
whose forgetful functor is faithful.
Source: BBD 1.3.3 and 1.3.16, node proof steps 4 and 6
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Proof: compose the two intertwiners with associators. Both lifted functors have structure
GF(θ)G(α)β and send an arrow to GF(u), so identity carriers give the lift comparison.
Naturality of the lower comparison at the upper one and normalization by the truncation
maps give the composite truncation comparison (lem-pod-texact-truncation-comparison).
Shift-addition coherence then gives the displayed cohomology equation. The identity
comparisons satisfy the defining truncation equations, so uniqueness makes them identity.
Faithfulness transfers these equations to the natural isomorphisms of fixed pairs. -/
theorem texact_fixedPair_cohomology_composition
    {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] [IsTriangulated E]
    (tC : TStructure C) (tD : TStructure D) (tE : TStructure E)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤) (_hE : tE.bounded = ⊤)
    (P : C ≌ C) (Q : D ≌ D) (R : E ≌ E)
    [P.functor.CommShift ℤ] [P.functor.IsTriangulated]
    [P.functor.IsTExact tC tC] [P.inverse.IsTExact tC tC]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated]
    [Q.functor.IsTExact tD tD] [Q.inverse.IsTExact tD tD]
    [R.functor.CommShift ℤ] [R.functor.IsTriangulated]
    [R.functor.IsTExact tE tE] [R.inverse.IsTExact tE tE]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tD tE]
    (α : F ⋙ Q.functor ≅ P.functor ⋙ F) [α.hom.CommShift ℤ]
    (β : G ⋙ R.functor ≅ Q.functor ⋙ G) [β.hom.CommShift ℤ] :
    (∃ c : IsoAlgebra.mapOfNatIso α ⋙ IsoAlgebra.mapOfNatIso β ≅
        IsoAlgebra.mapOfNatIso
          (fixedPairCompositeIntertwiner P.functor Q.functor R.functor F G α β),
      ∀ K : IsoAlgebra P.functor, (c.hom.app K).hom.f = 𝟙 (G.obj (F.obj K.carrier))) ∧
    (∀ (a : ℤ) (K : C),
      (fixedPairCompositeCohomologyComparison tC tD tE F G a K).hom =
        G.map (fixedPairCohomologyCarrierComparison tC tD F a K).hom ≫
          (fixedPairCohomologyCarrierComparison tD tE G a (F.obj K)).hom) ∧
    (∀ (a : ℤ) (K : C),
      (fixedPairIdentityCohomologyComparison tC a K).hom = 𝟙 _) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · let c : IsoAlgebra.mapOfNatIso α ⋙ IsoAlgebra.mapOfNatIso β ≅
        IsoAlgebra.mapOfNatIso
          (fixedPairCompositeIntertwiner P.functor Q.functor R.functor F G α β) :=
      NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
        (Algebra.isoMk (Iso.refl _) (by
          simp [fixedPairCompositeIntertwiner, IsoAlgebra.mapOfNatIso,
            Algebra.mapOfNatTrans, Functor.map_comp, Category.assoc])))
        (by
          intro K L u
          apply ObjectProperty.hom_ext
          apply Algebra.Hom.ext
          simp)
    exact ⟨c, fun K ↦ rfl⟩
  · intro a K
    exact truncationCohomologyComparison_comp tC tD F _hC _hD tE _hE G a K
  · intro a K
    exact truncationCohomologyComparison_id tC _hC a K


/-- Compatibility with shift-compatible natural isomorphisms of intertwining functors.
The lifted natural isomorphism has carrier η, and its cohomology square is the displayed
square; taking inverses gives the square for the direction in the main statement.
Source: BBD 1.3.3 and 1.3.16, node proof steps 4–6
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Proof: naturality of η at θ and its compatibility with α and α' give equivariance
of η_K, hence also of its inverse. Naturality gives a natural isomorphism of the lifts.
The normalized truncation comparisons are natural in η by
lem-pod-texact-truncation-comparison. Combine these two equations with η.CommShift to
get Hᵃ(η)e_F = e_F'η_H. Faithfulness gives the same equation for the lifts. -/
theorem texact_fixedPair_cohomology_natIso
    (tC : TStructure C) (tD : TStructure D)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (P : C ≌ C) (Q : D ≌ D)
    [P.functor.CommShift ℤ] [P.functor.IsTriangulated]
    [P.functor.IsTExact tC tC] [P.inverse.IsTExact tC tC]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated]
    [Q.functor.IsTExact tD tD] [Q.inverse.IsTExact tD tD]
    (F F' : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    [F'.CommShift ℤ] [F'.IsTriangulated] [F'.IsTExact tC tD]
    (α : F ⋙ Q.functor ≅ P.functor ⋙ F) [α.hom.CommShift ℤ]
    (α' : F' ⋙ Q.functor ≅ P.functor ⋙ F') [α'.hom.CommShift ℤ]
    (η : F ≅ F') [η.hom.CommShift ℤ]
    (_hη : ∀ K : C,
      Q.functor.map (η.hom.app K) ≫ α'.hom.app K =
        α.hom.app K ≫ η.hom.app (P.functor.obj K)) :
    (∃ e : IsoAlgebra.mapOfNatIso α ≅ IsoAlgebra.mapOfNatIso α',
      ∀ K : IsoAlgebra P.functor, (e.hom.app K).hom.f = η.hom.app K.carrier) ∧
    (∀ (a : ℤ) (K : C),
      η.hom.app ((tC.truncGELE a a ⋙ shiftFunctor C a).obj K) ≫
          (fixedPairCohomologyCarrierComparison tC tD F' a K).hom =
        (fixedPairCohomologyCarrierComparison tC tD F a K).hom ≫
          (tD.truncGELE a a ⋙ shiftFunctor D a).map (η.hom.app K)) := by
  classical
  refine ⟨?_, ?_⟩
  · let e : IsoAlgebra.mapOfNatIso α ≅ IsoAlgebra.mapOfNatIso α' :=
      NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
        (Algebra.isoMk (η.app K.carrier) (by
          change Q.functor.map (η.hom.app K.carrier) ≫
              (α'.hom.app K.carrier ≫ F'.map K.obj.str) =
            (α.hom.app K.carrier ≫ F.map K.obj.str) ≫ η.hom.app K.carrier
          rw [← Category.assoc, _hη, Category.assoc, ← η.hom.naturality,
            Category.assoc])))
        (by
          intro K L u
          apply ObjectProperty.hom_ext
          apply Algebra.Hom.ext
          exact η.hom.naturality u.hom.f)
    exact ⟨e, fun K ↦ rfl⟩
  · intro a K
    exact truncationCohomologyComparison_naturality tC tD F _hC _hD F' η.hom a K


end CategoryTheory.Triangulated.TStructure
