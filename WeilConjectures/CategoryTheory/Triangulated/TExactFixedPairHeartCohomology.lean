/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.FixedPairTruncationCohomologyFunctors
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.CategoryTheory.Limits.Creates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-! # Exact hearts and cohomology of fixed pairs

Source: BBD 1.3.3--1.3.6 and 1.3.17; the fixed-pair calculations supplement the
restriction and Part 2 exactness paragraphs of the latest blueprint proof of
lem-zl-morphism-open-closed-reduction
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Only ordinary triangulated categories carry t-structures here. Fixed pairs and
fixed-pair hearts use the existing invertible-algebra category and full subcategories.
-/

@[expose] public noncomputable section

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
  {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E] [IsTriangulated E]

/-- The full subcategory of fixed pairs whose carrier lies in the heart.
Source: BBD 1.3.6, fixed-pair assembly in the restriction paragraph of
lem-zl-morphism-open-closed-reduction
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
abbrev fixedPairHeart (t : TStructure C) (P : C ⥤ C) :=
  ObjectProperty.FullSubcategory (fun K : IsoAlgebra P => t.heart K.carrier)

/-- Forget the invertible structure, retaining the ordinary-heart object and arrow.
Source: BBD 1.3.6, fixed-pair assembly in lem-zl-morphism-open-closed-reduction
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
def fixedPairHeartForget (t : TStructure C) (P : C ⥤ C) :
    fixedPairHeart t P ⥤ t.heart.FullSubcategory where
  obj A := ⟨A.obj.carrier, A.property⟩
  map u := ObjectProperty.homMk u.hom.hom.f

/-- Restrict the actual transport functor to the full fixed-pair hearts.
Source: BBD 1.3.17, Part 2 exactness in lem-zl-morphism-open-closed-reduction
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
def fixedPairHeartMap (tC : TStructure C) (tD : TStructure D)
    (P : C ⥤ C) (Q : D ⥤ D) (F : C ⥤ D) [F.IsTExact tC tD]
    (α : F ⋙ Q ≅ P ⋙ F) : fixedPairHeart tC P ⥤ fixedPairHeart tD Q :=
  ObjectProperty.lift (fun K : IsoAlgebra Q => tD.heart K.carrier)
    (ObjectProperty.ι (fun K : IsoAlgebra P => tC.heart K.carrier) ⋙
      IsoAlgebra.mapOfNatIso α) (fun A => by
        obtain ⟨hLE, hGE⟩ := (tC.mem_heart_iff A.obj.carrier).1 A.property
        exact (tD.mem_heart_iff _).2
          ⟨Functor.IsTExact.isLE_obj tC tD F A.obj.carrier 0,
            Functor.IsTExact.isGE_obj tC tD F A.obj.carrier 0⟩)

/-- The specified canonical cohomology comparison, evaluated on a carrier.
Source: BBD 1.3.3--1.3.6, the comparison formula of
 def-per-truncation-cohomology-comparison
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology). -/
abbrev fixedPairCohomologyCarrierComparison
    (tC : TStructure C) (tD : TStructure D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] (a : ℤ) (K : C) :=
  (truncationCohomologyComparison tC tD F a).app K

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




/-- Transport, canonical lifted comparisons, abelian fixed-pair hearts, exactness,
and creation of kernels and cokernels, including both structure and inverse equations.
Source: BBD 1.3.3--1.3.6 and 1.3.17; agent fixed-pair argument supplementing
lem-zl-morphism-open-closed-reduction, restriction and Part 2 exactness
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Proof plan:
Use IsoAlgebra.mapOfNatIso for the transported functor. Its existing object-structure and arrow
lemmas give the first two clauses exactly. Naturality of alpha supplies the algebra square, and
its carrier maps are F.map.

For upper and lower truncations use the corresponding two squares of
truncationCohomologyComparison_square, instantiated with U=P, V=Q and F'=F. The private
liftComparison construction turns each square into a natural isomorphism of transported fixed-
pair functors. On the forward component use the canonical comparison e_F, prove equivariance by
the square and naturality of e_F at theta, and then take the inverse. This gives precisely the
inverse canonical truncation carrier asserted.

Identify the composite fixedPairCohomology with transport by truncationCohomologyComparison
using an isomorphism with identity carriers. Expand the three transport structure maps and the
specified comparison: functoriality gives the same shifted double-truncation structure map.
Apply liftComparison to the cohomology square from truncationCohomologyComparison_square and
whisker by the two identity-carrier identifications. The resulting carrier is exactly the
inverse canonical cohomology comparison.

For every a the object truncGELE a a K has both bounds a; the shift by a puts it in the heart.
This is the heart clause already proved by cohomology_comparison_pasting. The carrier of lifted
cohomology is definitionally that shifted double truncation, giving both final clauses.

Restrict each t-exact functor R to the full ordinary hearts by heartMap, whose objects and
arrows are R on carriers. The two t-exactness fields prove preservation of heart objects, and
additivity follows from R.map_add. A short exact sequence in the heart extends to a
distinguished triangle by shortExact_iff_exists_distTriang. Apply R to that triangle and its
specified shift comparison, then apply the same characterization in the target heart. Thus the
restriction preserves short exact sequences. Functor.exact_tfae gives preservation of finite
limits and finite colimits, without completeness assumptions.

Construct explicitly the equivalence from fixedPairHeart t P to IsoAlgebra of the ordinary-heart
restriction of P. An object is sent to the same carrier in the heart with its same structure
isomorphism, and a map is sent to its same carrier intertwiner. The inverse forgets the heart
wrappers; unit and counit have identity carriers. Their naturality and the triangle identity
follow on carriers. IsoAlgebra.abelian applies to the exact additive ordinary-heart restriction
from the previous step, and abelianOfEquivalence transfers this abelian structure back to the
given fixedPairHeart category.

Under the explicit equivalence the given fixedPairHeartForget is definitionally the algebra
forgetful functor composed with the equivalence. The exact forgetful instances in the adopted
EndoFunctor library therefore give its preservation of finite limits and finite colimits. It
reflects isomorphisms because its composite with the ordinary-heart inclusion is the faithful
full-subcategory inclusion followed by IsoAlgebra.forget. The finite-limit and finite-colimit
reflection lemmas apply since the fixed-pair hearts now have those limits.

For a given kernel fork c in the ordinary heart, apply the exact restriction of P to obtain a
limiting kernel fork of P(u). The structure isomorphisms of A and B define a natural isomorphism
of parallel-pair diagrams. IsLimit.conePointsIsoOfNatIso gives the structure kappa on the
kernel. Its hom and inverse projection equations give exactly the two equations in the
statement. Any competing kappa has the same composite with the kernel inclusion, so
Fork.IsLimit.hom_ext proves uniqueness in the ordinary heart and hence on carriers.

Dually apply P to a given cokernel cofork and use the same diagram isomorphism.
IsColimit.coconePointsIsoOfNatIso gives its structure gamma; its coprojection equations give
both the asserted hom and inverse equations. Cofork.IsColimit.hom_ext applied to the mapped
cofork proves uniqueness. These constructions work for an arbitrary universal fork or cofork,
not merely the chosen kernel or cokernel.

The abelian fixed-pair hearts have kernels and cokernels. Since the forgetful functor preserves
these limits and colimits and reflects isomorphisms,
createsLimitOfReflectsIsomorphismsOfPreserves and its colimit analogue give creation of every
parallel pair (u,0) required in the statement. No infinite limit or colimit is assumed.

The composite of fixedPairHeartMap with target forgetting is definitionally source forgetting
followed by heartMap of F. Both factors are exact by the preceding steps. Target forgetting
reflects finite limits and finite colimits, so preservesFiniteLimits_of_reflects_of_preserves
and its colimit analogue prove both required preservation statements for fixedPairHeartMap.

Retain the existing complete composition and natural-isomorphism coherence proofs. Identity
carriers identify the two composite transport functors; eta components identify compatible
transports. The canonical carrier equations use truncationCohomologyComparison_comp,
truncationCohomologyComparison_id and truncationCohomologyComparison_naturality. Faithful
forgetting checks naturality and the algebra squares.
-/
theorem texact_fixedPair_heart_cohomology (tC : TStructure C) (tD : TStructure D) (_hC :
    tC.bounded = ⊤) (_hD : tD.bounded = ⊤) (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact tC tC] [P.inverse.IsTExact tC tC]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact tD tD]
    [Q.inverse.IsTExact tD tD] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (α : F ⋙ Q.functor ≅ P.functor ⋙ F) [α.hom.CommShift ℤ] : (∀ K : IsoAlgebra P.functor,
    ((IsoAlgebra.mapOfNatIso α).obj K).str = α.app K.carrier ≪≫ F.mapIso K.str) ∧ (∀ (K L :
    IsoAlgebra P.functor) (u : K ⟶ L), ((IsoAlgebra.mapOfNatIso α).map u).hom.f = F.map u.hom.f)
    ∧ (∀ m : ℤ, ∃ e : IsoAlgebra.mapOfNatIso α ⋙ fixedPairTruncLE tD Q.functor m ≅
    fixedPairTruncLE tC P.functor m ⋙ IsoAlgebra.mapOfNatIso α, ∀ K : IsoAlgebra P.functor,
    (e.hom.app K).hom.f = (F.eTruncLTIso tC tD (m + 1 : ℤ)).inv.app K.carrier) ∧ (∀ m : ℤ, ∃ e :
    IsoAlgebra.mapOfNatIso α ⋙ fixedPairTruncGE tD Q.functor m ≅ fixedPairTruncGE tC P.functor m
    ⋙ IsoAlgebra.mapOfNatIso α, ∀ K : IsoAlgebra P.functor, (e.hom.app K).hom.f = (F.eTruncGEIso
    tC tD m).inv.app K.carrier) ∧ (∀ a : ℤ, ∃ e : IsoAlgebra.mapOfNatIso α ⋙ fixedPairCohomology
    tD Q.functor a ≅ fixedPairCohomology tC P.functor a ⋙ IsoAlgebra.mapOfNatIso α, ∀ K :
    IsoAlgebra P.functor, (e.hom.app K).hom.f = (fixedPairCohomologyCarrierComparison tC tD F a
    K.carrier).inv) ∧ Nonempty (Abelian (fixedPairHeart tC P.functor)) ∧ Nonempty (Abelian
    (fixedPairHeart tD Q.functor)) ∧ PreservesFiniteLimits (fixedPairHeartMap tC tD P.functor
    Q.functor F α) ∧ PreservesFiniteColimits (fixedPairHeartMap tC tD P.functor Q.functor F α) ∧
    (∀ (A B : fixedPairHeart tC P.functor) (u : A ⟶ B), Nonempty (CreatesLimit (parallelPair u
    0) (fixedPairHeartForget tC P.functor)) ∧ Nonempty (CreatesColimit (parallelPair u 0)
    (fixedPairHeartForget tC P.functor))) ∧ (∀ (A B : fixedPairHeart tD Q.functor) (u : A ⟶ B),
    Nonempty (CreatesLimit (parallelPair u 0) (fixedPairHeartForget tD Q.functor)) ∧ Nonempty
    (CreatesColimit (parallelPair u 0) (fixedPairHeartForget tD Q.functor))) ∧ (∀ (A B :
    fixedPairHeart tC P.functor) (u : A ⟶ B) (c : KernelFork ((fixedPairHeartForget tC
    P.functor).map u)) (_hc : IsLimit c), ∃! κ : P.functor.obj c.pt.obj ≅ c.pt.obj, κ.hom ≫
    c.ι.hom = P.functor.map c.ι.hom ≫ A.obj.str.hom ∧ κ.inv ≫ P.functor.map c.ι.hom = c.ι.hom ≫
    A.obj.str.inv) ∧ (∀ (A B : fixedPairHeart tC P.functor) (u : A ⟶ B) (c : CokernelCofork
    ((fixedPairHeartForget tC P.functor).map u)) (_hc : IsColimit c), ∃! γ : P.functor.obj
    c.pt.obj ≅ c.pt.obj, P.functor.map c.π.hom ≫ γ.hom = B.obj.str.hom ≫ c.π.hom ∧ c.π.hom ≫
    γ.inv = B.obj.str.inv ≫ P.functor.map c.π.hom) ∧ (∀ (A B : fixedPairHeart tD Q.functor) (u :
    A ⟶ B) (c : KernelFork ((fixedPairHeartForget tD Q.functor).map u)) (_hc : IsLimit c), ∃! κ
    : Q.functor.obj c.pt.obj ≅ c.pt.obj, κ.hom ≫ c.ι.hom = Q.functor.map c.ι.hom ≫ A.obj.str.hom
    ∧ κ.inv ≫ Q.functor.map c.ι.hom = c.ι.hom ≫ A.obj.str.inv) ∧ (∀ (A B : fixedPairHeart tD
    Q.functor) (u : A ⟶ B) (c : CokernelCofork ((fixedPairHeartForget tD Q.functor).map u)) (_hc
    : IsColimit c), ∃! γ : Q.functor.obj c.pt.obj ≅ c.pt.obj, Q.functor.map c.π.hom ≫ γ.hom =
    B.obj.str.hom ≫ c.π.hom ∧ c.π.hom ≫ γ.inv = B.obj.str.inv ≫ Q.functor.map c.π.hom) ∧ (∀ (a :
    ℤ) (K : IsoAlgebra P.functor), tC.heart (((fixedPairCohomology tC P.functor a).obj
    K).carrier)) ∧ (∀ (a : ℤ) (K : IsoAlgebra Q.functor), tD.heart (((fixedPairCohomology tD
    Q.functor a).obj K).carrier)) := by
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

variable (tC : TStructure C) (tD : TStructure D)
  (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
  (P : C ≌ C) (Q : D ≌ D)
  [P.functor.CommShift ℤ] [P.functor.IsTriangulated]
  [P.functor.IsTExact tC tC] [P.inverse.IsTExact tC tC]
  [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated]
  [Q.functor.IsTExact tD tD] [Q.inverse.IsTExact tD tD]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
  (α : F ⋙ Q.functor ≅ P.functor ⋙ F) [α.hom.CommShift ℤ]

include _hC _hD in
/-- The normalized lifted cohomology comparisons commute with composition.
The transport comparison has identity carriers, and the equation is in fixed pairs.
Source: BBD 1.3.3 and 1.3.17, fixed-pair pasting in the restriction paragraph of
lem-zl-morphism-open-closed-reduction
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Proof: use the canonical comparison for F, G and their composite. Lift the square
from lem-a1-cohomology-comparison-pasting using naturality at the structure map.
The composite transport isomorphism is IsoAlgebra.mapOfNatIsoCompIso with identity
carriers. After faithful forgetting, its asserted equation is the inverse of
truncationCohomologyComparison_comp. Thus the equation holds in fixed pairs. -/
theorem texact_fixedPair_cohomology_composition
    (tE : TStructure E) (_hE : tE.bounded = ⊤) (R : E ≌ E)
    [R.functor.CommShift ℤ] [R.functor.IsTriangulated]
    [R.functor.IsTExact tE tE] [R.inverse.IsTExact tE tE]
    (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tD tE]
    (β : G ⋙ R.functor ≅ Q.functor ⋙ G) [β.hom.CommShift ℤ] (a : ℤ) :
    ∃ (eF : IsoAlgebra.mapOfNatIso α ⋙ fixedPairCohomology tD Q.functor a ≅
        fixedPairCohomology tC P.functor a ⋙ IsoAlgebra.mapOfNatIso α)
      (eG : IsoAlgebra.mapOfNatIso β ⋙ fixedPairCohomology tE R.functor a ≅
        fixedPairCohomology tD Q.functor a ⋙ IsoAlgebra.mapOfNatIso β)
      (eFG : IsoAlgebra.mapOfNatIso (IsoAlgebra.compCommIso α β) ⋙
          fixedPairCohomology tE R.functor a ≅
        fixedPairCohomology tC P.functor a ⋙
          IsoAlgebra.mapOfNatIso (IsoAlgebra.compCommIso α β))
      (c : IsoAlgebra.mapOfNatIso α ⋙ IsoAlgebra.mapOfNatIso β ≅
        IsoAlgebra.mapOfNatIso (IsoAlgebra.compCommIso α β)),
      (∀ K : IsoAlgebra P.functor,
        (eF.hom.app K).hom.f = (truncationCohomologyComparison tC tD F a).inv.app K.carrier) ∧
      (∀ L : IsoAlgebra Q.functor,
        (eG.hom.app L).hom.f = (truncationCohomologyComparison tD tE G a).inv.app L.carrier) ∧
      (∀ K : IsoAlgebra P.functor, (eFG.hom.app K).hom.f =
        (truncationCohomologyComparison tC tE (F ⋙ G)
          (hF := cohomologyComparison_compTExact tC tD tE F G) a).inv.app K.carrier) ∧
      (∀ K : IsoAlgebra P.functor, (c.hom.app K).hom.f = 𝟙 _) ∧
      (∀ K : IsoAlgebra P.functor,
        eFG.hom.app K =
          (fixedPairCohomology tE R.functor a).map (c.inv.app K) ≫
          eG.hom.app ((IsoAlgebra.mapOfNatIso α).obj K) ≫
          (IsoAlgebra.mapOfNatIso β).map (eF.hom.app K) ≫
          c.hom.app ((fixedPairCohomology tC P.functor a).obj K)) := by
  let := cohomologyComparison_compTExact tC tD tE F G
  have : (IsoAlgebra.compCommIso α β).hom.CommShift ℤ := by
    dsimp [IsoAlgebra.compCommIso]
    infer_instance
  obtain ⟨eF, heF⟩ :=
    (texact_fixedPair_heart_cohomology tC tD _hC _hD P Q F α).2.2.2.2.1 a
  obtain ⟨eG, heG⟩ :=
    (texact_fixedPair_heart_cohomology tD tE _hD _hE Q R G β).2.2.2.2.1 a
  obtain ⟨eFG, heFG⟩ := (texact_fixedPair_heart_cohomology tC tE _hC _hE P R
    (F ⋙ G) (IsoAlgebra.compCommIso α β)).2.2.2.2.1 a
  let c := IsoAlgebra.mapOfNatIsoCompIso α β
  refine ⟨eF, eG, eFG, c, heF, heG, heFG, fun _ ↦ rfl, ?_⟩
  intro K
  apply (IsoAlgebra.forget R.functor).map_injective
  change (eFG.hom.app K).hom.f =
    ((fixedPairCohomology tE R.functor a).map (c.inv.app K)).hom.f ≫
      (eG.hom.app ((IsoAlgebra.mapOfNatIso α).obj K)).hom.f ≫
      G.map (eF.hom.app K).hom.f ≫
      (c.hom.app ((fixedPairCohomology tC P.functor a).obj K)).hom.f
  have hc : (c.inv.app K).hom.f = 𝟙 _ := rfl
  have hmap : ((fixedPairCohomology tE R.functor a).map (c.inv.app K)).hom.f = 𝟙 _ := by
    change (tE.truncGELE a a ⋙ shiftFunctor E a).map (c.inv.app K).hom.f = _
    rw [hc, Functor.map_id]
    rfl
  erw [hmap, Category.id_comp, show
    (c.hom.app ((fixedPairCohomology tC P.functor a).obj K)).hom.f = 𝟙 _ from rfl,
    Category.comp_id, heFG, heG, heF]
  have hcomp :
      (truncationCohomologyComparison tC tE (F ⋙ G) a).app K.carrier =
        G.mapIso ((truncationCohomologyComparison tC tD F a).app K.carrier) ≪≫
          (truncationCohomologyComparison tD tE G a).app (F.obj K.carrier) :=
    Iso.ext (truncationCohomologyComparison_comp tC tD F _hC _hD tE _hE G a K.carrier)
  exact congrArg Iso.inv hcomp

include _hC _hD in
/-- Shift-compatible isomorphisms of intertwining functors preserve the normalized
cohomology comparison. The lifted transformation has exactly the given carriers.
Source: BBD 1.3.3 and 1.3.17, fixed-pair naturality in the restriction paragraph of
lem-zl-morphism-open-closed-reduction
(blueprint: lem-zl-texact-fixed-pair-heart-cohomology).

Proof: IsoAlgebra.mapOfNatIsoIsoOfIso lifts eta using the assumed intertwiner
square. Lift the canonical cohomology comparisons as in the main theorem.
Faithful forgetting reduces the displayed square to the inverse form of
truncationCohomologyComparison_naturality, which uses eta's shift compatibility.
The normalizations identify all carriers with the specified canonical maps. -/
theorem texact_fixedPair_cohomology_natIso
    (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tC tD]
    (β : G ⋙ Q.functor ≅ P.functor ⋙ G) [β.hom.CommShift ℤ]
    (η : F ≅ G) [η.hom.CommShift ℤ]
    (hη : Functor.whiskerRight η.hom Q.functor ≫ β.hom =
      α.hom ≫ Functor.whiskerLeft P.functor η.hom) (a : ℤ) :
    ∃ (eF : IsoAlgebra.mapOfNatIso α ⋙ fixedPairCohomology tD Q.functor a ≅
        fixedPairCohomology tC P.functor a ⋙ IsoAlgebra.mapOfNatIso α)
      (eG : IsoAlgebra.mapOfNatIso β ⋙ fixedPairCohomology tD Q.functor a ≅
        fixedPairCohomology tC P.functor a ⋙ IsoAlgebra.mapOfNatIso β)
      (d : IsoAlgebra.mapOfNatIso α ≅ IsoAlgebra.mapOfNatIso β),
      (∀ K : IsoAlgebra P.functor,
        (eF.hom.app K).hom.f = (truncationCohomologyComparison tC tD F a).inv.app K.carrier) ∧
      (∀ K : IsoAlgebra P.functor,
        (eG.hom.app K).hom.f = (truncationCohomologyComparison tC tD G a).inv.app K.carrier) ∧
      (∀ K : IsoAlgebra P.functor, (d.hom.app K).hom.f = η.hom.app K.carrier) ∧
      (∀ K : IsoAlgebra P.functor,
        (fixedPairCohomology tD Q.functor a).map (d.hom.app K) ≫ eG.hom.app K =
          eF.hom.app K ≫ d.hom.app ((fixedPairCohomology tC P.functor a).obj K)) := by
  obtain ⟨eF, heF⟩ :=
    (texact_fixedPair_heart_cohomology tC tD _hC _hD P Q F α).2.2.2.2.1 a
  obtain ⟨eG, heG⟩ :=
    (texact_fixedPair_heart_cohomology tC tD _hC _hD P Q G β).2.2.2.2.1 a
  let d := IsoAlgebra.mapOfNatIsoIsoOfIso η hη
  refine ⟨eF, eG, d, heF, heG, fun _ ↦ rfl, ?_⟩
  intro K
  apply (IsoAlgebra.forget Q.functor).map_injective
  change (tD.truncGELE a a ⋙ shiftFunctor D a).map (η.hom.app K.carrier) ≫
      (eG.hom.app K).hom.f =
    (eF.hom.app K).hom.f ≫ η.hom.app
      ((tC.truncGELE a a ⋙ shiftFunctor C a).obj K.carrier)
  rw [heF, heG]
  have hn := truncationCohomologyComparison_naturality tC tD F _hC _hD G η.hom a K.carrier
  apply (cancel_epi ((truncationCohomologyComparison tC tD F a).hom.app K.carrier)).1
  simp only [← Category.assoc]
  rw [← hn]
  simp

end CategoryTheory.Triangulated.TStructure
