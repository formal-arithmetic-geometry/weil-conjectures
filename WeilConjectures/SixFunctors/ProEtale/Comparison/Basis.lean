/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# The affine ind-étale basis of the pro-étale site

For a scheme `X`, the affine pro-étale site `X.AffineProEt` is the full subcategory of the small
pro-étale site of `X` on the affine schemes which are cofiltered limits of affine étale
`X`-schemes. When `X` is affine these are exactly the affine schemes ind-étale over `X`
(`AlgebraicGeometry.ProEtale.AffineProEt.indEtale_appTop`). This is the basis of the
pro-étale site on which sheaves, their morphisms and the exactness of complexes of sheaves can
be tested.

## Main results

- `AlgebraicGeometry.ProEtale.AffineProEt.isBasis`: the basis properties of the affine
  ind-étale subsite (blueprint `lem-weil-pbc-ind-etale-basis`).
- `AlgebraicGeometry.ProEtale.isIso_of_isIso_rightDerivedFunctorPlus_sectionsFunctor`: a morphism
  in the bounded below derived category of pro-étale sheaves is an isomorphism if its derived
  sections over every object of the basis are isomorphisms
  (blueprint `lem-weil-pbc-basis-derived-detection`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Blueprint `def-weil-pbc-ind-etale-basis`: the affine ind-étale subsite.

The subsite is `AlgebraicGeometry.Scheme.AffineProEt X` with the topology
`AlgebraicGeometry.Scheme.AffineProEt.topology X` induced from the small pro-étale site. For
`X` affine, an object `W` of it is an affine scheme whose structure map is ind-étale on global
sections, that is, an affine scheme ind-étale over `X`. -/
lemma AffineProEt.indEtale_appTop {X : Scheme.{u}} [IsAffine X] (W : X.AffineProEt) :
    W.hom.appTop.hom.IndEtale :=
  Scheme.AffineProEt.indEtale_appTop_of_proAffineEtale W.prop

/-- Conversely to `AlgebraicGeometry.ProEtale.AffineProEt.indEtale_appTop`, the spectrum of an
ind-étale algebra over a ring `R` is an object of the affine ind-étale subsite of `Spec R`
(blueprint `def-weil-pbc-ind-etale-basis`). -/
lemma AffineProEt.proAffineEtale_Spec_map {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.IndEtale) : proAffineEtale (Spec.map f) :=
  proAffineEtale_Spec_iff.2 hf

/-- Blueprint `lem-weil-pbc-ind-etale-basis`: the ind-étale subsite is a basis.

1. every object of the pro-étale site of `X` is covered by objects of the affine ind-étale
   subsite (cover density);
2. every covering sieve of an object of the subsite contains a finite jointly surjective family
   of morphisms from objects of the subsite;
3. the subsite has fibre products, preserved by the inclusion into the pro-étale site;
4. restriction to the subsite is an equivalence between the categories of sheaves (with values
   in a category with enough limits), so that it determines sheaves and their morphisms and
   detects isomorphisms. -/
theorem AffineProEt.isBasis (X : Scheme.{u}) (A : Type*) [Category* A]
    [HasLimitsOfSize.{u, u + 1} A] :
    (AffineProEt.toProEt X).IsCoverDense (ProEt.topology X) ∧
    (∀ (W : X.AffineProEt) (T : Sieve W), T ∈ AffineProEt.topology X W →
      ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.AffineProEt) (f : ∀ i, V i ⟶ W),
        (∀ i, T (f i)) ∧ ∀ x : W.left, ∃ i, x ∈ Set.range ((f i).left.base)) ∧
    HasPullbacks X.AffineProEt ∧
    PreservesLimitsOfShape WalkingCospan (AffineProEt.toProEt X) ∧
    ((AffineProEt.toProEt X).sheafPushforwardContinuous A (AffineProEt.topology X)
      (ProEt.topology X)).IsEquivalence :=
  ⟨inferInstance, fun _ _ hT ↦ AffineProEt.exists_finite_jointly_surjective_of_mem_topology hT,
    inferInstance, inferInstance, inferInstance⟩

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- A cochain complex of pro-étale sheaves is exact in degree `n` if its complexes of sections
over all the objects of the affine pro-étale site are exact in degree `n`. -/
lemma exactAt_of_exactAt_sectionsFunctor {X : Scheme.{u}}
    (K : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) (n : ℤ)
    (h : ∀ W : X.AffineProEt, (((sectionsFunctor A ((AffineProEt.toProEt X).obj W)).mapHomologicalComplex
      _).obj K).ExactAt n) : K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff]
  refine ShortComplex.exact_of_exact_sectionsFunctor A _ fun W ↦ ?_
  have := h W
  rw [HomologicalComplex.exactAt_iff] at this
  exact this

/-- An object of the derived category is zero if it is the image of a complex which is exact in
every degree. -/
lemma _root_.DerivedCategory.isZero_Q_obj_of_exactAt {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) (h : ∀ n, K.ExactAt n) :
    IsZero (DerivedCategory.Q.obj K) := by
  have : K.IsGE 1 := by rw [CochainComplex.isGE_iff]; exact fun n _ ↦ h n
  have : K.IsLE 0 := by rw [CochainComplex.isLE_iff]; exact fun n _ ↦ h n
  exact DerivedCategory.TStructure.t.isZero _ 0 1

/-- Blueprint `lem-weil-pbc-basis-derived-detection`: derived sections on the basis detect
isomorphisms.

A morphism `φ` between bounded below complexes of pro-étale sheaves is an isomorphism if its
derived sections `RΓ(W, φ)` over every object `W` of the affine ind-étale basis are
isomorphisms. Indeed, represent the cone of `φ` by a bounded below complex `J` of injective
sheaves: its derived sections over `W` are computed by the complex of sections `Γ(W, J)`,
which is thus exact; exactness of a complex of sheaves is detected by its sections over the
basis, so `J` is exact and the cone vanishes. -/
theorem isIso_of_isIso_rightDerivedFunctorPlus_sectionsFunctor {X : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf (ProEt.topology X) A)} (φ : K ⟶ L)
    (h : ∀ W : X.AffineProEt, IsIso
      ((sectionsFunctor A ((AffineProEt.toProEt X).obj W)).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  obtain ⟨C, g, k, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  have hC (W : X.AffineProEt) : IsZero
      ((sectionsFunctor A ((AffineProEt.toProEt X).obj W)).rightDerivedFunctorPlus.obj C) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      ((sectionsFunctor A ((AffineProEt.toProEt X).obj W)).rightDerivedFunctorPlus.map_distinguished
        _ hT) (h W)
  obtain ⟨n, hn⟩ := C.2
  have : C.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff C n).1 hn
  obtain ⟨M, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso C n
  let M' := (InjectiveObject.ι _).mapCochainComplexPlus.obj M
  refine IsZero.of_iso ?_ e.symm
  rw [← DerivedCategory.Plus.ι.map_isZero_iff]
  refine IsZero.of_iso (DerivedCategory.isZero_Q_obj_of_exactAt M'.obj fun k ↦ ?_)
    ((DerivedCategory.quotientCompQhIso _).symm.app M'.obj)
  refine exactAt_of_exactAt_sectionsFunctor A _ _ fun W ↦ ?_
  let F := sectionsFunctor A ((AffineProEt.toProEt X).obj W)
  have h₁ : IsZero (DerivedCategory.Plus.Qh.obj
      (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient _).obj M'))) :=
    (hC W).of_iso (asIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj M')) ≪≫ F.rightDerivedFunctorPlus.mapIso e)
  have h₂ : IsZero (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj M'.obj)) :=
    (DerivedCategory.Plus.ι.map_isZero h₁).of_iso
      ((DerivedCategory.quotientCompQhIso _).app _)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (DerivedCategory.Plus.ι.map_isZero h₂).of_iso
    ((DerivedCategory.homologyFunctorFactors _ k).app _).symm

end AlgebraicGeometry.ProEtale
