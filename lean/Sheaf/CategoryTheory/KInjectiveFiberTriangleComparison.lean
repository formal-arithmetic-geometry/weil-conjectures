/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Unit-normalized K-injective mapping-fibre comparisons

Source: Stacks Project, Derived Categories, Tags 090X, 070K, 070Y and 05SU;
blueprint main-20261015, `prop-weil-pbc-direct-image-limits`, applying direct image to
Roos triangles (blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

The fibre triangle is the inverse rotation of Mathlib's signed cone triangle.
Mathlib orders the cone coordinates as `(x,y)`; in the node's order `(y,x)` its
shift by -1 has differential `(-dy - ux, dx)`. All comparisons below are constructed
from the existing cone, shift and biproduct comparisons, without exactness of `G`.
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The triangle `(Cone(u)[-1], P, P; r, u, b)`, with `r(y,x)=x` and `b(z)=(z,0)`.
Source: Stacks, Tag 090X, inverse rotation of the signed cone triangle
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable abbrev kInjectiveFiberTriangle {P : CochainComplex A ℤ} (u : P ⟶ P) :
    Triangle (CochainComplex A ℤ) :=
  (CochainComplex.mappingCone.triangle u).invRotate

/-- The diagonal map of fibre triangles induced by a commuting endomorphism square.
Source: Stacks, Tag 090X, cone-coordinate comparison
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveFiberTriangleMap
    {P R : CochainComplex A ℤ} (u : P ⟶ P) (v : R ⟶ R)
    (a : P ⟶ R) (ha : u ≫ a = a ≫ v) :
    kInjectiveFiberTriangle u ⟶ kInjectiveFiberTriangle v :=
  (invRotate (CochainComplex A ℤ)).map
    (CochainComplex.mappingCone.triangleMap u v a a ha)

/-- The actual diagonal comparison: canonical additive cone comparison followed by
`diag(c,c)`, with inverse rotation supplying the canonical shift identification.
Its first component is the node's `theta`, with coordinates `(y,x) ↦ (cy,cx)`.
Source: Stacks, Tag 090X (blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveFiberChainComparison (G : A ⥤ B) [G.Additive]
    {P : CochainComplex A ℤ} {P' : CochainComplex B ℤ}
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangle.obj
      (kInjectiveFiberTriangle u) ⟶ kInjectiveFiberTriangle u' :=
  (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangleInvRotateIso.inv.app
      (CochainComplex.mappingCone.triangle u) ≫
    (invRotate (CochainComplex B ℤ)).map
      ((CochainComplex.mappingCone.mapTriangleIso u G).hom ≫
        CochainComplex.mappingCone.triangleMap
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map u) u' c.hom c.hom hc)

private theorem leftKan_of_bijective
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (F : C ⥤ E) (R : D ⥤ E) (η : F ⟶ Q ⋙ R)
    (h : ∀ S : D ⥤ E,
      Function.Bijective (fun β : R ⟶ S ↦ η ≫ Functor.whiskerLeft Q β)) :
    R.IsLeftKanExtension η := by
  classical
  let desc (e : Functor.LeftExtension Q F) : Functor.LeftExtension.mk R η ⟶ e :=
    StructuredArrow.homMk ((h e.right).surjective e.hom).choose
      ((h e.right).surjective e.hom).choose_spec
  refine ⟨⟨IsInitial.ofUniqueHom desc ?_⟩⟩
  intro e f
  apply StructuredArrow.hom_ext
  apply (h e.right).injective
  exact f.w.trans ((h e.right).surjective e.hom).choose_spec.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem leftKan_postcomp_equivalence
    {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    (Q : C ⥤ D) (F : C ⥤ E) (R : D ⥤ E) (η : F ⟶ Q ⋙ R)
    [R.IsLeftKanExtension η] (S : E ⥤ E') [S.IsEquivalence] :
    (R ⋙ S).IsLeftKanExtension
      (Functor.whiskerRight η S ≫ (Functor.associator Q R S).hom) := by
  let P := Functor.LeftExtension.postcompose₂ Q F S
  have : P.IsEquivalence := by
    dsimp [P, Functor.LeftExtension.postcompose₂]
    have := NatIso.isIso_of_isIso_app
      ({ app X := (Functor.associator Q X S).hom } :
        (Functor.whiskeringLeft C D E).obj Q ⋙
            (Functor.whiskeringRight C E E').obj S ⟶
          (Functor.whiskeringRight D E E').obj S ⋙
            (Functor.whiskeringLeft C D E').obj Q)
    apply StructuredArrow.isEquivalenceMap₂
  exact ⟨⟨IsInitial.equivOfIso (Functor.LeftExtension.postcompose₂ObjMkIso S η)
    ((IsInitial.isInitialIffObj P _) (R.isUniversalOfIsLeftKanExtension η))⟩⟩

private theorem fiber_isKInjective {P : CochainComplex A ℤ} (u : P ⟶ P)
    (hP : P.IsKInjective) : (kInjectiveFiberTriangle u).obj₁.IsKInjective := by
  have hC : (CochainComplex.mappingCone u).IsKInjective := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal.ext_of_isTriangulatedClosed₃
      (CochainComplex.mappingCone.triangleh u)
      (HomotopyCategory.mappingCone_triangleh_distinguished u)
      (CochainComplex.IsKInjective.rightOrthogonal P)
      (CochainComplex.IsKInjective.rightOrthogonal P)
  exact inferInstanceAs ((CochainComplex.mappingCone u)⟦(-1 : ℤ)⟧).IsKInjective

private theorem cone_map_isIso {P R : CochainComplex A ℤ} (u : P ⟶ P) (v : R ⟶ R)
    (c : P ≅ R) (hc : u ≫ c.hom = c.hom ≫ v) :
    IsIso (CochainComplex.mappingCone.map u v c.hom c.hom hc) := by
  let hi : v ≫ c.inv = c.inv ≫ u := by
    apply (cancel_epi c.hom).mp
    rw [← Category.assoc, ← hc]
    simp
  refine ⟨CochainComplex.mappingCone.map v u c.inv c.inv hi, ?_, ?_⟩
  · rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id u
  · rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id v

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem cone_map_naturality (G : A ⥤ B) [G.Additive]
    {P R : CochainComplex A ℤ} (u : P ⟶ P) (v : R ⟶ R)
    (a : P ⟶ R) (ha : u ≫ a = a ≫ v) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCone.map u v a a ha) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso v G).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso u G).hom ≫
        CochainComplex.mappingCone.map
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map u)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
          (by
            simpa only [← Functor.map_comp] using
              congrArg (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ha) := by
  apply (cancel_epi (CochainComplex.mappingCone.mapHomologicalComplexIso u G).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext n
  dsimp [CochainComplex.mappingCone.mapHomologicalComplexIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso']
  simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
    CochainComplex.mappingCone.map]
  simp only [← G.map_comp_assoc]
  simp [-Functor.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fiber_chain_hom₂ (G : A ⥤ B) [G.Additive]
    {P : CochainComplex A ℤ} {P' : CochainComplex B ℤ}
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    (kInjectiveFiberChainComparison G u u' c hc).hom₂ = c.hom := by
  simp [kInjectiveFiberChainComparison, CochainComplex.mappingCone.mapTriangleIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fiber_chain_hom₃ (G : A ⥤ B) [G.Additive]
    {P : CochainComplex A ℤ} {P' : CochainComplex B ℤ}
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    (kInjectiveFiberChainComparison G u u' c hc).hom₃ = c.hom := by
  simp [kInjectiveFiberChainComparison, CochainComplex.mappingCone.mapTriangleIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fiber_chain_isIso (G : A ⥤ B) [G.Additive]
    {P : CochainComplex A ℤ} {P' : CochainComplex B ℤ}
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    IsIso (kInjectiveFiberChainComparison G u u' c hc) := by
  have hi := cone_map_isIso
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map u) u' c hc
  have : IsIso (CochainComplex.mappingCone.triangleMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map u) u' c.hom c.hom hc) :=
    Triangle.isIso_of_isIsos _ (by dsimp; infer_instance) (by dsimp; infer_instance) hi
  unfold kInjectiveFiberChainComparison
  infer_instance

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The unit normalization, spelling out both localization-shift identifications.
Source: Stacks, Tag 05SU, normalized by the universal unit of Tags 070K/070Y
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
def IsUnitNormalizedKInjectiveShift (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ)) : Prop :=
  ∀ K : CochainComplex A ℤ,
    η.app (K⟦(1 : ℤ)⟧) ≫
        RG.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
        σ.hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          (((G.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (η.app K)⟦(1 : ℤ)⟧'

/-- Inverse of the derived unit at a computing K-injective object. Its data is the
inverse of an isomorphism, not a choice of an arbitrary comparison.
Source: Stacks, Tag 070Y (blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveInverseUnit (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    (K : CochainComplex A ℤ) (hK : K.IsKInjective) :
    RG.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (@asIso _ _ _ _ (η.app K) (hη K hK)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem inverse_unit_naturality (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    {K L : CochainComplex A ℤ} (hK : K.IsKInjective) (hL : L.IsKInjective)
    (f : K ⟶ L) :
    RG.map (DerivedCategory.Q.map f) ≫ (kInjectiveInverseUnit G RG η hη L hL).hom =
      (kInjectiveInverseUnit G RG η hη K hK).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have : IsIso (η.app K) := hη K hK
  have : IsIso (η.app L) := hη L hL
  change RG.map (DerivedCategory.Q.map f) ≫ inv (η.app L) =
    inv (η.app K) ≫ DerivedCategory.Q.map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  apply (cancel_epi (η.app K)).mp
  have hn := η.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn]
  simp

/-- The image of the localized fibre triangle using precisely the shift `σ`.
Source: Stacks, Tags 090X and 05SU
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveDerivedFiberTriangle
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    {P : CochainComplex A ℤ} (u : P ⟶ P) : Triangle (DerivedCategory B) :=
  Triangle.mk
    (RG.map (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u)).mor₁)
    (RG.map (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u)).mor₂)
    (RG.map (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u)).mor₃ ≫
      σ.hom.app (DerivedCategory.Q.obj (kInjectiveFiberTriangle u).obj₁))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- There is exactly one natural shift isomorphism normalized by the universal unit,
for every complex, including complexes which are not K-injective.
Source: Stacks, Tags 05SU, 070K and 070Y
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

Proof: the universal-unit bijections say that RG is a left Kan extension along Q.
Precomposition by the complex shift and transport along the Q-shift isomorphism
make shift followed by RG a left Kan extension of the shifted source functor.
Postcomposition by the derived shift equivalence makes RG followed by shift a
left Kan extension of the source followed by shift. The canonical termwise and
localization shift comparisons identify their source functors. Uniqueness of Kan
extensions gives sigma; its factorization equation is the required normalization
at every complex. Kan-extension hom-ext applied to the same equation proves
uniqueness. -/
theorem existsUnique_unitNormalizedKInjectiveShift
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (G : A ⥤ B) [G.Additive]
    (hG : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hUniversal : ∀ F : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun β : RG ⟶ F ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K)) :
    ∃! σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ),
      IsUnitNormalizedKInjectiveShift G RG η σ := by
  classical
  have _ := hA
  have _ := hG
  have _ := hη
  clear hA hG hη
  let M := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let QA : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  let T := shiftFunctor (CochainComplex A ℤ) (1 : ℤ)
  let S := shiftFunctor (DerivedCategory A) (1 : ℤ)
  let V := shiftFunctor (DerivedCategory B) (1 : ℤ)
  have : RG.IsLeftKanExtension η := leftKan_of_bijective QA (M ⋙ QB) RG η hUniversal
  let α : T ⋙ (M ⋙ QB) ⟶ QA ⋙ (S ⋙ RG) :=
    Functor.whiskerLeft T η ≫
      Functor.whiskerRight (QA.commShiftIso (1 : ℤ)).hom RG
  have hα : (S ⋙ RG).IsLeftKanExtension α := by
    have h := (Functor.isLeftKanExtension_iff_precomp RG T η).mp
      (inferInstance : RG.IsLeftKanExtension η)
    convert (Functor.isLeftKanExtension_iff_postcomp₁ S
      (QA.commShiftIso (1 : ℤ)).symm
      (Functor.whiskerLeft T η ≫ (Functor.associator T QA RG).inv)).mp h using 1
    ext K
    simp [α, Category.assoc, QA, T, S]
  let β : (M ⋙ QB) ⋙ V ⟶ QA ⋙ (RG ⋙ V) := Functor.whiskerRight η V
  have hβ : (RG ⋙ V).IsLeftKanExtension β := by
    convert leftKan_postcomp_equivalence QA (M ⋙ QB) RG η V using 1
    ext K
    simp [β]
  let i : T ⋙ (M ⋙ QB) ≅ (M ⋙ QB) ⋙ V :=
    (Functor.associator T M QB).symm ≪≫
      Functor.isoWhiskerRight (M.commShiftIso (1 : ℤ)) QB ≪≫
      Functor.associator M (shiftFunctor (CochainComplex B ℤ) (1 : ℤ)) QB ≪≫
      Functor.isoWhiskerLeft M (QB.commShiftIso (1 : ℤ)) ≪≫
      (Functor.associator M QB V).symm
  let σ := Functor.leftKanExtensionUniqueOfIso (S ⋙ RG) α i (RG ⋙ V) β
  have hs : IsUnitNormalizedKInjectiveShift G RG η σ := by
    intro K
    simpa [α, β, σ, i, M, QA, QB, T, S, V,
      IsUnitNormalizedKInjectiveShift, Category.assoc] using
      NatTrans.congr_app
        (Functor.descOfIsLeftKanExtension_fac (S ⋙ RG) α (RG ⋙ V) (i.hom ≫ β)) K
  refine ⟨σ, hs, ?_⟩
  intro τ hτ
  apply Iso.ext
  apply Functor.hom_ext_of_isLeftKanExtension (S ⋙ RG) α
  apply NatTrans.ext
  funext K
  simpa [α, Category.assoc] using (hτ K).trans (hs K).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- K-injective mapping fibres and their unit-normalized distinguished triangle comparison.
The chain comparison is the explicitly defined diagonal map, so its triangle-morphism
laws are exactly `c G(r) = r' theta` and `theta[1] G(b) = b' c`.
Source: Stacks, Tags 090X, 070Y and 05SU
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

Proof: K-injectives are the right orthogonal of acyclic complexes in the
homotopy category. This orthogonal is triangulated, hence contains the cone of u
and its shift by -1. Repeat for P'; preservation by G gives G(H). The canonical
additive cone comparison followed by the cone map of c is invertible, since the
cone map of c inverse is its inverse. Inverse rotation gives the stated chain
comparison and its projection and inclusion equations. The localized fibre
triangles are distinguished by inverse rotation of the localized cone triangles.
Construct a triangle morphism from the localized termwise G-image to the stated
RG-image, with components eta_H, eta_P, eta_P. Naturality of eta proves the first
two squares; its naturality at the connecting map, combined with normalization
at H and the two localization-shift comparisons, proves the third. Each component
is invertible by h_eta. Invert this triangle morphism and compose with the
localized chain comparison. Its components give the displayed inverse-unit
formulas, and its third square is the requested connecting equation. Transport
distinguishedness through this isomorphism. -/
theorem kInjectiveFiberTriangle_comparison
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (G : A ⥤ B) [G.Additive]
    (hG : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hUniversal : ∀ F : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun β : RG ⟶ F ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    (hσ : IsUnitNormalizedKInjectiveShift G RG η σ)
    (P : CochainComplex A ℤ) (P' : CochainComplex B ℤ)
    (hP : P.IsKInjective) (hP' : P'.IsKInjective)
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    ∃ hH : (kInjectiveFiberTriangle u).obj₁.IsKInjective,
      (kInjectiveFiberTriangle u').obj₁.IsKInjective ∧
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (kInjectiveFiberTriangle u).obj₁) ∧
      (kInjectiveFiberChainComparison G u u' c hc).hom₂ = c.hom ∧
      (kInjectiveFiberChainComparison G u u' c hc).hom₃ = c.hom ∧
      IsIso (kInjectiveFiberChainComparison G u u' c hc).hom₁ ∧
      DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u) ∈
        distTriang (DerivedCategory A) ∧
      kInjectiveDerivedFiberTriangle RG σ u ∈ distTriang (DerivedCategory B) ∧
      DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u') ∈
        distTriang (DerivedCategory B) ∧
      ∃ e : kInjectiveDerivedFiberTriangle RG σ u ≅
          DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u'),
        e.hom.hom₁ = (kInjectiveInverseUnit G RG η hη _ hH).hom ≫
          DerivedCategory.Q.map (kInjectiveFiberChainComparison G u u' c hc).hom₁ ∧
        e.hom.hom₂ = (kInjectiveInverseUnit G RG η hη P hP).hom ≫
          DerivedCategory.Q.map c.hom ∧
        e.hom.hom₃ = (kInjectiveInverseUnit G RG η hη P hP).hom ≫
          DerivedCategory.Q.map c.hom ∧
        (kInjectiveDerivedFiberTriangle RG σ u).mor₃ ≫ e.hom.hom₁⟦(1 : ℤ)⟧' =
          e.hom.hom₃ ≫
            (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u')).mor₃ := by
  have _ := hA
  have _ := hUniversal
  clear hA hUniversal
  let M := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let QA : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  have hH := fiber_isKInjective u hP
  have hH' := fiber_isKInjective u' hP'
  have hθ := fiber_chain_isIso G u u' c hc
  let θ := asIso (kInjectiveFiberChainComparison G u u' c hc)
  let T := kInjectiveFiberTriangle u
  let t : QB.mapTriangle.obj (M.mapTriangle.obj T) ⟶
      kInjectiveDerivedFiberTriangle RG σ u :=
    { hom₁ := η.app T.obj₁
      hom₂ := η.app P
      hom₃ := η.app P
      comm₁ := η.naturality T.mor₁
      comm₂ := η.naturality T.mor₂
      comm₃ := by
        change (QB.map (M.map T.mor₃ ≫ (M.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
            (QB.commShiftIso (1 : ℤ)).hom.app (M.obj T.obj₁)) ≫
            (η.app T.obj₁)⟦(1 : ℤ)⟧' =
          η.app P ≫ (RG.map (QA.map T.mor₃ ≫
            (QA.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ σ.hom.app (QA.obj T.obj₁))
        simp only [Functor.map_comp, Category.assoc]
        rw [← hσ T.obj₁]
        have hn := η.naturality T.mor₃
        dsimp only [Functor.comp_map] at hn
        simpa [Category.assoc, M, QA, QB, T, kInjectiveFiberTriangle] using congrArg
          (fun f ↦ f ≫ RG.map ((QA.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
            σ.hom.app (QA.obj T.obj₁)) hn }
  have ht₁ : IsIso t.hom₁ := hη _ hH
  have ht₂ : IsIso t.hom₂ := hη _ hP
  have ht₃ : IsIso t.hom₃ := hη _ hP
  let et := Triangle.isoMk _ _ (asIso t.hom₁) (asIso t.hom₂) (asIso t.hom₃)
    t.comm₁ t.comm₂ t.comm₃
  let e := et.symm ≪≫ QB.mapTriangle.mapIso θ
  have source_dist (P : CochainComplex A ℤ) (u : P ⟶ P) :
      QA.mapTriangle.obj (kInjectiveFiberTriangle u) ∈ distTriang (DerivedCategory A) := by
    exact isomorphic_distinguished _
      (inv_rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished u)) _
      (QA.mapTriangleInvRotateIso.symm.app (CochainComplex.mappingCone.triangle u))
  have target_dist : QB.mapTriangle.obj (kInjectiveFiberTriangle u') ∈
      distTriang (DerivedCategory B) := by
    exact isomorphic_distinguished _
      (inv_rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished u')) _
      (QB.mapTriangleInvRotateIso.symm.app (CochainComplex.mappingCone.triangle u'))
  refine ⟨hH, hH', hG _ hH, fiber_chain_hom₂ G u u' c hc,
    fiber_chain_hom₃ G u u' c hc, ?_, source_dist P u,
    isomorphic_distinguished _ target_dist _ e, target_dist, e, ?_, ?_, ?_, e.hom.comm₃⟩
  · exact inferInstanceAs (IsIso θ.hom.hom₁)
  · rfl
  · simp [e, et, θ, t, kInjectiveInverseUnit, fiber_chain_hom₂, QB]
  · simp [e, et, θ, t, kInjectiveInverseUnit, fiber_chain_hom₃, QB]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual diagonal chain comparison and of both unit-normalized
localized comparison components, for commuting maps of endomorphism diagrams.
Source: Stacks, Tag 090X, explicit cone comparison; Tags 070Y and 05SU
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

Proof: check naturality of the additive cone comparison in each degree using
the two cone inclusions. Functoriality of cone maps and the assumed c/a/d square
give a commuting square of cone triangles. Naturality of the inverse-rotation
comparison gives the fibre-triangle square; project its first component. For any
map between K-injective complexes, cancel the invertible source unit in eta's
naturality equation to obtain naturality of the inverse unit. Apply this to the
fibre map and to a, and combine with the localized chain square and c/a/d square.
These are the two remaining displayed equations. -/
theorem kInjectiveFiberTriangle_comparison_naturality
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (G : A ⥤ B) [G.Additive]
    (hG : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hUniversal : ∀ F : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun β : RG ⟶ F ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    (hσ : IsUnitNormalizedKInjectiveShift G RG η σ)
    (P R : CochainComplex A ℤ) (P' R' : CochainComplex B ℤ)
    (hP : P.IsKInjective) (hR : R.IsKInjective)
    (hP' : P'.IsKInjective) (hR' : R'.IsKInjective)
    (u : P ⟶ P) (v : R ⟶ R) (u' : P' ⟶ P') (v' : R' ⟶ R')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (d : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj R ≅ R')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u')
    (hd : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫ d.hom = d.hom ≫ v')
    (a : P ⟶ R) (a' : P' ⟶ R')
    (ha : u ≫ a = a ≫ v) (ha' : u' ≫ a' = a' ≫ v')
    (hca : c.hom ≫ a' = (G.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ d.hom)
    (hH : (kInjectiveFiberTriangle u).obj₁.IsKInjective)
    (hJ : (kInjectiveFiberTriangle v).obj₁.IsKInjective) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (kInjectiveFiberTriangleMap u v a ha).hom₁ ≫
        (kInjectiveFiberChainComparison G v v' d hd).hom₁ =
      (kInjectiveFiberChainComparison G u u' c hc).hom₁ ≫
        (kInjectiveFiberTriangleMap u' v' a' ha').hom₁ ∧
    RG.map (DerivedCategory.Q.map (kInjectiveFiberTriangleMap u v a ha).hom₁) ≫
        (kInjectiveInverseUnit G RG η hη _ hJ).hom ≫
        DerivedCategory.Q.map (kInjectiveFiberChainComparison G v v' d hd).hom₁ =
      (kInjectiveInverseUnit G RG η hη _ hH).hom ≫
        DerivedCategory.Q.map (kInjectiveFiberChainComparison G u u' c hc).hom₁ ≫
        DerivedCategory.Q.map (kInjectiveFiberTriangleMap u' v' a' ha').hom₁ ∧
    RG.map (DerivedCategory.Q.map a) ≫
        (kInjectiveInverseUnit G RG η hη R hR).hom ≫ DerivedCategory.Q.map d.hom =
      (kInjectiveInverseUnit G RG η hη P hP).hom ≫ DerivedCategory.Q.map c.hom ≫
        DerivedCategory.Q.map a' := by
  have _ := hA
  have _ := hG
  have _ := hUniversal
  have _ := hP'
  have _ := hR'
  have _ := hσ
  clear hA hG hUniversal hP' hR' hσ
  let M := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let ta := CochainComplex.mappingCone.triangleMap u v a a ha
  let ta' := CochainComplex.mappingCone.triangleMap u' v' a' a' ha'
  let tc := CochainComplex.mappingCone.triangleMap (M.map u) u' c.hom c.hom hc
  let td := CochainComplex.mappingCone.triangleMap (M.map v) v' d.hom d.hom hd
  have hcone : M.mapTriangle.map ta ≫
        (CochainComplex.mappingCone.mapTriangleIso v G).hom ≫ td =
      (CochainComplex.mappingCone.mapTriangleIso u G).hom ≫ tc ≫ ta' := by
    apply Triangle.hom_ext
    · simpa [M, ta, td, tc, ta', CochainComplex.mappingCone.mapTriangleIso] using hca.symm
    · simpa [M, ta, td, tc, ta', CochainComplex.mappingCone.mapTriangleIso] using hca.symm
    · dsimp [ta, ta', tc, td, CochainComplex.mappingCone.mapTriangleIso]
      rw [← Category.assoc, cone_map_naturality G u v a ha, Category.assoc]
      rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
      simp only [← hca]
      rfl
  have htri : M.mapTriangle.map (kInjectiveFiberTriangleMap u v a ha) ≫
        kInjectiveFiberChainComparison G v v' d hd =
      kInjectiveFiberChainComparison G u u' c hc ≫
        kInjectiveFiberTriangleMap u' v' a' ha' := by
    let I := invRotate (CochainComplex B ℤ)
    have hn := M.mapTriangleInvRotateIso.inv.naturality ta
    dsimp only [Functor.comp_map] at hn
    have htri' : M.mapTriangle.map ((invRotate (CochainComplex A ℤ)).map ta) ≫
          M.mapTriangleInvRotateIso.inv.app (CochainComplex.mappingCone.triangle v) ≫
            I.map ((CochainComplex.mappingCone.mapTriangleIso v G).hom ≫ td) =
        M.mapTriangleInvRotateIso.inv.app (CochainComplex.mappingCone.triangle u) ≫
          I.map ((CochainComplex.mappingCone.mapTriangleIso u G).hom ≫ tc) ≫
            I.map ta' := by
      calc
        _ = M.mapTriangleInvRotateIso.inv.app
              (CochainComplex.mappingCone.triangle u) ≫
            I.map (M.mapTriangle.map ta) ≫
              I.map ((CochainComplex.mappingCone.mapTriangleIso v G).hom ≫ td) := by
          simpa only [Category.assoc] using congrArg (fun f ↦
            f ≫ I.map ((CochainComplex.mappingCone.mapTriangleIso v G).hom ≫ td)) hn
        _ = _ := by
          simpa only [← Functor.map_comp, Category.assoc] using congrArg (fun f ↦
            M.mapTriangleInvRotateIso.inv.app (CochainComplex.mappingCone.triangle u) ≫
              I.map f) hcone
    simpa only [kInjectiveFiberTriangleMap, kInjectiveFiberChainComparison,
      Category.assoc, I, ta, ta', tc, td] using htri'
  have hchain := congrArg TriangleMorphism.hom₁ htri
  dsimp only [comp_hom₁, Functor.mapTriangle_map_hom₁] at hchain
  refine ⟨hchain, ?_, ?_⟩
  · rw [← Category.assoc, inverse_unit_naturality G RG η hη hH hJ]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [hchain]
  · rw [← Category.assoc, inverse_unit_naturality G RG η hη hP hR]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [← hca]

end CategoryTheory
