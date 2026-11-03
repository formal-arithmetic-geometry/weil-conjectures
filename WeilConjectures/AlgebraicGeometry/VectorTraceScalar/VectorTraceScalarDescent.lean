/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarProjectiveComponents
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineInduction
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarFrameComparison
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.Vector.VectorTraceGeometricDescent
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Scalar descent of the specified vector-bundle trace

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, old Steps 9--10
(blueprint: lem-pur-vector-trace-scalar-descent).

The helper maps express the normalized Tate balancing in the existing ordered-tensor
presentation used by vector integration and the affine coordinate tower. All compact
support maps are the published proper/open maps for the chosen compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
namespace VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

private theorem splitting_square
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (Q : C ⥤ D) [Q.Additive] {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z')
    (l : Q.obj X ⟶ X') (u : Q.obj Y ⟶ Y') (q : Q.obj Z ⟶ Z')
    (ha : Q.map a ≫ q = l ≫ a') (hb : Q.map b ≫ q = u ≫ b') :
    Q.map (biprod.desc a b) ≫ q =
      biprod.lift (Q.map biprod.fst ≫ l) (Q.map biprod.snd ≫ u) ≫
        biprod.desc a' b' := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts Q
  apply (cancel_epi (Q.mapBiprod X Y).inv).mp
  apply biprod.hom_ext' <;>
    simp [← Functor.map_comp_assoc, ha, hb]

private theorem trace_square
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {X Y Z : C} {X' Y' Z' : D} (b : X ≅ Y) (b' : X' ≅ Y')
    (q : Q.obj Y ⟶ Y') (s : Q.obj X ⟶ X') (p : X ⟶ Z) (p' : X' ⟶ Z')
    (u : Q.obj Z ⟶ Z') (hsq : Q.map b.hom ≫ q = s ≫ b'.hom)
    (hp : s ≫ p' = Q.map p ≫ u) :
    q ≫ b'.inv ≫ p' = Q.map (b.inv ≫ p) ≫ u := by
  apply (cancel_epi (Q.map b.hom)).1
  rw [← Category.assoc, hsq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Q.map_comp_assoc, Iso.hom_inv_id_assoc]
  exact hp

private theorem derived_eq_of_cover (R : Type (u + 1)) [CommRing R]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    [∀ i, Etale (a i)]
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    {K : DerivedCategoryModule R X}
    {M P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (f g : K ⟶ (_root_.DerivedCategory.singleFunctor _ 0).obj P)
    (h : ∀ i, (ordinaryFinitePullback R (a i)).map f =
      (ordinaryFinitePullback R (a i)).map g) : f = g := by
  obtain ⟨ell, hell⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective (α.inv ≫ f)
  obtain ⟨mu, hmu⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective (α.inv ≫ g)
  have he : α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell = f := by
    rw [hell, ← Category.assoc, α.hom_inv_id, Category.id_comp]
  have hm : α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map mu = g := by
    rw [hmu, ← Category.assoc, α.hom_inv_id, Category.id_comp]
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} R) (a i)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro P Q z hz
    exact isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} R) a ha z hz
  have heq : ell = mu := by
    apply hf.map_injective
    intro i
    have hh := congrArg (etaleDegreeZeroHomEquiv R (a i) α) (h i)
    rw [← he, ← hm, etaleDegreeZeroHomEquiv_map, etaleDegreeZeroHomEquiv_map] at hh
    rw [← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} R) (a i) inferInstance) ell,
      ← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} R) (a i) inferInstance) mu, hh]
  rw [← he, ← hm, heq]

private theorem projective_splitting_square (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).map (projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
      projective φ N hN hA hB S hS =
    sum φ N hN hA hB S hS ≫ (projectiveLineTraceDatum N hN B hB S hS).decomposition.hom := by
  let : (scalarExtension φ S).Additive := by
    unfold scalarExtension ProEtale.pbcFixedScalarExtension
    exact (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars S.smallEtaleTopology φ)).left_adjoint_additive
  obtain ⟨hv, hc⟩ := projective_components N hN φ hA hB S hS
  rw [(projectiveLineTraceDatum N hN A hA S hS).decomposition_hom,
    (projectiveLineTraceDatum N hN B hB S hS).decomposition_hom]
  exact splitting_square (scalarExtension φ S) _ _ _ _
    (line φ N hN hA hB S hS) (unit φ S) (projective φ N hN hA hB S hS) hv hc

private theorem projective_trace_square (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    projective φ N hN hA hB S hS ≫ ordinaryFiniteProjectiveLineTrace N hN B hB S hS =
      (scalarExtension φ S).map (ordinaryFiniteProjectiveLineTrace N hN A hA S hS) ≫ unit φ S := by
  exact trace_square (scalarExtension φ S)
    (projectiveLineTraceDatum N hN A hA S hS).decomposition
    (projectiveLineTraceDatum N hN B hB S hS).decomposition
    (projective φ N hN hA hB S hS) (sum φ N hN hA hB S hS)
    biprod.snd biprod.snd (unit φ S)
    (projective_splitting_square N hN φ hA hB S hS)
    (by simp only [sum, biprod.lift_snd])

/-- Scalar extension preserves the specified Kummer component, projective decomposition,
its second-projection trace, all coordinate-tower traces, and global vector integration.
Source: main-20261015, cor-pur-vector-bundle-purity.proof.md, paragraph 2, old Steps 9--10
(blueprint: lem-pur-vector-trace-scalar-descent).

Proof:
1. Fix the normalized scalar unit and Tate balancing. On K-flat flat degree-zero Tate
lines the scalar/single comparison is ordinary balancing; shifted tensor powers compute
all ranks. Pullback preserves the generator formula (z tensor a) tensor b maps to
z tensor phi(a)b. Use lem-asd-etale-finite-twist-pullback,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and degree-zero full faithfulness.
2. Transpose the proper scalar mate using lem-asd-proper-finite-coefficient-extension.
Naturality of the scalar/pullback comparison and lem-sp-p1-kummer-derived-scalar identify
the two adjuncts of h with the same normalized Kummer arrow. Adjunction injectivity gives
the first equality. The triangle identity and pullback compatibility give the first
summand's equation, hence the decomposition equality by additivity.
3. Invert the two normalized decompositions and project to their second summands.
The biproduct projection identities give the projective-line trace equality.
4. The inverse open scalar comparison is the left mate of the inverse pullback comparison
(lem-pur-etale-open-scalar-composition). Apply lem-pur-adjunction-mate-transpose to the
open counit. Naturality of the proper comparison and Step 3 give the affine-line equation.
5. Tensor that equation with every shifted Tate input. The ordered projection square of
lem-pur-etale-compact-scalar-coherence and the open tensor/counit identity of
lem-pur-etale-open-derived-tensor give the affine-line counit equation on these inputs.
6. Induct through the ordered coordinate tower, starting with the identity at rank zero.
Use the actual composition scalar square, the preceding counit equation and naturality.
Every intermediate input and its scalar extension is a shifted flat Tate line, hence D+;
all bases remain Noetherian. Proper-refinement coherence identifies the resulting map
with the specified compactification comparison.
7. On a common Zariski frame cover use def-amb-vector-integration: the local maps are
exactly these affine traces. The actual open-restriction square and Cartesian exchange
for the inverse frame identify the scalar maps. Refinement removes compactification
choices. Thus the global equation holds on every frame open.
8. Local traces are invertible. Degree-zero concentration and cover detection make the
global trace invertible. Precompose the desired equality with the inverse of Q(t_A)
followed by u. Both maps are now endomorphisms of the constant degree-zero object.
Degree-zero full faithfulness and lem-pur-sheaf-hom-cover-gluing detect their equality;
cancel the inverse. This is descent only for these degree-zero sheaf maps.
9. Rank zero uses the identity adjunction and multiplication. On the empty base all
objects are zero. N=1 gives zero coefficient rings. No flatness of B over A, cohomology
base-change assertion, or general smooth-purity theorem enters this argument. -/
theorem vectorTraceScalarDescent (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (r : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank r] :
    ((scalarExtension φ S).map (ordinaryFiniteP1ChernPushforward A N hA S
        (projectiveLineTraceDatum N hN A hA S hS).chern) ≫
      projective φ N hN hA hB S hS =
      unit φ S ≫ ordinaryFiniteP1ChernPushforward B N hB S
        (projectiveLineTraceDatum N hN B hB S hS).chern) ∧
    ((scalarExtension φ S).map (projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
      projective φ N hN hA hB S hS =
      sum φ N hN hA hB S hS ≫ (projectiveLineTraceDatum N hN B hB S hS).decomposition.hom) ∧
    (projective φ N hN hA hB S hS ≫ ordinaryFiniteProjectiveLineTrace N hN B hB S hS =
      (scalarExtension φ S).map (ordinaryFiniteProjectiveLineTrace N hN A hA S hS) ≫ unit φ S) ∧
    (∀ d : ℕ, affine φ N hN hA hB S hS d ≫ affineTrace N hN B hB S hS d =
      (scalarExtension φ S).map (affineTrace N hN A hA S hS d) ≫ unit φ S) ∧
    (vector φ N hN hA hB S hS r F ≫ vectorBundleIntegration N hN B hB S hS r F =
      (scalarExtension φ S).map (vectorBundleIntegration N hN A hA S hS r F) ≫ unit φ S) := by
  have hp := projective_trace_square N hN φ hA hB
  have ha := affine_of_projective N hN φ hA hB hp
  refine ⟨(projective_components N hN φ hA hB S hS).2,
    projective_splitting_square N hN φ hA hB S hS, hp S hS, ha S hS, ?_⟩
  classical
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := r)
  let : IsIso (vectorBundleIntegration N hN A hA S hS r F) :=
    (vectorBundleIntegration_concentration_and_isIso N hN A hA S hS r F).2
  let : IsIso (unit φ S) := by
    dsimp only [unit, purityScalarUnitMap, purityTransportUnitMap]
    infer_instance
  let α : (scalarExtension φ S).obj (vectorIntegrationSource A N hA S r F) ≅
      ordinaryFiniteUnit B S :=
    (scalarExtension φ S).mapIso (asIso (vectorBundleIntegration N hN A hA S hS r F)) ≪≫
      asIso (unit φ S)
  refine derived_eq_of_cover B (fun i : I ↦ (V i).ι) ?_ α _ _ ?_
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i
    exact frame_scalar_square N hN φ hA hB ha S hS r F (V i) (e i).some

end VectorTraceScalar
end AlgebraicGeometry.Etale
