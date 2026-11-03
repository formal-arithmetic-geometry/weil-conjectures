/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectionIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveCoefficient
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveLineTraceSupplement
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.TensorTraceRightUnit

/-!
# Proper projection followed by the normalized tensor trace

This isolates the tensorator, proper-integration, decomposition, and right-unitor
calculation in the projective counit comparison.
(blueprint: lem-route-line-proper-counit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local instance 100000] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local irreducible] Etale.projectiveLineTraceDatum Etale.projectiveLineTraceTransport
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

attribute [local implicit_reducible] Scheme.finiteEtaleTateSheaf Scheme.finiteEtaleTateTwist

/-- The canonical direct-image comparison carries the ordinary projective trace
onto the supported trace, by the two decomposition components. -/
private theorem projective_trace_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    :
    let A := Scheme.finiteTateCoefficient l E n
    let q : ProjectiveLine T ⟶ T := ProjectiveLine T ↘ T
    let W := (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧
    geoP1PushComparison A q W ≫ projectiveTrace l E n T hT hI r hA =
      (comparison A T).map (Etale.projectiveLineTrace (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) A hA T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1))) := by
  dsimp only
  let A := Scheme.finiteTateCoefficient l E n
  let q : ProjectiveLine T ⟶ T := ProjectiveLine T ↘ T
  let W := (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  have hNT : IsUnit (N : Γ(T, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hT.pow (r + 1)
  let D := Etale.projectiveLineTraceDatum N hN A hA T hNT
  have hb : projectiveB l E n T hT hI r hA =
      geoP1TwistedMap A N hN hA T hNT := by
    unfold projectiveB geoP1TwistedMap
    rw [D.decomposition_hom]
    exact compared_desc_total (geoP1Comparison A T) _ _ _ _ _
      (unit_comparison l E n T hT r hA)
      (chern_push_comparison l E n T hT hI r hA)
  unfold projectiveTrace geoP1Trace
  simp only [asIso_inv]
  let := projectiveB_isIso l E n T hT hI r hA
  let := sumComparison_isIso A T
    ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) (Etale.ordinaryFiniteUnit A T)
  have hb' : geoP1SumComparison A T _ _ ≫
      (comparison A T).map D.decomposition.hom ≫ geoP1PushComparison A q W =
      projectiveB l E n T hT hI r hA := hb.symm
  apply (cancel_epi ((comparison A T).map D.decomposition.hom)).mp
  apply (cancel_epi (geoP1SumComparison A T
    ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
    (Etale.ordinaryFiniteUnit A T))).mp
  rw [reassoc_of% hb']
  simp only [IsIso.hom_inv_id_assoc]
  change _ = geoP1SumComparison A T _ _ ≫ (comparison A T).map D.decomposition.hom ≫
    (comparison A T).map (D.decomposition.inv ≫ biprod.snd)
  rw [← Functor.map_comp, Iso.hom_inv_id_assoc]
  symm
  let U := (Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧
  let V := Etale.ordinaryFiniteUnit A T
  change (geoP1Comparison A T).biprodComparison' U V ≫
    (geoP1Comparison A T).map (biprod.snd (X := U) (Y := V)) =
    biprod.snd (X := (geoP1Comparison A T).obj U) (Y := (geoP1Comparison A T).obj V)
  rw [← Functor.biprodComparison_snd (geoP1Comparison A T) U V,
    Functor.biprodComparison'_comp_biprodComparison_assoc]


private theorem ordinary_trace_epsilon_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (K : Etale.DerivedCategoryModule A S) :
    Etale.projectiveLineTraceEpsilon N hN A hA S hS K =
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  letI : IsProper (ProjectiveLine S ↘ S) :=
    ProjectiveSpace.instIsProper (ULift (Fin 2)) S
  letI : IsIso (Etale.ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) :=
    Etale.isIso_proper_projection_formula_reordered A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K
  inv (Etale.ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) ≫
    ((Etale.ordinaryFiniteTensor A S).obj K).map (Etale.projectiveLineTrace N hN A hA S hS) ≫
      (Etale.derivedTensorSingleUnitIso K).hom := by
  rfl
private theorem ordinary_projective_counit_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hNT : IsUnit (N : Γ(T, ⊤)))
    (K : Etale.DerivedCategoryModule A T) :
    let q : ProjectiveLine T ⟶ T := ProjectiveLine T ↘ T
    let W := (Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧
    Etale.ordinaryFiniteProjection A q W K ≫ Etale.projectiveLineTraceEpsilon N hN A hA T hNT K =
      ((Etale.ordinaryFiniteTensor A T).obj K).map (Etale.projectiveLineTrace N hN A hA T hNT) ≫
        (Etale.derivedTensorSingleUnitIso K).hom := by
  dsimp only
  let q : ProjectiveLine T ⟶ T := ProjectiveLine T ↘ T
  let W := (Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧
  let te := Etale.projectiveLineTrace N hN A hA T hNT
  let : IsLocallyNoetherian (ProjectiveLine T) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine T ↘ T)
  let : CompactSpace (ProjectiveLine T) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine T ↘ T)
  let : IsProper (ProjectiveLine T ↘ T) :=
    ProjectiveSpace.instIsProper (ULift (Fin 2)) T
  let : IsIso (Etale.ordinaryFiniteProjection A q W K) :=
    Etale.isIso_proper_projection_formula_reordered A q W K
  rw [ordinary_trace_epsilon_eq]
  exact IsIso.hom_inv_id_assoc _ _


/-- Map a composition equation after its domain-category proof has been checked. -/
private theorem map_comp_of_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (w : f ≫ g = h) :
    F.map f ≫ F.map g = F.map h := by
  rw [← F.map_comp, w]

/-- The ordinary proper projection cancels against the inverse in the trace counit. -/
private theorem ordinary_projective_counit_cancel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hNT : IsUnit (N : Γ(T, ⊤)))
    (K : Etale.DerivedCategoryModule A T) :
    let q : ProjectiveLine T ⟶ T := ProjectiveLine T ↘ T
    let W := (Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧
    let C := comparison A T
    C.map (Etale.ordinaryFiniteProjection A q W K) ≫
        C.map (Etale.projectiveLineTraceEpsilon N hN A hA T hNT K) =
      C.map (((Etale.ordinaryFiniteTensor A T).obj K).map
        (Etale.projectiveLineTrace N hN A hA T hNT) ≫
        (Etale.derivedTensorSingleUnitIso K).hom) := by
  dsimp only
  exact map_comp_of_eq (comparison A T)
    (ordinary_projective_counit_projection A N hN hA T hNT K)

set_option linter.unusedVariables false in
/-- Postcomposing the canonical projection square with the normalized proper trace
is the comparison image of the ordinary projective counit.

Source: the final two paragraphs of
`lem-amb-affine-space-top-trace.proof.md`, first paragraph, lines 19--24;
Stacks 0B65 and 0GL1.
(blueprint: lem-route-line-proper-counit-tensor-trace)

Proof: use the defining `ProperIntegrationEquation` of `projectiveEpsilon`.
The projective decomposition comparison identifies its trace with the comparison
image of the ordinary trace.  Naturality of the tensorator moves this comparison
through the tensor product, and the defining formula for `rightUnit` cancels the
comparison tensorator and leaves the ordinary tensor right unitor.  Finally unfold
`projectiveLineTraceEpsilon` and reassociate.  The equation below is the resulting
postcomposed equality; it is strictly smaller than the counit comparison because
its source is already the canonical tensor/projection route.
-/
theorem proper_counit_tensor_trace
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hχ : projectiveChern l E n T hT hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T)).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA T
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).chern)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    let A := Scheme.finiteTateCoefficient l E n
    let P := ProjectiveLine T
    let q : P ⟶ T := P ↘ T
    let W := (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA P)⟦(2 : ℤ)⟧
    let L := (Etale.ordinaryFinitePushforward A q).obj W
    let M := (Etale.ordinaryFiniteP1Right A (l ^ (r + 1)) hA T).obj K.obj
    (tensorComparison A T K.obj L).hom ≫
        ((-⊗ᴸ-(T)[ModuleCat.{u + 1} A].obj ((comparison A T).obj K.obj)).map
          (id (geoP1PushComparison A q W))) ≫
        properProjection (ModuleCat.{u + 1} A) q (line l E n r hA P)
          ((comparison A T).obj K.obj) ≫
        projectiveEpsilon l E n T hT hI r hA K =
      (comparison A T).map (Etale.ordinaryFiniteProjection A q W K.obj) ≫
      (comparison A T).map (Etale.projectiveLineTraceEpsilon (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) A hA T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) K.obj) := by
  dsimp only
  let A := Scheme.finiteTateCoefficient l E n
  let P := ProjectiveLine T
  let q : P ⟶ T := P ↘ T
  let W := (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA P)⟦(2 : ℤ)⟧
  let L := (Etale.ordinaryFinitePushforward A q).obj W
  have hproper : ProperIntegrationEquation A q (line l E n r hA P) K.obj
      (projectiveTrace l E n T hT hI r hA)
      (projectiveEpsilon l E n T hT hI r hA K) := by
    unfold projectiveEpsilon
    exact (existsUniqueProjectiveEpsilon l E n T hT hI r hA K).exists.choose_spec
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  have hNT : IsUnit (N : Γ(T, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hT.pow (r + 1)
  have ht := projective_trace_comparison l E n T hT hI r hA
  have he := ordinary_projective_counit_cancel A N hN hA T hNT K.obj
  let te := Etale.projectiveLineTrace N hN A hA T hNT
  unfold ProperIntegrationEquation at hproper
  dsimp only [id]
  rw [hproper, ← Functor.map_comp_assoc, ht]
  rw [he]
  exact tensorComparison_trace_rightUnit A T K.obj L te

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
