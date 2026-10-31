/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineOrderedCounitZero
import WeilConjectures.AlgebraicGeometry.AffineOrderedCounitSuccessor
import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Ordinary-counit normalization of ordered tensor integration
Source: projection-purity agreement, final paragraph, ordered counit calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] ordinarySourceObject
attribute [local implicit_reducible] ordinarySourceObject
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor Etale.rightDerivedLowerShriek
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  ordinaryLower sourceEtale etaleCategory proCategory

private theorem ordinary_tensor_counit (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y d)
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y d) d) K _ (ordinarySourceIso P Y aY K d)
      (ordinaryCounit P Y aY K hK d) (ordinaryTraceRaw P Y aY d) := by
  induction d generalizing K with
  | zero => exact ordinary_counit_zero P Y aY K hK
  | succ d ih => exact ordinary_counit_successor P Y aY d (fun K hK ↦ ih K hK) K hK

set_option maxHeartbeats 800000 in
-- Identifying the concrete derived source functors needs additional elaboration.
private theorem ordinary_coordinates_raw_equation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ) :
    let A := AffineLinePurity.Ring P
    let f := affineTraceProjection Y d
    let W := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P)
      (affineTraceTower Y d) d
    Etale.compactSupportProjectionMap A f W Ke ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d)
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app Ke)
          (Iso.refl W)).inv ≫
      (ordinaryTensorCoordinatesRaw P Y aY Ke hKe d).hom ≫
      (orderedAdjunction P Y aY d).counit.app Ke =
        (Etale.ordinaryFiniteTensorTrace A Y (ordinaryTraceRaw P Y aY d)).app Ke := by
  have h := ordinary_tensor_counit P Y aY Ke hKe d
  unfold OrdinaryCounitEquation ordinaryCounit at h
  dsimp only
  simp only [ordinaryTensorCoordinatesRaw, id_eq, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact h

private theorem dependent_pair_transport {I : Type*} (F G : I → Type*)
    (Q : ∀ i, F i → G i → Prop) {i j : I} (h : i = j)
    {x : F i} {y : G i} {x' : F j} {y' : G j}
    (hx : HEq x' x) (hy : HEq y' y) (hQ : Q i x y) : Q j x' y' := by
  cases h
  rw [eq_of_heq hx, eq_of_heq hy]
  exact hQ

private theorem ordinary_coordinates_equation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ) :
    let A := AffineLinePurity.Ring P
    let f := iteratedAffineLineProj Y d
    let := (projection_geometry Y d).2
    Etale.compactSupportProjectionMap A f (etaleCoefficient P Y d) Ke ≫
      (ordinaryLower P Y d).map
        (Etale.ordinaryFiniteTensorRightMapIso A (iteratedAffineLine Y d)
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app Ke)
          (Iso.refl (etaleCoefficient P Y d))).inv ≫
      (ordinaryTensorCoordinates P Y aY Ke hKe d).hom ≫
      (orderedAdjunction P Y aY d).counit.app Ke =
        (Etale.ordinaryFiniteTensorTrace A Y (ordinaryTrace P Y aY d)).app Ke := by
  let A := AffineLinePurity.Ring P
  let W := fun X : Scheme.{u} ↦
    Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) X d
  let I := {q : Σ X : Scheme.{u}, X ⟶ Y // HasCompactification q.2}
  let ti := fun q : I ↦
    letI := q.property
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q.val.2).obj
      (ordinarySourceObject A q.val.2 (W q.val.1) Ke) ≅
        (Etale.affineTraceLeft A Y d).obj
          ((Etale.affineTraceRight A (exponent P) (annihilates P) Y d).obj Ke)
  let tt := fun q : I ↦
    letI := q.property
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q.val.2).obj (W q.val.1) ⟶
      Etale.ordinaryFiniteUnit A Y
  let Q : ∀ q, ti q → tt q → Prop := fun q e t ↦
    letI := q.property
    Etale.compactSupportProjectionMap A q.val.2 (W q.val.1) Ke ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q.val.2).map
        (Etale.ordinaryFiniteTensorRightMapIso A q.val.1
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) q.val.2).app Ke) (Iso.refl (W q.val.1))).inv ≫
      e.hom ≫ (orderedAdjunction P Y aY d).counit.app Ke =
        (Etale.ordinaryFiniteTensorTrace A Y t).app Ke
  let q₀ : I := ⟨⟨affineTraceTower Y d, affineTraceProjection Y d⟩, inferInstance⟩
  let q₁ : I := ⟨⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩,
    (projection_geometry Y d).2⟩
  have hq : q₀ = q₁ := Subtype.ext (affineTower_projection_eq Y d)
  have he : HEq (ordinaryTensorCoordinates P Y aY Ke hKe d)
      (ordinaryTensorCoordinatesRaw P Y aY Ke hKe d) := by
    unfold ordinaryTensorCoordinates
    exact cast_heq _ _
  have ht := (ordinaryTrace_existsUnique P Y aY d).exists.choose_spec
  exact dependent_pair_transport ti tt Q hq he ht
    (ordinary_coordinates_raw_equation P Y aY Ke hKe d)

private theorem identity_iso_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (J : C) : (Iso.refl F).app J = Iso.refl (F.obj J) := by
  rfl

private theorem ordinary_standing_self
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ)
    (J : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) (iteratedAffineLine Y d)) :
    let := (projection_geometry Y d).2
    (Etale.rightDerivedLowerShriekIso (AffineLinePurity.Ring P)
      (compactification Y d)).app J = Iso.refl _ := by
  let := (projection_geometry Y d).2
  let := tower_noetherian P Y aY d
  have h := (Etale.unboundedEtaleCompactSupport_comparison_coherence
    (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)).1 (compactification Y d)
  simpa only [Etale.rightDerivedLowerShriekIso, compactification,
    Etale.rightDerivedLowerShriek, identity_iso_app] using
    congrArg (fun e ↦ e.app J) h

private theorem normalization_of_tensor_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (V : E ⥤ D) {S T U : C} {L R Ke : E} {K : D}
    (sc : S ≅ U) (real : T ≅ U) (c : F.obj T ≅ V.obj L)
    (coord : L ≅ R) (epsilon : R ⟶ Ke) (e : V.obj Ke ≅ K)
    (augmentation : F.obj U ⟶ K)
    (ht : F.map real.hom ≫ augmentation =
      c.hom ≫ V.map (coord.hom ≫ epsilon) ≫ e.hom) :
    F.map sc.hom ≫ augmentation =
      (F.mapIso (sc ≪≫ real.symm) ≪≫ c ≪≫ V.mapIso coord).hom ≫
        V.map epsilon ≫ e.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc] at ht
  rw [← ht]
  simp only [← F.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The tensor augmentation in explicit ordinary counit coordinates, at one rank.
This statement contains no last-coordinate evaluation or compact-support composition.
Source: current blueprint projection-purity agreement, final paragraph.
(blueprint: lem-pur-affine-ordered-evaluation-normalization).

Proof step 1: For every finite-Tor ordinary H prove OrdinaryCounitEquation at all d by
induction: ordinary_counit_zero is the base, and ordinary_counit_successor applies the induction
hypothesis to all finite-Tor H. This gives the coefficient-first tensor formula for the actual
bounded-below transported counit, rather than replacing it by an unbounded or product-coordinate
counit.

Proof step 2: Insert the exact-versus-left-derived pullback tensor isomorphism into that
equation and cancel its inverse. By definition the remaining source/counit factors are
ordinaryTensorCoordinatesRaw.hom followed by ε_d. Transport the equality along
affineTower_projection_eq, including the proof-irrelevant compactifiability witnesses. The HEq
characterizations of ordinaryTensorCoordinates and ordinaryTrace give the corresponding equation
on the iteratedAffineLine tower. Identity-refinement coherence identifies the standing ordinary
compactification comparison with identity.

Proof step 3: Write W for the ordinary rank-d Tate coefficient, J=p_d^*Ke⊗W, C_W,C_J for
compact-support site comparisons, V for comparison on Y, and b for tensorPullbackComparison on
X_d. The boundedness hypotheses for W and J follow from source_applicability. Apply the
compact-support projection square. Naturality of the signed braiding on both sites puts it in
coefficient-first order. If P_e and P_p are the actual ordinary and pro-etale projections, the
square becomes δ_(Ke,FeW);(1⊗C_W.inv);P_p = V(P_e);C_J.inv;F_d(b.hom). The exact-pullback
comparison appearing in the ordinary formula is cancelled by its inverse. Its cancellation uses
symmetry naturality and the involutivity of the actual canonical signed swap, not an unspecified
tensor isomorphism.

Proof step 4: Invert the two projection isomorphisms in this square. Tensor-comparison
naturality for the ordinaryTrace map moves tensor with that trace across δ. The definition of
integration says C_W.inv;integration=V(ordinaryTrace), after identity compactification
comparison. The coefficient-unit comparison is the derived oplax unit; therefore oplax
right-unitality identifies moduleRightUnit with δ.inv followed by V of the ordinary right
unitor. The ordinary single-unit identification is identity, so the ordinaryFiniteTensorTrace
formula has precisely that right unitor. Thus F_d(b.hom);augmentation_(VKe) =
C_J.hom;V(ordinaryTensorCoordinates.hom;ε_d).

Proof step 5: Projection-map naturality, inversion of the projection, tensor bifunctoriality and
right-unitor naturality show naturality of projectionTensorTrace in eK.hom. Use this to replace
VKe by K in the preceding equation. Expand sourceRealization=realizeTensorSource followed by
s_d.symm. Its inverse, the site comparison C_J and the ordinary coordinates are exactly E_d.
Cancellation of realizeTensorSource and associativity give the claimed equation. All maps exist
on zero coefficients and the empty base; d=0 uses the specified inverse tensor unitor and
identity pullback. -/
theorem orderedEvaluation_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y d)).map
        (sourceComparison P Y K.obj d).hom ≫ augmentation P Y aY K Ke hKe eK d =
      (orderedCounitCoordinates P Y aY K Ke hKe eK d).hom ≫
        (comparison (AffineLinePurity.Ring P) Y).map
          ((orderedAdjunction P Y aY d).counit.app Ke) ≫ eK.hom := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
