/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.PbcWeilCategory
public import Sheaf.Paper.WeilTensorProduct
import all Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.WfTensorCompletionFrobenius
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import all Sheaf.Paper.WeilTensorProduct

/-! # Coefficient and constructible-domain bridge for the Weil projection inputs

Source: main-20261015, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).

The coefficient identification, integral and rational tensor comparisons, and operation
outputs below are the clauses of this bridge. No projection map is assumed invertible.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
universe v r w

section TensorTransport
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem comparison_exists
    {A : Type u} {B : Type v} (P : A → Prop) (Q J H : A → B → B → Prop)
    (h : ∃ a, P a ∧ ∀ b c, J a b c ∧ Q a b c)
    (hH : ∀ a, P a → ∀ b c, H a b c) :
    ∃ a, P a ∧ ∀ b c, Q a b c ∧ H a b c := by
  obtain ⟨a, ha, hq⟩ := h
  exact ⟨a, ha, fun b c ↦ ⟨(hq b c).2, hH a ha b c⟩⟩

/-- A functor respects heterogeneous equality once its endpoints agree. -/
private theorem map_heq {C : Type u} [Category C] {D : Type v} [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst hx
  subst hy
  cases h
  rfl

private theorem nat_app_heq {C : Type u} [Category C] {D : Type v} [Category D]
    {F G : C ⥤ D} (eta : F ⟶ G) {M N : C} (h : M = N) :
    HEq (eta.app M) (eta.app N) := by
  subst h
  rfl

/-- Transport a normalized component using only functor and object equalities. -/
private theorem component_transport
    {A : Type u} [Category A] {B : Type v} [Category B]
    {C : Type r} [Category C] {D : Type w} [Category D]
    (Q : A ⥤ B) (I : B ⥤ D) (J : A ⥤ C) (QA : C ⥤ D)
    (S : A × A ⥤ A) (T : B × B ⥤ B) (F₀ : A ⥤ A) (F : B ⥤ B)
    (hI : Q ⋙ I = J ⋙ QA) (hT : (Q.prod Q) ⋙ T = S ⋙ Q)
    (hF : ∀ M : A, F.obj (Q.obj M) = Q.obj (F₀.obj M))
    (mu₀ : ∀ M N : A, F₀.obj (S.obj (M, N)) ⟶ S.obj (F₀.obj M, F₀.obj N))
    (mu : ∀ M N : B, F.obj (T.obj (M, N)) ⟶ T.obj (F.obj M, F.obj N))
    (hmu : ∀ M N : A, HEq (mu (Q.obj M) (Q.obj N)) (Q.map (mu₀ M N)))
    (M N : A) :
    HEq (I.map (mu (Q.obj M) (Q.obj N))) (QA.map (J.map (mu₀ M N))) := by
  have hs := (congrArg F.obj (Functor.congr_obj hT (M, N))).trans (hF (S.obj (M, N)))
  have hp : (F.obj (Q.obj M), F.obj (Q.obj N)) =
      (Q.obj (F₀.obj M), Q.obj (F₀.obj N)) := Prod.ext (hF M) (hF N)
  have ht := (congrArg T.obj hp).trans (Functor.congr_obj hT (F₀.obj M, F₀.obj N))
  exact (map_heq I hs ht (hmu M N)).trans (Functor.hcongr_hom hI (mu₀ M N))

private theorem component_transport_extended
    {A : Type u} [Category A] {B : Type v} [Category B]
    {C : Type r} [Category C] {D : Type w} [Category D]
    (Q : A ⥤ B) (I : B ⥤ D) (J : A ⥤ C) (QA : C ⥤ D)
    (S : A × A ⥤ A) (T : B × B ⥤ B) (F₀ : A ⥤ A) (F : B ⥤ B)
    (hI : Q ⋙ I = J ⋙ QA) (hT : (Q.prod Q) ⋙ T = S ⋙ Q)
    (hF : ∀ M : A, F.obj (Q.obj M) = Q.obj (F₀.obj M))
    (mu₀ : ∀ M N : A, F₀.obj (S.obj (M, N)) ⟶ S.obj (F₀.obj M, F₀.obj N))
    (mu : ∀ M N : B, F.obj (T.obj (M, N)) ⟶ T.obj (F.obj M, F.obj N))
    (hmu : ∀ M N : A, HEq (mu (Q.obj M) (Q.obj N)) (Q.map (mu₀ M N)))
    (U : D × D ⥤ D) (G : D ⥤ D)
    (nu : U ⋙ G ⟶ (G.prod G) ⋙ U)
    (hnu : ∀ M N : A, HEq (QA.map (J.map (mu₀ M N)))
      (nu.app (QA.obj (J.obj M), QA.obj (J.obj N)))) (M N : A) :
    HEq (I.map (mu (Q.obj M) (Q.obj N)))
      (nu.app (I.obj (Q.obj M), I.obj (Q.obj N))) := by
  have hp : (I.obj (Q.obj M), I.obj (Q.obj N)) =
      (QA.obj (J.obj M), QA.obj (J.obj N)) :=
    Prod.ext (Functor.congr_obj hI M) (Functor.congr_obj hI N)
  exact (component_transport Q I J QA S T F₀ F hI hT hF mu₀ mu hmu M N).trans
    ((hnu M N).trans (nat_app_heq nu hp).symm)

/-- Transport both arrows of a bifunctor without clearing denominators. -/
private theorem pair_map_heq {C : Type u} [Category C] {D : Type v} [Category D]
    (F : C × C ⥤ D) {X X' Y Y' Z Z' W W' : C}
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') (hw : W = W')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ W} {g' : Z' ⟶ W'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (F.map (Prod.mkHom f g)) (F.map (Prod.mkHom f' g')) := by
  subst_vars
  rfl

/-- Compose the tensor-functor and pullback-component identifications. -/
private theorem tensor_structure_heq
    {C : Type u} [Category C] {D : Type v} [Category D]
    (I : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (mu : T ⋙ F ⟶ (F.prod F) ⋙ T) (nu : U ⋙ G ⟶ (G.prod G) ⋙ U)
    (hT : T ⋙ I = (I.prod I) ⋙ U)
    (hF : ∀ M : C, G.obj (I.obj M) = I.obj (F.obj M))
    (hmu : ∀ M N : C, HEq (I.map (mu.app (M, N))) (nu.app (I.obj M, I.obj N)))
    (M N : C) (f : F.obj M ⟶ M) (g : F.obj N ⟶ N)
    (f' : G.obj (I.obj M) ⟶ I.obj M) (g' : G.obj (I.obj N) ⟶ I.obj N)
    (hf : HEq (I.map f) f') (hg : HEq (I.map g) g') :
    HEq (I.map (mu.app (M, N) ≫ T.map (Prod.mkHom f g)))
      (nu.app (I.obj M, I.obj N) ≫ U.map (Prod.mkHom f' g')) := by
  rw [I.map_comp]
  have hm := Functor.hcongr_hom hT (Prod.mkHom f g)
  have hm' := pair_map_heq U (hF M).symm rfl (hF N).symm rfl hf hg
  exact heq_comp
    ((hF (T.obj (M, N))).symm.trans
      (congrArg G.obj (Functor.congr_obj hT (M, N))))
    ((Functor.congr_obj hT (F.obj M, F.obj N)).trans
      (congrArg U.obj (Prod.ext (hF M).symm (hF N).symm)))
    (Functor.congr_obj hT (M, N)) (hmu M N) (hm.trans hm')

/-- Transport the normalization equation through the ambient inclusion. -/
private theorem tensor_precomp_transport
    {A : Type u} [Category A] {B : Type v} [Category B]
    {C : Type r} [Category C] (Q : A ⥤ B) (I : B ⥤ C) (H : A ⥤ C)
    (S : A × A ⥤ A) (T : B × B ⥤ B) (U : C × C ⥤ C)
    (hT : (Q.prod Q) ⋙ T = S ⋙ Q) (hI : Q ⋙ I = H)
    (hbase : S ⋙ H = (H.prod H) ⋙ U) :
    (Q.prod Q) ⋙ (T ⋙ I) = (Q.prod Q) ⋙ ((I.prod I) ⋙ U) := by
  calc
    (Q.prod Q) ⋙ (T ⋙ I) = S ⋙ (Q ⋙ I) := congrArg (fun F ↦ F ⋙ I) hT
    _ = S ⋙ H := congrArg (fun F ↦ S ⋙ F) hI
    _ = (H.prod H) ⋙ U := hbase
    _ = ((Q ⋙ I).prod (Q ⋙ I)) ⋙ U := congrArg (fun F ↦ (F.prod F) ⋙ U) hI.symm
    _ = (Q.prod Q) ⋙ ((I.prod I) ⋙ U) := rfl

/-- Compose two functorial tensor identifications. -/
private theorem tensor_functor_combine
    {A : Type u} [Category A] {B : Type v} [Category B]
    {C : Type r} [Category C] (J : A ⥤ B) (Q : B ⥤ C)
    (S : A × A ⥤ A) (T : B × B ⥤ B) (U : C × C ⥤ C)
    (hJ : S ⋙ J = (J.prod J) ⋙ T) (hQ : T ⋙ Q = (Q.prod Q) ⋙ U) :
    S ⋙ (J ⋙ Q) = ((J ⋙ Q).prod (J ⋙ Q)) ⋙ U := by
  calc
    S ⋙ (J ⋙ Q) = ((J.prod J) ⋙ T) ⋙ Q := congrArg (fun F ↦ F ⋙ Q) hJ
    _ = (J.prod J) ⋙ ((Q.prod Q) ⋙ U) := congrArg (fun F ↦ (J.prod J) ⋙ F) hQ
    _ = ((J ⋙ Q).prod (J ⋙ Q)) ⋙ U := rfl

/-- Apply the comparison to the tensor of two arbitrary Weil structures. -/
private theorem tensor_weil_structure_heq
    {C : Type u} [Category C] {D : Type v} [Category D]
    (I : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (mu : T ⋙ F ≅ (F.prod F) ⋙ T) (nu : U ⋙ G ≅ (G.prod G) ⋙ U)
    (hT : T ⋙ I = (I.prod I) ⋙ U)
    (hF : ∀ M : C, G.obj (I.obj M) = I.obj (F.obj M))
    (hmu : ∀ M N : C, HEq (I.map (mu.hom.app (M, N)))
      (nu.hom.app (I.obj M, I.obj N)))
    (weilst : ∀ M : Endofunctor.IsoAlgebra F, G.obj (I.obj M.carrier) ≅ I.obj M.carrier)
    (hw : ∀ M : Endofunctor.IsoAlgebra F, HEq (weilst M).hom (I.map M.str.hom))
    (K L : Endofunctor.IsoAlgebra F) :
    HEq (weilst (Endofunctor.IsoAlgebra.mk (F := F) (T.obj (K.carrier, L.carrier))
      (mu.app (K.carrier, L.carrier) ≪≫ T.mapIso (K.str.prod L.str)))).hom
      (nu.app (I.obj K.carrier, I.obj L.carrier) ≪≫
        U.mapIso ((weilst K).prod (weilst L))).hom := by
  refine (hw _).trans ?_
  exact tensor_structure_heq I F G T U mu.hom nu.hom hT hF hmu
    K.carrier L.carrier K.str.hom L.str.hom (weilst K).hom (weilst L).hom
    (hw K).symm (hw L).symm

private theorem map_iso_transport_heq
    {C : Type u} [Category C] {D : Type v} [Category D] (I : C ⥤ D)
    {M N : C} {Y : D} (h : Y = I.obj M) (e : M ≅ N) :
    HEq (eqToIso h ≪≫ I.mapIso e).hom (I.map e.hom) := by
  exact eqToHom_comp_heq (I.map e.hom) h

/-- Restrict an ambient isomorphism and then include it in the intermediate subcategory. -/
private theorem lift_iso_heq
    {C : Type u} [Category C] (P Q : ObjectProperty C)
    (hPQ : ∀ M : P.FullSubcategory, Q M.obj)
    (M N : P.FullSubcategory) (hM : Q M.obj) (hN : Q N.obj)
    (e : (⟨M.obj, hM⟩ : Q.FullSubcategory) ≅ ⟨N.obj, hN⟩) :
    HEq ((ObjectProperty.lift Q P.ι hPQ).map
      (ObjectProperty.isoMk P (Q.ι.mapIso e)).hom) e.hom := by
  rfl

private theorem restrict_completed_tensor
    {C : Type u} [Category C] (P Q : ObjectProperty C)
    (H : C × C ⥤ Q.FullSubcategory)
    (hPQ : ∀ M : P.FullSubcategory, Q M.obj)
    (hHP : ∀ MN : P.FullSubcategory × P.FullSubcategory,
      P (H.obj (MN.1.obj, MN.2.obj)).obj) :
    let I := ObjectProperty.lift Q P.ι hPQ
    ObjectProperty.lift P ((P.ι.prod P.ι) ⋙ H ⋙ Q.ι) hHP ⋙ I =
      (I.prod I) ⋙ ((Q.ι.prod Q.ι) ⋙ H) := by
  dsimp only
  refine Functor.hext (fun _ ↦ ObjectProperty.FullSubcategory.ext rfl) ?_
  intro MN MN' f
  rfl

/-- Localization precomposition is injective in both variables, by currying. -/
private theorem product_precomp_injective
    {A : Type r} [CommRing A] {C : Type u} [Category C] [Preadditive C] [Linear A C]
    (p : A) {D : Type v} [Category D]
    (F G : ScalarLocalization A C p × ScalarLocalization A C p ⥤ D)
    (h : ((ScalarLocalization.localization A C p).prod
      (ScalarLocalization.localization A C p)) ⋙ F =
        ((ScalarLocalization.localization A C p).prod
          (ScalarLocalization.localization A C p)) ⋙ G) : F = G := by
  apply Functor.curry_obj_injective
  apply scalarLocalization_precomp_injective p
  apply Functor.flip_injective
  apply scalarLocalization_precomp_injective p
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

end TensorTransport

namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- Package the specified geometric fibre as a finite-type space of the operation datum.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge). -/
def sfProjectionWeilSpace (D : FiniteFieldDatum.{u})
    (W₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] :
    SixFunctorSpace D :=
  ⟨D.geometricFiber W₀, by
    change LocallyOfFiniteType (pullback.snd W₀.hom _) ∧
      QuasiCompact (pullback.snd W₀.hom _)
    exact ⟨inferInstance, inferInstance⟩⟩

/-- Geometric base change of the given morphism, retaining its map over the base field.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge). -/
def sfProjectionWeilMap (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    sfProjectionWeilSpace D X₀ ⟶ sfProjectionWeilSpace D Y₀ :=
  ObjectProperty.homMk
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀)

/-- IsSeparated is preserved by the specified geometric base change.
Source: projection-formula proof, geometric-fibre hypotheses
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof: the underlying map is the pullback of f₀.left along the base extension.
Apply stability under base change of IsSeparated. -/
@[instance] theorem sfProjectionWeilMap_isSeparated (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] :
    IsSeparated (sfProjectionWeilMap D f₀).hom.left := by
  exact MorphismProperty.overPullbackMap (P := @IsSeparated)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- LocallyOfFiniteType is preserved by the specified geometric base change.
Source: projection-formula proof, geometric-fibre hypotheses
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof: the underlying map is the pullback of f₀.left along the base extension.
Apply stability under base change of LocallyOfFiniteType. -/
@[instance] theorem sfProjectionWeilMap_locallyOfFiniteType (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (sfProjectionWeilMap D f₀).hom.left := by
  exact MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- QuasiCompact is preserved by the specified geometric base change.
Source: projection-formula proof, geometric-fibre hypotheses
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof: the underlying map is the pullback of f₀.left along the base extension.
Apply stability under base change of QuasiCompact. -/
@[instance] theorem sfProjectionWeilMap_quasiCompact (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] :
    QuasiCompact (sfProjectionWeilMap D f₀).hom.left := by
  exact MorphismProperty.overPullbackMap (P := @QuasiCompact)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- The integral categories use the same completed coefficients and finite reductions.
The first equation fixes the comparison by every quotient projection; the second clause
identifies the full subcategories, including the compatible etale-origin condition.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, step 1: finite-type geometric fibres are Noetherian and finite-dimensional,
and ell is invertible because it differs from the base characteristic. Apply
lem-pur-rational-lattice-adic-domain and integralStratifiedPerfectDetailed. Their
coefficient comparison is fixed by every quotient projection, so the reduction functors
and their compatible etale-origin witnesses are transported unchanged. The raw rational
category of def-wf-weil-category uses exactly this integral full subcategory. -/
theorem sfProjectionWeilCoefficientBridge (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (W₀ : Over (Spec (.of D.k₀))) [IsSeparated W₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E : Type u) [Field E] [Algebra (Padic c.l) E] [FiniteDimensional (Padic c.l) E] :
    (∀ n : ℕ,
      (integralDetailedCoefficientComparison (D.geometricFiber W₀).left c.l E).hom ≫
          limit.π (integralCoefficientSheafSystem c.l E (D.geometricFiber W₀).left) (op n) =
        (adicLisseForget (D.geometricFiber W₀).left).map
            (pbcAdicProjection (D.geometricFiber W₀).left (pbcIntegralDatum c.l E) n) ≫
          (integralDetailedLevelComparison (D.geometricFiber W₀).left c.l E n).hom) ∧
    (∀ K : DerivedCategory (scalarReductionSource.{u, u} c.l E (D.geometricFiber W₀).left),
      sfIntegralConstructible c.l E (D.geometricFiber W₀).left K ↔
        PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left (pbcIntegralDatum c.l E)
          ((integralDetailedTransport (D.geometricFiber W₀).left c.l E).obj K)) := by
  let W := sfProjectionWeilSpace D W₀
  let : LocallyOfFiniteType W.obj.hom := W.property.1
  let : QuasiCompact W.obj.hom := W.property.2
  have : IsNoetherian W.obj.left :=
    isNoetherian_of_locallyOfFiniteType W.obj.hom
  have hdim := exists_topologicalKrullDim_le W.obj.hom
  have hunit : IsUnit (c.l : Γ(W.obj.left, ⊤)) := by
    simpa only [map_natCast] using
      (PurCompactSupport.coefficientPrimeUnit c.l D c.different).map
        ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ W.obj.hom.appTop).hom
  exact ⟨(integralDetailedCoefficientComparison_exists _ c.l E).exists.choose_spec,
    fun K ↦ integralStratifiedPerfectDetailed _ c.l E hdim hunit K⟩

/-- Both tensor models are integral bounded constructible and the canonical unit
is invertible for every pair, without imposing any Weil structure on the inputs.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, step 2: use lem-wf-constructible-tensor-koszul-unit. Its normalized comparison
identifies the quotient completion map with the intrinsic unit. The ordinary tensor
is complete and constructible; so is its completion, and that unit is invertible. -/
theorem sfProjectionWeilIntegralTensorDomains (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (W₀ : Over (Spec (.of D.k₀))) [IsSeparated W₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (M N : WfTensorCompletion.Integral D c W₀ E) :
    PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left
        (pbcStageDatum.{u} c.l c.Qbar E)
        ((WfTensorCompletion.ordinaryAmbient D c W₀ E).obj (M, N)) ∧
    PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left
        (pbcStageDatum.{u} c.l c.Qbar E)
        ((WfTensorCompletion.completedAmbient D c W₀ E).obj (M, N)) ∧
    IsIso ((WfTensorCompletion.chi D c W₀ E).app (M, N)) := by
  have h := (WfTensorCompletion.integral D c W₀ E).1 (M, N)
  refine ⟨h.1, h.2.1, ?_⟩
  have : IsIso ((ObjectProperty.ι _).map
      ((WfTensorCompletion.chi D c W₀ E).app (M, N))) := h.2.2
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- The canonical integral tensor comparison is invertible and Frobenius-equivariant.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, steps 2--3: lem-wf-constructible-tensor-koszul-unit identifies the quotient-tower
map with the intrinsic unit after the quotient/Koszul comparison. Both tensors are
constructible and the unit is invertible. Apply lem-wf-tensor-completion-frobenius:
exact geometric-Frobenius transport preserves the quotient projections, uniformizer,
Koszul inclusions and the strict fibre unit (u,0). Its unit square and naturality for
the tensor of the two Weil maps give the displayed commuting equation. -/
theorem sfProjectionWeilIntegralTensorBridge (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (W₀ : Over (Spec (.of D.k₀))) [IsSeparated W₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (M N : WfTensorCompletion.Integral D c W₀ E)
    (phi : (WfTensorCompletion.pullback D c W₀ E).obj M ≅ M)
    (psi : (WfTensorCompletion.pullback D c W₀ E).obj N ≅ N) :
    IsIso ((WfTensorCompletion.chi D c W₀ E).app (M, N)) ∧
    (WfTensorCompletion.ordinaryMu D c W₀ E M N).hom ≫
        (WfTensorCompletion.ordinary D c W₀ E).map (Prod.mkHom phi.hom psi.hom) ≫
        (WfTensorCompletion.chi D c W₀ E).app (M, N) =
      (WfTensorCompletion.pullback D c W₀ E).map
          ((WfTensorCompletion.chi D c W₀ E).app (M, N)) ≫
        (WfTensorCompletion.completedMu D c W₀ E M N).hom ≫
        (WfTensorCompletion.completed D c W₀ E).map (Prod.mkHom phi.hom psi.hom) := by
  exact WfTensorCompletion.integral_equivariance D c W₀ E M N phi psi

section RationalNormalization
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (p : A)

/-- The explicit rational tensor restricts to localization of the integral tensor. -/
private theorem rational_tensor_localization :
    let Q := ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p
    (Q.prod Q) ⋙ wfRationalTensor X d r a ha p = wfIntegralTensor X d r a ha ⋙ Q := by
  dsimp only
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro MN MN' fg
  rcases MN with ⟨M, N⟩
  rcases MN' with ⟨M', N'⟩
  rcases fg with ⟨f, g⟩
  apply heq_of_eq
  have ht := wfRationalTensorHom_tmul X d r a ha p
    (⟨M⟩) (⟨M'⟩) (⟨N⟩) (⟨N'⟩) f g 1 1
  simp only [one_mul] at ht
  exact ht

/-- The chosen rational pullback comparison has the prescribed integral components. -/
private theorem rational_tensor_pullback_hom_heq (e : Aut X)
    (M N : WfCompleteCategory X d r a ha) :
    let Q := ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p
    HEq (Q.map (wfIntegralTensorPullback X d r a ha e M N).hom)
      ((wfRationalTensorPullback X d r a ha e p).hom.app (Q.obj M, Q.obj N)) := by
  have hm := (wfRationalTensorPullback_exists X d r a ha e p).exists.choose_spec
  have ht := hm M N
  have hh := heq_of_eq ht
  simpa only [wfRationalTensorPullback, Functor.comp_obj, Functor.prod_obj,
    wfRationalTensor, wfRationalTensorObj, wfAmbientRationalPullback,
    ScalarLocalization.map, ScalarLocalization.localization] using hh.symm

/-- Compatibility of a normalized rational tensor with the transported Weil structures. -/
private theorem rational_weil_tensor_structure (e : Aut X)
    (S : PbcRationalCategory X d p × PbcRationalCategory X d p ⥤
      PbcRationalCategory X d p)
    (mu : S ⋙ pbcRationalIsoPullback e d p ≅
      ((pbcRationalIsoPullback e d p).prod (pbcRationalIsoPullback e d p)) ⋙ S)
    (hT : S ⋙ wfConstructibleInclusion X d r a ha p =
      ((wfConstructibleInclusion X d r a ha p).prod
        (wfConstructibleInclusion X d r a ha p)) ⋙ wfRationalTensor X d r a ha p)
    (hmu : ∀ M N : PbcRationalCategory X d p,
      HEq ((wfConstructibleInclusion X d r a ha p).map (mu.hom.app (M, N)))
        ((wfRationalTensorPullback X d r a ha e p).hom.app
          ((wfConstructibleInclusion X d r a ha p).obj M,
            (wfConstructibleInclusion X d r a ha p).obj N))) :
    let I := wfConstructibleInclusion X d r a ha p
    let W (M : Endofunctor.IsoAlgebra (pbcRationalIsoPullback e d p)) :=
      eqToIso (wfConstructiblePullback_obj X d r a ha e p M.carrier) ≪≫ I.mapIso M.str
    ∀ K L : Endofunctor.IsoAlgebra (pbcRationalIsoPullback e d p),
      HEq (W (Endofunctor.IsoAlgebra.mk (F := pbcRationalIsoPullback e d p)
        (S.obj (K.carrier, L.carrier))
        (mu.app (K.carrier, L.carrier) ≪≫ S.mapIso (K.str.prod L.str)))).hom
        ((wfRationalTensorPullback X d r a ha e p).app
          (I.obj K.carrier, I.obj L.carrier) ≪≫
          (wfRationalTensor X d r a ha p).mapIso ((W K).prod (W L))).hom := by
  let I := wfConstructibleInclusion X d r a ha p
  exact tensor_weil_structure_heq I (pbcRationalIsoPullback e d p)
    (wfAmbientRationalPullback X d r a ha e p) S (wfRationalTensor X d r a ha p)
    mu (wfRationalTensorPullback X d r a ha e p) hT
    (wfConstructiblePullback_obj X d r a ha e p) hmu
    (fun M ↦ eqToIso (wfConstructiblePullback_obj X d r a ha e p M.carrier) ≪≫
      I.mapIso M.str)
    (fun M ↦ map_iso_transport_heq I
      (wfConstructiblePullback_obj X d r a ha e p M.carrier) M.str)

end RationalNormalization

section TensorNormalization
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open WfTensorCompletion

attribute [local irreducible] wfRationalTensor wfConstructibleInclusion
  wfRationalTensorPullback wfWeilStructure wfTensorFrobenius
  ScalarLocalization.category ScalarLocalization.preadditive ScalarLocalization.composition
  ScalarLocalization.linear ScalarLocalization.linearOriginal
  pbcIntegralLinear pbcCompletedDerivedLinear pbcCompletedModulesLinear
  wfPullbackCompletion proEtaleCanonicalTensorComparison pbcCompletedScalarSections
  wfCompletionObj intrinsicCompletion intrinsicCompletionUnit

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

private theorem integral_tensor_inclusion :
    completed D c X₀ E ⋙ wfIntegralConstructibleInclusion (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E) 1
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
      (wfUniformizer_generates D c E) =
    ((wfIntegralConstructibleInclusion (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E) 1
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
      (wfUniformizer_generates D c E)).prod
      (wfIntegralConstructibleInclusion (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E) 1
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
      (wfUniformizer_generates D c E))) ⋙
    wfIntegralTensor (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
      (wfUniformizer_generates D c E) := by
  exact restrict_completed_tensor _ _
    (wfOrdinaryDerivedTensor _ _ ⋙ completion D c X₀ E)
    (wfConstructible_complete _ _ _ _ _)
    (fun MN ↦ (integral D c X₀ E).1 MN |>.2.1)

private theorem normalized_tensor (R : RationalComparison D c X₀ E)
    (hR : R.Normalized D c X₀ E) :
    R.completed ⋙ wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E) =
      ((wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).prod
        (wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E))) ⋙
          wfTensor D c X₀ E := by
  let X := (D.geometricFiber X₀).left
  let d := pbcStageDatum.{u} c.l c.Qbar E
  let p := pbcStageUniformizer.{u} c.l c.Qbar E
  let a := fun _ : Fin 1 ↦ p
  let ha := wfUniformizer_generates D c E
  let I := wfConstructibleInclusion X d 1 a ha p
  let J := wfIntegralConstructibleInclusion X d 1 a ha
  let Q := localization D c X₀ E
  let QA := ScalarLocalization.localization _ (WfCompleteCategory X d 1 a ha) p
  let C := WfTensorCompletion.completed D c X₀ E
  let T := wfTensor D c X₀ E
  have hI : Q ⋙ I = J ⋙ QA := by
    simpa only [I, wfConstructibleInclusion] using
      (wfConstructibleInclusion_exists X d 1 a ha p).exists.choose_spec
  let S := wfIntegralTensor X d 1 a ha
  have hC : C ⋙ J = (J.prod J) ⋙ S := integral_tensor_inclusion D c X₀ E
  have hbase : C ⋙ (J ⋙ QA) = ((J ⋙ QA).prod (J ⋙ QA)) ⋙ T :=
    tensor_functor_combine J QA C S T hC
      (rational_tensor_localization X d 1 a ha p).symm
  apply product_precomp_injective p
  exact tensor_precomp_transport Q I (J ⋙ QA) C R.completed T hR.2.1 hI hbase

section TensorComponents
attribute [local semireducible] wfRationalTensor ScalarLocalization.category

private theorem included_integral_mu (M N : Integral D c X₀ E) :
    HEq ((ScalarLocalization.localization _ (WfCompleteCategory ((D.geometricFiber X₀).left)
        (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ (pbcStageUniformizer.{u} c.l c.Qbar E))
        (wfUniformizer_generates D c E)) (pbcStageUniformizer.{u} c.l c.Qbar E)).map
        ((wfIntegralConstructibleInclusion ((D.geometricFiber X₀).left) (pbcStageDatum.{u} c.l
        c.Qbar E) 1 (fun _ : Fin 1 ↦ (pbcStageUniformizer.{u} c.l c.Qbar E))
        (wfUniformizer_generates D c E)).map (completedMu D c X₀ E M N).hom))
      ((wfRationalTensorPullback ((D.geometricFiber X₀).left) (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ (pbcStageUniformizer.{u} c.l c.Qbar E)) (wfUniformizer_generates D c E)
        (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).hom.app
        ((ScalarLocalization.localization _ (WfCompleteCategory ((D.geometricFiber X₀).left)
        (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ (pbcStageUniformizer.{u} c.l c.Qbar E))
        (wfUniformizer_generates D c E)) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj
        ((wfIntegralConstructibleInclusion ((D.geometricFiber X₀).left) (pbcStageDatum.{u} c.l
        c.Qbar E) 1 (fun _ : Fin 1 ↦ (pbcStageUniformizer.{u} c.l c.Qbar E))
        (wfUniformizer_generates D c E)).obj M), (ScalarLocalization.localization _
        (WfCompleteCategory ((D.geometricFiber X₀).left) (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ :
        Fin 1 ↦ (pbcStageUniformizer.{u} c.l c.Qbar E)) (wfUniformizer_generates D c E))
        (pbcStageUniformizer.{u} c.l c.Qbar E)).obj ((wfIntegralConstructibleInclusion
        ((D.geometricFiber X₀).left) (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦
        (pbcStageUniformizer.{u} c.l c.Qbar E)) (wfUniformizer_generates D c E)).obj N))) := by
  let X := (D.geometricFiber X₀).left
  let d := pbcStageDatum.{u} c.l c.Qbar E
  let p := pbcStageUniformizer.{u} c.l c.Qbar E
  let a := fun _ : Fin 1 ↦ p
  let ha := wfUniformizer_generates D c E
  let J := wfIntegralConstructibleInclusion X d 1 a ha
  let QA := ScalarLocalization.localization _ (WfCompleteCategory X d 1 a ha) p
  let C := WfTensorCompletion.completed D c X₀ E
  let H := wfCompletePullback X d 1 a ha (D.geometricFrobenius X₀)
  let T := wfIntegralTensor X d 1 a ha
  let e := wfIntegralTensorPullback X d 1 a ha (D.geometricFrobenius X₀)
    (J.obj M) (J.obj N)
  have hx : J.obj ((pullback D c X₀ E).obj (C.obj (M, N))) =
      H.obj (T.obj (J.obj M, J.obj N)) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  have hy : J.obj (C.obj ((pullback D c X₀ E).obj M,
      (pullback D c X₀ E).obj N)) = T.obj (H.obj (J.obj M), H.obj (J.obj N)) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  have hj : HEq (J.map (completedMu D c X₀ E M N).hom) e.hom := by
    exact lift_iso_heq _ _ (wfConstructible_complete X d 1 a ha)
      ((pullback D c X₀ E).obj (C.obj (M, N)))
      (C.obj ((pullback D c X₀ E).obj M, (pullback D c X₀ E).obj N))
      (H.obj (T.obj (J.obj M, J.obj N))).property
      (T.obj (H.obj (J.obj M), H.obj (J.obj N))).property e
  have hq := map_heq QA hx hy hj
  exact hq.trans
    (rational_tensor_pullback_hom_heq X d 1 a ha p (D.geometricFrobenius X₀)
      (J.obj M) (J.obj N))


private theorem normalized_mu (R : RationalComparison D c X₀ E)
    (hR : R.Normalized D c X₀ E) (M N : Rational D c X₀ E) :
    HEq ((wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).map
          (R.completedMu.hom.app (M, N)))
      ((wfRationalTensorPullback (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
        (pbcStageUniformizer.{u} c.l c.Qbar E)).hom.app
          ((wfConstructibleInclusion (D.geometricFiber X₀).left
            (pbcStageDatum.{u} c.l c.Qbar E) 1
            (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj M,
          (wfConstructibleInclusion (D.geometricFiber X₀).left
            (pbcStageDatum.{u} c.l c.Qbar E) 1
            (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj N)) := by
  let X := (D.geometricFiber X₀).left
  let d := pbcStageDatum.{u} c.l c.Qbar E
  let p := pbcStageUniformizer.{u} c.l c.Qbar E
  let a := fun _ : Fin 1 ↦ p
  let ha := wfUniformizer_generates D c E
  let I := wfConstructibleInclusion X d 1 a ha p
  let J := wfIntegralConstructibleInclusion X d 1 a ha
  let Q := localization D c X₀ E
  let QA := ScalarLocalization.localization _ (WfCompleteCategory X d 1 a ha) p
  let C := WfTensorCompletion.completed D c X₀ E
  let F := weilFrobeniusPullback D c X₀ E
  let mu := wfRationalTensorPullback X d 1 a ha (D.geometricFrobenius X₀) p
  have hI : Q ⋙ I = J ⋙ QA := by
    simpa only [I, wfConstructibleInclusion] using
      (wfConstructibleInclusion_exists X d 1 a ha p).exists.choose_spec
  exact component_transport_extended Q I J QA C R.completed (pullback D c X₀ E) F
    hI hR.2.1 (fun _ ↦ rfl)
    (fun M N ↦ (completedMu D c X₀ E M N).hom)
    (fun M N ↦ R.completedMu.hom.app (M, N))
    (fun M N ↦ (hR.2.2 M N).2.2)
    (wfRationalTensor X d 1 a ha p)
    (wfAmbientRationalPullback X d 1 a ha (D.geometricFrobenius X₀) p) mu.hom
    (included_integral_mu D c X₀ E) M.obj N.obj

end TensorComponents

attribute [local semireducible] wfWeilStructure wfTensorFrobenius


/-- Rationalization preserves the normalized comparison, with the specified Weil tensor.
The last clause compares its Frobenius map in the faithful ambient coefficient model;
it does not require either rational input Weil isomorphism to lift integrally.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, steps 3 and 5: apply wfTensorCompletionFrobenius, which clears denominators
using naturality for arbitrary integral arrows rather than integral isomorphisms.
Its normalization fixes the completed tensor, completion unit and pullback comparison
on every unchanged integral object. Under wfConstructibleInclusion these are exactly
the functor wfTensor and the composite wfTensorFrobenius of def-wf-tensor-product.
Thus the rational commuting equation lifts the canonical chi to a Weil isomorphism
and identifies the actual tensor structure, including denominators. -/
theorem sfProjectionWeilRationalTensorBridge (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (W₀ : Over (Spec (.of D.k₀))) [IsSeparated W₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃ R : WfTensorCompletion.RationalComparison D c W₀ E,
      R.Normalized D c W₀ E ∧ ∀ K L : WeilD D c W₀ E,
        (∃ e : R.ordinaryPair D c W₀ E K L ≅ R.completedPair D c W₀ E K L,
          e.hom.hom.f = R.chi.hom.app (K.carrier, L.carrier)) ∧
        HEq (wfWeilStructure D c W₀ E (R.completedPair D c W₀ E K L)).hom
          (wfTensorFrobenius D c W₀ E K L).hom := by
  exact comparison_exists _ _ _ _ (wfTensorCompletionFrobenius_exists D c W₀ E)
    (fun R hR K L ↦ by
      exact rational_weil_tensor_structure (D.geometricFiber W₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)
        (D.geometricFrobenius W₀) R.completed R.completedMu
        (normalized_tensor D c W₀ E R hR) (normalized_mu D c W₀ E R hR) K L)

end TensorNormalization

/-- The same tensor bridge after arbitrary passage to a common finite coefficient field.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, steps 3 and 5: use wfTensorCompletionCommonField after transporting both inputs
by the actual Weil scalar extensions. The specified normalized chi is a Weil
isomorphism at G. The common-stage inclusion preserves it and its inverse. This works
also for E=F=G and requires integral representatives only for the underlying objects. -/
theorem sfProjectionWeilCommonTensorBridge (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (W₀ : Over (Spec (.of D.k₀))) [IsSeparated W₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E F G : Padic.FiniteCoefficientFields c.l c.Qbar) (h : E ≤ G) (k : F ≤ G)
    (K : WeilD D c W₀ E) (L : WeilD D c W₀ F)
    (R : WfTensorCompletion.RationalComparison D c W₀ G) (hR : R.Normalized D c W₀ G) :
    ∃ e : R.ordinaryPair D c W₀ G ((weilScalarExtension D c W₀ h).obj K)
          ((weilScalarExtension D c W₀ k).obj L) ≅
        R.completedPair D c W₀ G ((weilScalarExtension D c W₀ h).obj K)
          ((weilScalarExtension D c W₀ k).obj L),
      e.hom.hom.f = R.chi.hom.app
        (((weilScalarExtension D c W₀ h).obj K).carrier,
          ((weilScalarExtension D c W₀ k).obj L).carrier) ∧
      ∃ ebar : ((weilScalarSystem D c W₀).ι G).obj
          (R.ordinaryPair D c W₀ G ((weilScalarExtension D c W₀ h).obj K)
            ((weilScalarExtension D c W₀ k).obj L)) ≅
        ((weilScalarSystem D c W₀).ι G).obj
          (R.completedPair D c W₀ G ((weilScalarExtension D c W₀ h).obj K)
            ((weilScalarExtension D c W₀ k).obj L)),
        ebar = ((weilScalarSystem D c W₀).ι G).mapIso e := by
  exact wfTensorCompletionCommonField D c W₀ E F G h k K L R hR

/-- Completed scalar extension retains the identified integral coefficient domain.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, steps 1 and 5: lem-weil-integral-scalar-extension-constructible preserves the
intrinsic integral predicate. Apply the projection-normalized coefficient bridge at F
on the same geometric fibre. Thus the extended object has the same finite derived
reductions and compatible etale origins in the Weil coefficient convention. -/
theorem sfProjectionWeilScalarDomainBridge (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (W₀ : Over (Spec (.of D.k₀))) [IsSeparated W₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (E : Type u) [Field E] [Algebra (Padic c.l) E] [FiniteDimensional (Padic c.l) E]
    (F : Type u) [Field F] [Algebra (Padic c.l) F] [FiniteDimensional (Padic c.l) F]
    (i : E →ₐ[Padic c.l] F)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E (D.geometricFiber W₀).left))
    (_hK : sfIntegralConstructible c.l E (D.geometricFiber W₀).left K) :
    sfIntegralConstructible c.l F (D.geometricFiber W₀).left
        ((integralScalarExtension c.l E F i (D.geometricFiber W₀).left).obj K) ∧
    PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left (pbcIntegralDatum c.l F)
      ((integralDetailedTransport (D.geometricFiber W₀).left c.l F).obj
        ((integralScalarExtension c.l E F i (D.geometricFiber W₀).left).obj K)) := by
  have h := sfIntegralScalarExtension_constructible D.p c.l c.different E F i
    (D.geometricFiber W₀).left K _hK
  exact ⟨h, ((sfProjectionWeilCoefficientBridge D c W₀ F).2 _).mp h⟩

/-- The five actual integral outputs lie in the constructible domains, and agree
with the operation datum and its rationalization. The ambient proper/open functor
is identified with the specified reduction-limit compact-support construction.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, step 4: apply lem-pur-integral-operations-preserve-constructible to L for P,
and to K,P for H. Apply lem-sf-integral-compact-support-constructible to K and H
for U and V. Apply the tensor clause again to U,L for B. These results apply to
finite-type schemes without separated structure maps. The given f is separated
and finite type by base change. The normalized datum comparisons identify these
outputs with its pullback, tensors and compact support; sfQcqsCompactSupportRealization
identifies the completed proper/open realization with the strict reduction-limit
functor. Step 5: raw rationalization retains exactly these integral objects and
the datum's coefficient-model normalization identifies all five rational outputs.
No integral structure map is requested for a rational Weil input. -/
theorem sfProjectionWeilTensorDomainBridge (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (E : Type u) [Field E] [Algebra (Padic c.l) E]
    [FiniteDimensional (Padic c.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D c E n hn)
    (X₀ Y₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom] [IsSeparated Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (b : Compactification (sfProjectionWeilMap D f₀).hom.left)
    (K : sfIntegralConstructibleCategory c.l E (D.geometricFiber X₀).left)
    (L : sfIntegralConstructibleCategory c.l E (D.geometricFiber Y₀).left)
    (_hL : finiteTorConstructibleIntegral c.l E (D.geometricFiber Y₀).left L.obj) :
    ∃ P H : sfIntegralConstructibleCategory c.l E (D.geometricFiber X₀).left,
    ∃ U V B : sfIntegralConstructibleCategory c.l E (D.geometricFiber Y₀).left,
      P.obj = (integralDerivedPullback c.l E (sfProjectionWeilMap D f₀).hom.left).obj L.obj ∧
      H.obj = (integralCompletedTensor c.l E (D.geometricFiber X₀).left).obj (K.obj, P.obj) ∧
      Nonempty (U.obj ≅ (PurCompactSupport.image (PurCompactSupport.completed c.l E) b).obj
        K.obj) ∧
      Nonempty (V.obj ≅ (PurCompactSupport.image (PurCompactSupport.completed c.l E) b).obj
        H.obj) ∧
      B.obj = (integralCompletedTensor c.l E (D.geometricFiber Y₀).left).obj (U.obj, L.obj) ∧
      P = (S.higher.integral.pull (sfProjectionWeilMap D f₀)).obj L ∧
      H = ((S.higher.integralTensor (sfProjectionWeilSpace D X₀)).obj K).obj P ∧
      U = (S.higher.integral.support (sfProjectionWeilMap D f₀) b).obj K ∧
      V = (S.higher.integral.support (sfProjectionWeilMap D f₀) b).obj H ∧
      B = ((S.higher.integralTensor (sfProjectionWeilSpace D Y₀)).obj U).obj L ∧
      (S.higher.rational.pull (sfProjectionWeilMap D f₀)).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber Y₀).left).obj L) =
        (sfRationalConstructibleLocalization c.l E (D.geometricFiber X₀).left).obj P ∧
      ((S.higher.rationalTensor (sfProjectionWeilSpace D X₀)).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber X₀).left).obj K)).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber X₀).left).obj P) =
        (sfRationalConstructibleLocalization c.l E (D.geometricFiber X₀).left).obj H ∧
      (S.higher.rational.support (sfProjectionWeilMap D f₀) b).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber X₀).left).obj K) =
        (sfRationalConstructibleLocalization c.l E (D.geometricFiber Y₀).left).obj U ∧
      (S.higher.rational.support (sfProjectionWeilMap D f₀) b).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber X₀).left).obj H) =
        (sfRationalConstructibleLocalization c.l E (D.geometricFiber Y₀).left).obj V ∧
      ((S.higher.rationalTensor (sfProjectionWeilSpace D Y₀)).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber Y₀).left).obj U)).obj
          ((sfRationalConstructibleLocalization c.l E (D.geometricFiber Y₀).left).obj L) =
        (sfRationalConstructibleLocalization c.l E (D.geometricFiber Y₀).left).obj B := by
  let X := sfProjectionWeilSpace D X₀
  let Y := sfProjectionWeilSpace D Y₀
  let f := sfProjectionWeilMap D f₀
  have hl := PurCompactSupport.coefficientPrimeUnit c.l D c.different
  let : ∀ x : X.obj.left, Invertible (c.l : X.obj.left.residueField x) := fun x ↦
    (D.geometricFiber_coefficientPrimeInvertible c.l c.different X₀ x).invertible
  let : ∀ y : Y.obj.left, Invertible (c.l : Y.obj.left.residueField y) := fun y ↦
    (D.geometricFiber_coefficientPrimeInvertible c.l c.different Y₀ y).invertible
  let P := (S.higher.integral.pull f).obj L
  let H := ((S.higher.integralTensor X).obj K).obj P
  let U := (S.higher.integral.support f b).obj K
  let V := (S.higher.integral.support f b).obj H
  let B := ((S.higher.integralTensor Y).obj U).obj L
  have hP : P = (constructibleIntegralPullback c.l E f.hom.left).obj L := by
    exact Functor.congr_obj (S.higher.integralPullback f) L
  have hH : H = (constructibleIntegralTensor c.l E X.obj.left).obj (K, P) := by
    change ((S.higher.integralTensor X).obj K).obj P = _
    rw [S.higher.integralTensorNormalization X]
    rfl
  have hB : B = (constructibleIntegralTensor c.l E Y.obj.left).obj (U, L) := by
    change ((S.higher.integralTensor Y).obj U).obj L = _
    rw [S.higher.integralTensorNormalization Y]
    rfl
  have hs (A : sfIntegralConstructibleCategory c.l E X.obj.left) :
      ((S.higher.integral.support f b).obj A).obj ≅
        (PurCompactSupport.image (PurCompactSupport.completed c.l E) b).obj A.obj := by
    have he := (S.higher.supportConstruction f hl b).choose_spec.2.2.1 A
    have hf := sfCompactSupportFiniteIntegralFunctor_obj c.l D.k hl b E A
    exact eqToIso (congrArg (fun Z ↦ Z.obj) (he.trans hf.symm)) ≪≫
      (sfQcqsCompactSupportRealization c.l E D.k hl b).symm.app A
  refine ⟨P, H, U, V, B, congrArg (fun Z ↦ Z.obj) hP,
    congrArg (fun Z ↦ Z.obj) hH, ⟨hs K⟩, ⟨hs H⟩,
    congrArg (fun Z ↦ Z.obj) hB, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S.higher.rationalPullback f]
    exact (rationalDerivedPullback_existsUnique c.l E f.hom.left).exists.choose_spec.2.1
      ((sfRationalConstructibleLocalization c.l E Y.obj.left).obj L) |>.trans
        (congrArg (sfRationalConstructibleLocalization c.l E X.obj.left).obj hP.symm)
  · rw [S.higher.rationalTensorNormalization X]
    exact (rationalDerivedTensor_existsUnique c.l E X.obj.left).exists.choose_spec.1
      ((sfRationalConstructibleLocalization c.l E X.obj.left).obj K,
        (sfRationalConstructibleLocalization c.l E X.obj.left).obj P) |>.trans
          (congrArg (sfRationalConstructibleLocalization c.l E X.obj.left).obj hH.symm)
  · exact (S.higher.supportConstruction f hl b).choose_spec.2.2.2.choose_spec.2.2.1 K
      |>.trans (congrArg (sfRationalConstructibleLocalization c.l E Y.obj.left).obj
        ((S.higher.supportConstruction f hl b).choose_spec.2.2.1 K).symm)
  · exact (S.higher.supportConstruction f hl b).choose_spec.2.2.2.choose_spec.2.2.1 H
      |>.trans (congrArg (sfRationalConstructibleLocalization c.l E Y.obj.left).obj
        ((S.higher.supportConstruction f hl b).choose_spec.2.2.1 H).symm)
  · rw [S.higher.rationalTensorNormalization Y]
    exact (rationalDerivedTensor_existsUnique c.l E Y.obj.left).exists.choose_spec.1
      ((sfRationalConstructibleLocalization c.l E Y.obj.left).obj U,
        (sfRationalConstructibleLocalization c.l E Y.obj.left).obj L) |>.trans
          (congrArg (sfRationalConstructibleLocalization c.l E Y.obj.left).obj hB.symm)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def tensorStageIso (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (G : Padic.FiniteCoefficientFields l Ω)
    (M N : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X G) :
    (commonStageDerivedTensor l Ω X).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion G).obj M,
          (GeneralAlgebraicallyClosedCoefficients.inclusion G).obj N) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion G).obj
        ((rationalDerivedTensor l (Coefficient.{u} l Ω G) X).obj (M, N)) := by
  let A := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X
  let P := (A.ι G).obj M
  let Q := (A.ι G).obj N
  have hc : Padic.finiteCoefficientCompositum l Ω G G = G := by
    apply Subtype.ext
    simp only [Padic.finiteCoefficientCompositum, sup_idem]
  let h : (commonStageTensorObject l Ω X P Q).stage ≤ G := hc.le
  let e : A.T (le_refl G) ≅ 𝟭 _ :=
    eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω X).exists.choose_spec.1 G G (le_refl G)) ≪≫
        GeneralAlgebraicallyClosedCoefficients.unitor l Ω X G
  exact eqToIso ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 P Q) ≪≫
    A.isoToStage (commonStageTensorObject l Ω X P Q) h ≪≫
      (A.ι G).mapIso (commonStageTensorComparison l Ω X P Q G h ≪≫
        (rationalDerivedTensor l (Coefficient.{u} l Ω G) X).mapIso
          (Iso.prod (e.app M) (e.app N)))

/-- At every common finite field, all five outputs have integral constructible
models and their inclusions give precisely the common-stage operation outputs.
Source: projection-formula proof, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).
Proof, steps 4--5: apply the integral output argument at G to the coefficient stage
of S. Underlying inputs from different stages reach G by completed scalar extension,
which preserves constructibility. Raw rationalization keeps these integral objects.
The common-stage pullback and tensor normalizations and compact-support comparison
identify their inclusions with the five common-stage outputs. These are derived-object
isomorphisms and impose no condition on rational Weil structure maps. Together with
sfProjectionWeilCommonTensorBridge they give exactly the coefficient domains and
tensor Weil structure required by lem-fix-weil-operations. -/
theorem sfProjectionWeilCommonDomainBridge (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (E : Type u) [Field E] [Algebra (Padic c.l) E]
    [FiniteDimensional (Padic c.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D c E n hn)
    (G : Padic.FiniteCoefficientFields c.l c.Qbar)
    (X₀ Y₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom] [IsSeparated Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (b : Compactification (sfProjectionWeilMap D f₀).hom.left)
    (K : sfIntegralConstructibleCategory c.l (Coefficient.{u} c.l c.Qbar G)
      (D.geometricFiber X₀).left)
    (L : sfIntegralConstructibleCategory c.l (Coefficient.{u} c.l c.Qbar G)
      (D.geometricFiber Y₀).left)
    (_hL : finiteTorConstructibleIntegral c.l (Coefficient.{u} c.l c.Qbar G)
      (D.geometricFiber Y₀).left L.obj) :
    ∃ P H : sfIntegralConstructibleCategory c.l (Coefficient.{u} c.l c.Qbar G)
      (D.geometricFiber X₀).left,
    ∃ U V B : sfIntegralConstructibleCategory c.l (Coefficient.{u} c.l c.Qbar G)
      (D.geometricFiber Y₀).left,
      P.obj = (integralDerivedPullback c.l (Coefficient.{u} c.l c.Qbar G)
        (sfProjectionWeilMap D f₀).hom.left).obj L.obj ∧
      H.obj = (integralCompletedTensor c.l (Coefficient.{u} c.l c.Qbar G)
        (D.geometricFiber X₀).left).obj (K.obj, P.obj) ∧
      Nonempty (U.obj ≅ (PurCompactSupport.image
        (PurCompactSupport.completed c.l (Coefficient.{u} c.l c.Qbar G)) b).obj
        K.obj) ∧
      Nonempty (V.obj ≅ (PurCompactSupport.image
        (PurCompactSupport.completed c.l (Coefficient.{u} c.l c.Qbar G)) b).obj
        H.obj) ∧
      B.obj = (integralCompletedTensor c.l (Coefficient.{u} c.l c.Qbar G)
        (D.geometricFiber Y₀).left).obj (U.obj, L.obj) ∧
      P = ((S.closure.coefficientStages G).integral.pull (sfProjectionWeilMap D f₀)).obj L ∧
      H = (((S.closure.coefficientStages G).integralTensor
        (sfProjectionWeilSpace D X₀)).obj K).obj P ∧
      U = ((S.closure.coefficientStages G).integral.support (sfProjectionWeilMap D f₀) b).obj K ∧
      V = ((S.closure.coefficientStages G).integral.support (sfProjectionWeilMap D f₀) b).obj H ∧
      B = (((S.closure.coefficientStages G).integralTensor
        (sfProjectionWeilSpace D Y₀)).obj U).obj L ∧
      Nonempty ((S.closure.commonStage.pull (sfProjectionWeilMap D f₀)).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber Y₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber Y₀).left).obj L)) ≅
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber X₀).left).obj P))) ∧
      Nonempty (((S.closure.commonStageTensor (sfProjectionWeilSpace D X₀)).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber X₀).left).obj K))).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber X₀).left).obj P)) ≅
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber X₀).left).obj H))) ∧
      Nonempty ((S.closure.commonStage.support (sfProjectionWeilMap D f₀) b).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber X₀).left).obj K)) ≅
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber Y₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber Y₀).left).obj U))) ∧
      Nonempty ((S.closure.commonStage.support (sfProjectionWeilMap D f₀) b).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber X₀).left).obj H)) ≅
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber Y₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber Y₀).left).obj V))) ∧
      Nonempty (((S.closure.commonStageTensor (sfProjectionWeilSpace D Y₀)).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber Y₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber Y₀).left).obj U))).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber Y₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber Y₀).left).obj L)) ≅
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber Y₀).left) G).obj
          ((sfRationalConstructibleLocalization c.l
            (Coefficient.{u} c.l c.Qbar G) (D.geometricFiber Y₀).left).obj B))) := by
  let T : SixFunctorOperationDatum D c (Coefficient.{u} c.l c.Qbar G) 1 (by decide) :=
    { toSixFunctorFiniteOperations := (S.coefficientIntegralNormalization G).finiteLevels 0
      higher := S.closure.coefficientStages G
      integralNormalization := S.coefficientIntegralNormalization G
      closure := S.closure
      coefficientIntegralNormalization := S.coefficientIntegralNormalization
      commonStageCoherence := S.commonStageCoherence }
  obtain ⟨P, H, U, V, B, hP, hH, hU, hV, hB, eP, eH, eU, eV, eB,
    rP, rH, rU, rV, rB⟩ := sfProjectionWeilTensorDomainBridge D c _ 1 (by decide)
      T X₀ Y₀ f₀ b K L _hL
  let X := sfProjectionWeilSpace D X₀
  let Y := sfProjectionWeilSpace D Y₀
  let f := sfProjectionWeilMap D f₀
  let : ∀ x : X.obj.left, Invertible (c.l : X.obj.left.residueField x) := fun x ↦
    (D.geometricFiber_coefficientPrimeInvertible c.l c.different X₀ x).invertible
  let : ∀ y : Y.obj.left, Invertible (c.l : Y.obj.left.residueField y) := fun y ↦
    (D.geometricFiber_coefficientPrimeInvertible c.l c.different Y₀ y).invertible
  let I (W : SixFunctorSpace D) :=
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := c.l) (Ω := c.Qbar) (Y := W.obj.left) G
  let Q (W : SixFunctorSpace D) :=
    sfRationalConstructibleLocalization c.l (Coefficient.{u} c.l c.Qbar G) W.obj.left
  let C := S.closure.commonStageComparison G
  refine ⟨P, H, U, V, B, hP, hH, hU, hV, hB, eP, eH, eU, eV, eB,
    ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact ((C.directAdjunction f).left.app ((Q Y).obj L)).symm ≪≫
      (I X).mapIso (eqToIso rP)
  · rw [S.closure.commonStageTensorNormalization X]
    exact tensorStageIso c.l c.Qbar X.obj.left G ((Q X).obj K) ((Q X).obj P) ≪≫
      (I X).mapIso (eqToIso ((Functor.congr_obj
        (Functor.congr_obj ((S.closure.coefficientStages G).rationalTensorNormalization X)
          ((Q X).obj K)) ((Q X).obj P)).symm.trans rH))
  · exact ((C.supportAdjunction f b).left.app ((Q X).obj K)).symm ≪≫
      (I Y).mapIso (eqToIso rU)
  · exact ((C.supportAdjunction f b).left.app ((Q X).obj H)).symm ≪≫
      (I Y).mapIso (eqToIso rV)
  · rw [S.closure.commonStageTensorNormalization Y]
    exact tensorStageIso c.l c.Qbar Y.obj.left G ((Q Y).obj U) ((Q Y).obj L) ≪≫
      (I Y).mapIso (eqToIso ((Functor.congr_obj
        (Functor.congr_obj ((S.closure.coefficientStages G).rationalTensorNormalization Y)
          ((Q Y).obj U)) ((Q Y).obj L)).symm.trans rB))

end WeilConjectures
