/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitProduct
public import WeilConjectures.TraceFormula.Specialization.TraitSlice

/-!

# Base change of models to a trait `Spec K⟦t⟧`

Let `M` be a model of finite type over the trait `S = Spec k'⟦t⟧` along `q : 𝒳 ⟶ S`, and let
`K` be a field extension of `k'`. Given a factorisation `q = b ≫ p` through a scheme `Y` and a
morphism `v : Spec K⟦t⟧ ⟶ Y` lying over the trait map `Spec K⟦t⟧ ⟶ S`, the *base change*
`M.baseChange` (`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.baseChange`) is the
model over the trait `Spec K⟦t⟧` with total space `𝒳'' = 𝒳 ×_Y Spec K⟦t⟧`, geometric generic fibre
`𝒳'' ×_{K⟦t⟧} Spec Ω_K` (`Ω_K = (Frac K⟦t⟧)^alg`) and special fibre `𝒳'' ×_{K⟦t⟧} Spec K`, with
the identification `ε` through `𝒳_η̄`, using an embedding `Ω ⟶ Ω_K` of the fields of the
geometric generic points (`AlgebraicGeometry.traitGenericFieldMap`). Two cases occur in the
generic-slicing step of Gabber's Künneth formula (blueprint `sk-prop-tf-nearby-external-kunneth`,
"Finite support"):

* `Y = 𝔸¹_S` and `v` the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` along a coordinate `b`, the
  *geometric slice*, of smaller dimension;
* `Y = S`, `b = q`, `p = 𝟙` and `v` the trait map, the *change of trait*.

The base change is a model of finite type over `Spec K⟦t⟧`
(`NearbyCyclesModel.IsTraitModelOver.baseChange`), it maps to `M`
(`NearbyCyclesModel.baseChangeHom`), and morphisms of models induce morphisms of base changes
(`NearbyCyclesModel.Hom.baseChange`). For a product `P = M ×_S N` over the trait, the slice of
`P` along a coordinate of `M` is the product over `Spec K⟦t⟧` of the slice of `M` and of the change
of trait of `N` (`NearbyCyclesModel.isPullback_baseChange_product`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section GenericField

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧ ⟶ Ω_K` is injective. -/
lemma injective_algebraMap_comp_map :
    Function.Injective ((algebraMap (PowerSeries K) (traitGenericField K)).comp
      (PowerSeries.map (algebraMap k' K))) := by
  rw [RingHom.coe_comp]
  refine Function.Injective.comp ?_ (PowerSeries.map_injective _ (algebraMap k' K).injective)
  rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K))
    (traitGenericField K), RingHom.coe_comp]
  exact (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)).injective.comp
    (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))

/-- The embedding `Frac k'⟦t⟧ ⟶ Ω_K` induced by the coefficientwise map. -/
noncomputable def traitFractionFieldMap :
    FractionRing (PowerSeries k') →+* traitGenericField K :=
  IsFractionRing.lift (injective_algebraMap_comp_map k' K)

/-- An embedding `Ω = (Frac k'⟦t⟧)^alg ⟶ Ω_K = (Frac K⟦t⟧)^alg` of the fields of the geometric
generic points of the traits, over the coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧`. -/
noncomputable def traitGenericFieldMap : traitGenericField k' →+* traitGenericField K :=
  letI := (traitFractionFieldMap k' K).toAlgebra
  (IsAlgClosed.lift (R := FractionRing (PowerSeries k')) (S := traitGenericField k')
    (M := traitGenericField K)).toRingHom

/-- The embedding of the fields of the geometric generic points lies over the coefficientwise
map `k'⟦t⟧ ⟶ K⟦t⟧`. -/
lemma traitGenericFieldMap_comp_algebraMap :
    (traitGenericFieldMap k' K).comp (algebraMap (PowerSeries k') (traitGenericField k')) =
      (algebraMap (PowerSeries K) (traitGenericField K)).comp
        (PowerSeries.map (algebraMap k' K)) := by
  let := (traitFractionFieldMap k' K).toAlgebra
  ext a : 1
  rw [IsScalarTower.algebraMap_eq (PowerSeries k') (FractionRing (PowerSeries k'))
    (traitGenericField k')]
  simp only [traitGenericFieldMap, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes]
  change traitFractionFieldMap k' K _ = _
  rw [traitFractionFieldMap, IsFractionRing.lift_algebraMap]
  rfl

/-- The map `Spec Ω_K ⟶ Spec Ω` of the geometric generic points of the traits. -/
noncomputable def traitGenericPointMap :
    Spec (.of (traitGenericField K)) ⟶ Spec (.of (traitGenericField k')) :=
  Spec.map (CommRingCat.ofHom (traitGenericFieldMap k' K))

/-- The geometric generic points of the traits are compatible with the trait map. -/
@[reassoc]
lemma traitGenericPoint_traitMap :
    traitGenericPoint K ≫ traitMap k' K = traitGenericPointMap k' K ≫ traitGenericPoint k' := by
  rw [traitGenericPoint, traitMap, traitGenericPointMap, traitGenericPoint, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    traitGenericFieldMap_comp_algebraMap]

end GenericField

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section BaseChange

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)

/-- The special fibre `𝒳'' ×_{K⟦t⟧} Spec K` of the base change `𝒳'' = 𝒳 ×_Y Spec K⟦t⟧`, as a
scheme over `Spec K`. -/
noncomputable def baseChangeSpecial : Over (Spec (.of K)) :=
  Over.mk (pullback.snd (pullback.snd b v) (traitClosedPoint K))

include hb hv in
/-- The two maps from the total space of the base change to the trait `S` agree. -/
@[reassoc]
lemma pullback_fst_comp_eq_snd_comp_traitMap :
    pullback.fst b v ≫ q = pullback.snd b v ≫ traitMap k' K := by
  rw [← hb, pullback.condition_assoc, hv]

/-- The map `𝒳'' ×_{K⟦t⟧} Spec Ω_K ⟶ 𝒳_η̄` of geometric generic fibres of the base change. -/
noncomputable def baseChangeGenericMap :
    pullback (pullback.snd b v) (traitGenericPoint K) ⟶ M.generic :=
  hM.isPullback_j.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ traitGenericPointMap k' K) (by
      rw [Category.assoc, pullback_fst_comp_eq_snd_comp_traitMap b hb v hv,
        pullback.condition_assoc, traitGenericPoint_traitMap, Category.assoc])

@[reassoc (attr := simp)]
lemma baseChangeGenericMap_j :
    baseChangeGenericMap hM b hb v hv ≫ M.j = pullback.fst _ _ ≫ pullback.fst _ _ :=
  hM.isPullback_j.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeGenericMap_g :
    baseChangeGenericMap hM b hb v hv ≫ g = pullback.snd _ _ ≫ traitGenericPointMap k' K :=
  hM.isPullback_j.lift_snd _ _ _

/-- The *base change* of a model `M` over the trait `S = Spec k'⟦t⟧` along `v : Spec K⟦t⟧ ⟶ Y`,
for a factorisation `q = b ≫ p` of its structure morphism: total space `𝒳 ×_Y Spec K⟦t⟧`,
geometric generic fibre over `Spec Ω_K`, special fibre over `Spec K`, and the identification `ε`
through `𝒳_η̄`. -/
@[simps]
noncomputable def baseChange : NearbyCyclesModel X (baseChangeSpecial b v).left where
  total := pullback b v
  generic := pullback (pullback.snd b v) (traitGenericPoint K)
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := baseChangeGenericMap hM b hb v hv ≫ M.ε

end BaseChange

section HomBaseChange

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X Z : Scheme.{u}} {X' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {P : NearbyCyclesModel Z Z'.left} {f : Z ⟶ X} {f' : Z'.left ⟶ X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qP : P.total ⟶ trait k'} {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hP : P.IsTraitModelOver qP gP)
  {YM YP : Scheme.{u}} {bM : M.total ⟶ YM} {pM : YM ⟶ trait k'} (hbM : bM ≫ pM = qM)
  {vM : trait K ⟶ YM} (hvM : vM ≫ pM = traitMap k' K)
  {bP : P.total ⟶ YP} {pP : YP ⟶ trait k'} (hbP : bP ≫ pP = qP)
  {vP : trait K ⟶ YP} (hvP : vP ≫ pP = traitMap k' K)
  (φ : P.Hom M f f') (κ : YP ⟶ YM) (hκb : bP ≫ κ = φ.total ≫ bM) (hκv : vP ≫ κ = vM)

end HomBaseChange

section Product

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {MT NT PT Y : Scheme.{u}} {φ₁ : PT ⟶ MT} {φ₂ : PT ⟶ NT} {qM : MT ⟶ trait k'}
  {qN : NT ⟶ trait k'}

end Product

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
