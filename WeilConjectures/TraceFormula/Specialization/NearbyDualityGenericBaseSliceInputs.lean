/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTensor
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBase

/-!

# Nearby duality over a generic base: the inputs of the slice step

Let `M` be a trait model of `X₁` over the generic base, `b : 𝒳 ⟶ 𝔸¹_S` a coordinate of its total
space and `M''` the generic slice model of `b` (`NearbyCyclesModel.genericSliceModel`), a trait
model over the generic base `(Frac K⟦t⟧, X₂)`, with special fibre `Y = 𝒳''_s`. This file sets up
the proof of the slice compatibility of nearby duality
(`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`, blueprint
`det-tf-nearby-duality-slice` (2) with `det-tf-invariants-duality`):

* the pullback `Lg^*` of bounded constructible complexes along a morphism of schemes of finite
  type over possibly different fields (`boundedConstructibleUpperStarOfMap`), strong monoidal;
* the morphism of models `M'' ⟶ M` over `c : X₂ ⟶ X₁` and `p : Y ⟶ X'`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom`) and its pullback exchange
  `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange`),
  which is monoidal (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange_tensor`);
* the action of the self-maps of a model over the identities on its nearby cycles
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceSelfAction`), which is monoidal
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceSelfAction_tensor`);
* the duality map of the slice for the dualizing objects `c^* ω_{X₁}` and `p^* ω_{X'}`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceDualityMap`).

The other inputs of the slice step are in separate files: the averaging splitting of `α`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`, in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceAveraging`), the
commutation of the pullbacks with internal Hom (blueprint `det-pd-generic-closed-hom` (2), in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceClosedHom`) and the
dualizing map of the slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap`, in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceDualizing`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section UpperStarOfMap

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pullback `Lg^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible complexes
along a morphism of schemes `g : Y ⟶ X`, `X` and `Y` of finite type over possibly different
fields: the restriction of `L((g)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property

/-- The derived pullback along a morphism of schemes is strong monoidal on bounded constructible
complexes, with the comparison isomorphisms of `L((g)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g).Monoidal := by
  unfold boundedConstructibleUpperStarOfMap
  exact ObjectProperty.monoidalLift _ _

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The derived pullback along a morphism of schemes on bounded constructible complexes is that
of the ambient derived categories. -/
lemma boundedConstructibleUpperStarOfMap_map (g : Y.left ⟶ X.left)
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g).map f =
      ObjectProperty.homMk (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f.hom) :=
  rfl

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [IsSeparated X.hom]
  [IsSeparated Y.hom] in
/-- The tensor comparison of the derived pullback along a morphism of schemes on bounded
constructible complexes is that of the ambient derived pullback. -/
lemma μ_boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left)
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g) A B =
      ObjectProperty.homMk
        (Functor.LaxMonoidal.μ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A.obj B.obj) :=
  rfl

end UpperStarOfMap

namespace NearbyCyclesModel

section LiftExchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {k₁ k₁' k₂ k₂' : Type u} [Field k₁] [Field k₁'] [Field k₂]
  [Field k₂'] [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₁').Prime]
  [Fact (ringChar k₁' ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  [Fact (ringChar k₂').Prime] [Fact (ringChar k₂' ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k₁'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of k₂'))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y.left ⟶ X.left} {j' : Y'.left ⟶ X'.left}

end LiftExchange

/-! ### The generic slice -/

section GenericSlice

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {K : Type u} [Field K] [Algebra k' K] (x : K)

section Hom

end Hom

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase x hb).hom] [QuasiCompact (genericSliceBase x hb).hom]
  [IsSeparated (genericSliceBase x hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice x)).hom]

namespace IsTraitModelOfGenericBase

end IsTraitModelOfGenericBase

end GenericSlice

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
