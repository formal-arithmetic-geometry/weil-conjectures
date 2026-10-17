/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# The constant sheaf on the small pro-étale site as a sheaf of continuous maps

For a topological abelian group `A`, the presheaf `U ↦ C(U, A)` on the small pro-étale site of a
scheme `X` is a sheaf, being the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheafAb`. When `A` is discrete, it is the constant sheaf with
value `A`: a section of the constant pro-étale sheaf over `U` is a locally constant function on
the underlying space of `U`.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.continuousMapSheaf`: the sheaf `U ↦ C(U, A)` on the small
  pro-étale site.
- `AlgebraicGeometry.Scheme.ProEt.constantSheafIsoContinuousMapSheaf`: for discrete `A`, the
  isomorphism between the constant sheaf with value `A` and `U ↦ C(U, A)`, which sends the
  constant section `a` to the constant function `a`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type (u + 1)) [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A]

/-- The sheaf `U ↦ C(U, A)` of continuous functions with values in a topological abelian group
`A`, on the small pro-étale site of `X`. It is the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheafAb`. -/
noncomputable def ProEt.continuousMapSheaf : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  ⟨(ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheafAb.{u + 1, u} A,
    (ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf (ProEt.topology X) proetaleTopology
      ⟨continuousMapPresheafAb.{u + 1, u} A,
        Presheaf.isSheaf_of_le _ proetaleTopology_le_fpqcTopology
          (isSheaf_fpqcTopology_continuousMapPresheafAb A)⟩⟩

lemma ProEt.continuousMapSheaf_obj_obj (U : X.ProEt) :
    (ProEt.continuousMapSheaf X A).obj.obj (op U) = AddCommGrpCat.of C(U.left, A) :=
  rfl

lemma ProEt.continuousMapSheaf_obj_map_apply {U V : X.ProEt} (f : U ⟶ V)
    (s : C(V.left, A)) :
    (ProEt.continuousMapSheaf X A).obj.map f.op s = s.comp f.left.base.hom :=
  rfl

section Discrete

variable [DiscreteTopology A]

/-- The constant functions, as a map from the constant presheaf with value `A` to the sheaf of
continuous functions `U ↦ C(U, A)`. -/
noncomputable def ProEt.constToContinuousMap :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A) ⟶ (ProEt.continuousMapSheaf X A).obj where
  app _ := AddCommGrpCat.ofHom
    { toFun a := ContinuousMap.const _ a
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

omit [DiscreteTopology A] in
lemma ProEt.constToContinuousMap_app_apply (U : X.ProEtᵒᵖ) (a : A) :
    (ProEt.constToContinuousMap X A).app U a = ContinuousMap.const _ a :=
  rfl

/-- A continuous function to a discrete group is locally constant: it is constant on the open
fibres, which cover. -/
instance : Presheaf.IsLocallySurjective (ProEt.topology X) (ProEt.constToContinuousMap X A) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, A) := s₀
    let j (x : U.left) := (U.left.fiberOpens s (s x)).ι
    refine ProEt.mem_topology_of_openImmersion _ j
      (fun x ↦ ⟨x, ⟨⟨x, (U.left.mem_fiberOpens s (s x) x).2 rfl⟩, Scheme.Opens.ι_apply _ _⟩⟩)
      (fun x ↦ ⟨s x, ContinuousMap.ext fun y ↦ ?_⟩)
    exact ((U.left.mem_fiberOpens s (s x) _).1 y.2).symm

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty family. -/
instance : Presheaf.IsLocallyInjective (ProEt.topology X) (ProEt.constToContinuousMap X A) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact (ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl) ((ProEt.topology X).top_mem _)
    · have : IsEmpty U.unop.left :=
        ⟨fun x ↦ hab (congr_arg (fun f : C(U.unop.left, A) ↦ f x) h)⟩
      exact ProEt.mem_topology_of_openImmersion (ι := PEmpty.{u + 1}) _
        (Y := fun i ↦ i.elim) (fun i ↦ i.elim) (fun x ↦ isEmptyElim x) (fun i ↦ i.elim)

/-- The map from the constant sheaf with value `A` to the sheaf of continuous functions
`U ↦ C(U, A)` sending the constant section `a` to the constant function `a`. -/
noncomputable def ProEt.constantSheafToContinuousMapSheaf :
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of A) ⟶
      ProEt.continuousMapSheaf X A :=
  ((sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (ProEt.constToContinuousMap X A)

omit [DiscreteTopology A] in
lemma ProEt.toSheafify_constantSheafToContinuousMapSheaf :
    toSheafify (ProEt.topology X) _ ≫ (ProEt.constantSheafToContinuousMapSheaf X A).hom =
      ProEt.constToContinuousMap X A := by
  have h := ((sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))
      (ProEt.continuousMapSheaf X A)).apply_symm_apply (ProEt.constToContinuousMap X A)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

instance : IsIso (ProEt.constantSheafToContinuousMapSheaf X A) := by
  have : PreservesLimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  have : (ProEt.topology X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  have h := ProEt.toSheafify_constantSheafToContinuousMapSheaf X A
  refine (Sheaf.isLocallyBijective_iff_isIso (ProEt.constantSheafToContinuousMapSheaf X A)).1
    ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology X) _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology X) _), h]
    infer_instance

/-- **The constant pro-étale sheaf is the sheaf of continuous functions.** For a discrete
abelian group `A`, the constant sheaf with value `A` on the small pro-étale site of `X` is
isomorphic to the sheaf `U ↦ C(U, A)` of locally constant functions, by the map sending the
constant section `a` to the constant function `a`. -/
noncomputable def ProEt.constantSheafIsoContinuousMapSheaf :
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of A) ≅
      ProEt.continuousMapSheaf X A :=
  asIso (ProEt.constantSheafToContinuousMapSheaf X A)

end Discrete

end AlgebraicGeometry.Scheme
