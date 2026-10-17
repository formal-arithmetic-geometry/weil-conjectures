/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

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
        .of_le proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheafAb A)⟩⟩

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

section Module

variable (Λ : Type (u + 1)) [CommRing Λ] (M : Type (u + 1)) [AddCommGroup M] [Module Λ M]
  [TopologicalSpace M] [DiscreteTopology M]

/-- Scalar multiplication on a discrete module is continuous. -/
lemma continuousConstSMul_of_discreteTopology : ContinuousConstSMul Λ M :=
  ⟨fun _ ↦ continuous_of_discreteTopology⟩

attribute [local instance] continuousConstSMul_of_discreteTopology

/-- The presheaf of `Λ`-modules `U ↦ C(U, M)` of continuous (that is, locally constant)
functions to a discrete `Λ`-module `M`, on the category of schemes. -/
noncomputable def continuousMapPresheafModule : Scheme.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ C(U.unop, M)
  map {U V} f := ModuleCat.ofHom
    { toFun g := g.comp f.unop.base.hom
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

lemma isSheaf_fpqcTopology_continuousMapPresheafModule :
    Presheaf.IsSheaf fpqcTopology (continuousMapPresheafModule Λ M) :=
  have : ReflectsLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    reflectsLimitsOfSize_shrink.{u, u + 1, u + 1, u + 1} _
  Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
    (isSheaf_fpqcTopology_continuousMapPresheaf M)

/-- The sheaf of `Λ`-modules `U ↦ C(U, M)` on the small pro-étale site of `X`. -/
noncomputable def ProEt.continuousMapSheafModule :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  ⟨(ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheafModule Λ M,
    (ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf (ProEt.topology X) proetaleTopology
      ⟨continuousMapPresheafModule Λ M,
        .of_le proetaleTopology_le_fpqcTopology
          (isSheaf_fpqcTopology_continuousMapPresheafModule Λ M)⟩⟩

lemma ProEt.continuousMapSheafModule_obj_obj (U : X.ProEt) :
    (ProEt.continuousMapSheafModule X Λ M).obj.obj (op U) = ModuleCat.of Λ C(U.left, M) :=
  rfl

lemma ProEt.continuousMapSheafModule_obj_map_apply {U V : X.ProEt} (f : U ⟶ V)
    (s : C(V.left, M)) :
    (ProEt.continuousMapSheafModule X Λ M).obj.map f.op s = s.comp f.left.base.hom :=
  rfl

/-- The constant functions, as a map from the constant presheaf with value `M` to the sheaf of
continuous functions `U ↦ C(U, M)`. -/
noncomputable def ProEt.constToContinuousMapModule :
    (Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of Λ M) ⟶
      (ProEt.continuousMapSheafModule X Λ M).obj where
  app _ := ModuleCat.ofHom
    { toFun a := ContinuousMap.const _ a
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  naturality _ _ _ := rfl

lemma ProEt.constToContinuousMapModule_app_apply (U : X.ProEtᵒᵖ) (a : M) :
    (ProEt.constToContinuousMapModule X Λ M).app U a = ContinuousMap.const _ a :=
  rfl

instance : Presheaf.IsLocallySurjective (ProEt.topology X)
    (ProEt.constToContinuousMapModule X Λ M) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, M) := s₀
    let j (x : U.left) := (U.left.fiberOpens s (s x)).ι
    refine ProEt.mem_topology_of_openImmersion _ j
      (fun x ↦ ⟨x, ⟨⟨x, (U.left.mem_fiberOpens s (s x) x).2 rfl⟩, Scheme.Opens.ι_apply _ _⟩⟩)
      (fun x ↦ ⟨s x, ContinuousMap.ext fun y ↦ ?_⟩)
    exact ((U.left.mem_fiberOpens s (s x) _).1 y.2).symm

instance : Presheaf.IsLocallyInjective (ProEt.topology X)
    (ProEt.constToContinuousMapModule X Λ M) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact (ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl) ((ProEt.topology X).top_mem _)
    · have : IsEmpty U.unop.left :=
        ⟨fun x ↦ hab (congr_arg (fun f : C(U.unop.left, M) ↦ f x) h)⟩
      exact ProEt.mem_topology_of_openImmersion (ι := PEmpty.{u + 1}) _
        (Y := fun i ↦ i.elim) (fun i ↦ i.elim) (fun x ↦ isEmptyElim x) (fun i ↦ i.elim)

/-- The map from the constant sheaf of `Λ`-modules with value `M` to the sheaf of continuous
functions `U ↦ C(U, M)`. -/
noncomputable def ProEt.constantSheafToContinuousMapSheafModule :
    (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M) ⟶
      ProEt.continuousMapSheafModule X Λ M :=
  ((sheafificationAdjunction (ProEt.topology X) (ModuleCat.{u + 1} Λ)).homEquiv _ _).symm
    (ProEt.constToContinuousMapModule X Λ M)

lemma ProEt.toSheafify_constantSheafToContinuousMapSheafModule :
    toSheafify (ProEt.topology X) _ ≫ (ProEt.constantSheafToContinuousMapSheafModule X Λ M).hom =
      ProEt.constToContinuousMapModule X Λ M := by
  have h := ((sheafificationAdjunction (ProEt.topology X) (ModuleCat.{u + 1} Λ)).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of Λ M))
      (ProEt.continuousMapSheafModule X Λ M)).apply_symm_apply
        (ProEt.constToContinuousMapModule X Λ M)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

instance : IsIso (ProEt.constantSheafToContinuousMapSheafModule X Λ M) := by
  have h := ProEt.toSheafify_constantSheafToContinuousMapSheafModule X Λ M
  refine (Sheaf.isLocallyBijective_iff_isIso
    (ProEt.constantSheafToContinuousMapSheafModule X Λ M)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology X) _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology X) _), h]
    infer_instance

/-- **The constant pro-étale sheaf of `Λ`-modules is the sheaf of locally constant functions.**
For a discrete `Λ`-module `M`, the constant sheaf with value `M` on the small pro-étale site of
`X` is isomorphic to `U ↦ C(U, M)`, the constant section `a` corresponding to the constant
function `a`. -/
noncomputable def ProEt.constantSheafIsoContinuousMapSheafModule :
    (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M) ≅
      ProEt.continuousMapSheafModule X Λ M :=
  asIso (ProEt.constantSheafToContinuousMapSheafModule X Λ M)

end Module

end AlgebraicGeometry.Scheme
