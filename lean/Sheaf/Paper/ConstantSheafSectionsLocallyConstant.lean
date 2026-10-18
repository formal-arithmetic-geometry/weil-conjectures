/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H1 and K2
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Sections of a constant étale sheaf

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5).
The proof uses Mathlib's fpqc sheaf of continuous maps and local bijectivity,
following the source library's continuous-map comparison in
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`, in universe `u`.
(blueprint: lem-weil-pbc-constant-sheaf-sections-locally-constant)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private def locallyConstantPresheaf (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop.left E)
  map f := AddCommGrpCat.ofHom
    (LocallyConstant.comapAddMonoidHom ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id _ := by ext s x; rfl
  map_comp _ _ := by ext s x; rfl

private theorem locallyConstantPresheaf_isSheaf
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    Presheaf.IsSheaf T.smallEtaleTopology (locallyConstantPresheaf T E) := by
  let : TopologicalSpace E := ⊥
  let : DiscreteTopology E := ⟨rfl⟩
  let Q := (Scheme.Etale.forget T ⋙ Over.forget T).op ⋙ continuousMapPresheafAb E
  let e : locallyConstantPresheaf T E ≅ Q :=
    NatIso.ofComponents (fun U ↦ AddEquiv.toAddCommGrpIso
      { toFun := LocallyConstant.toContinuousMap
        invFun := fun t ↦
          let t₀ : C(U.unop.left, E) := t
          ⟨t₀, (IsLocallyConstant.iff_continuous _).2 t₀.continuous⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }) (by intros; rfl)
  rw [Presheaf.isSheaf_of_iso_iff e]
  exact (Scheme.Etale.forget T ⋙ Over.forget T).op_comp_isSheaf_of_isSheaf
    T.smallEtaleTopology Scheme.etaleTopology (continuousMapPresheafAb E)
    (.of_le (Scheme.etaleTopology_le_proetaleTopology.trans
      Scheme.proetaleTopology_le_fpqcTopology)
      (isSheaf_fpqcTopology_continuousMapPresheafAb E))

private def constToLocallyConstant (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    (Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of E) ⟶ locallyConstantPresheaf T E where
  app U := AddCommGrpCat.ofHom
    { toFun := LocallyConstant.const U.unop.left
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

private theorem constToLocallyConstant_surjective
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    Presheaf.IsLocallySurjective T.smallEtaleTopology (constToLocallyConstant T E) where
  imageSieve_mem {U} s₀ := by
    let s : LocallyConstant U.left E := s₀
    let F (e : E) : U.left.Opens := ⟨{x | s x = e}, s.isLocallyConstant.isOpen_fiber e⟩
    let V (e : E) : T.Etale := Scheme.Etale.mk ((F e).ι ≫ U.hom)
    let ι (e : E) : V e ⟶ U := MorphismProperty.Over.homMk (F e).ι rfl
    refine T.smallEtaleTopology.superset_covering ?_
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨e⟩
      refine ⟨e, LocallyConstant.ext fun x ↦ ?_⟩
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

private theorem constToLocallyConstant_injective
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    Presheaf.IsLocallyInjective T.smallEtaleTopology (constToLocallyConstant T E) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact T.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (T.smallEtaleTopology.top_mem _)
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hab (congrArg
        (fun f : LocallyConstant U.unop.left E ↦ f x) h)⟩
      refine T.smallEtaleTopology.superset_covering ?_
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

private noncomputable def constantToLocallyConstantSheaf
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of E) ⟶
      ⟨locallyConstantPresheaf T E, locallyConstantPresheaf_isSheaf T E⟩ :=
  ⟨sheafifyLift T.smallEtaleTopology (constToLocallyConstant T E)
    (locallyConstantPresheaf_isSheaf T E)⟩

private theorem constantToLocallyConstantSheaf_isIso
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    IsIso (constantToLocallyConstantSheaf T E) := by
  have := constToLocallyConstant_injective T E
  have := constToLocallyConstant_surjective T E
  refine (Sheaf.isLocallyBijective_iff_isIso (constantToLocallyConstantSheaf T E)).1
    ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify T.smallEtaleTopology _)]
    change Presheaf.IsLocallyInjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify T.smallEtaleTopology _)]
    change Presheaf.IsLocallySurjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance

/-- Sections of a constant étale sheaf are Zariski-locally constant maps, and the
comparison sends the canonical section induced by `e` to the constant map with value `e`.
Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5).
(blueprint: lem-weil-pbc-constant-sheaf-sections-locally-constant)

Proof:
1. Give `E` the discrete topology. The presheaf of locally constant `E`-valued
   functions is naturally isomorphic, as an abelian-group presheaf, to continuous
   maps into `E`. Mathlib proves the latter is an fpqc sheaf. Restrict along the
   continuous forgetful functor from the small étale site to get a sheaf here.
2. The constant-function map from the constant presheaf is locally surjective:
   the open fibres of every locally constant function cover its domain, and its
   restriction to the fibre of `e` is the constant function `e`.
3. The same map is locally injective. If two coefficients give equal constant
   functions on a nonempty scheme, evaluation gives equality of the coefficients.
   Otherwise the domain is empty and the empty family is an étale covering.
4. Factor the constant-function map through sheafification. Its local bijectivity,
   together with that of the sheafification unit, makes the resulting morphism
   of sheaves locally bijective, hence an isomorphism. Evaluate it at the identity
   object over `T` and convert the resulting abelian-group isomorphism to an
   additive equivalence. The sheafification factorization identity gives the
   displayed compatibility with constant maps. -/
theorem constantSheaf_sections_locallyConstant
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    ∃ φ : AddEquiv
      (↑(((constantSheaf T.smallEtaleTopology (AddCommGrpCat.{u})).obj
        (AddCommGrpCat.of E)).obj.obj
          (Opposite.op (Scheme.Etale.mk (𝟙 T)))))
      (LocallyConstant T E),
      ∀ e : E,
        φ (((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of E))).app
            (Opposite.op (Scheme.Etale.mk (𝟙 T)))) e) = LocallyConstant.const T e := by
  have := constantToLocallyConstantSheaf_isIso T E
  let i := (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}).mapIso
    (asIso (constantToLocallyConstantSheaf T E))
  let j := i.app (Opposite.op (Scheme.Etale.mk (𝟙 T)))
  refine ⟨j.addCommGroupIsoToAddEquiv, ?_⟩
  intro e
  have h := congrArg (fun f ↦ f.app (Opposite.op (Scheme.Etale.mk (𝟙 T))) e)
    (toSheafify_sheafifyLift T.smallEtaleTopology (constToLocallyConstant T E)
      (locallyConstantPresheaf_isSheaf T E))
  exact h

end AlgebraicGeometry
