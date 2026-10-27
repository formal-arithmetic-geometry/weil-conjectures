/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
import Sheaf.TraceFormula.FibreComponentRelativeAssociated
import Sheaf.TraceFormula.FlatAssociatedEquidimensional
import Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Dimension of fibres in a fibre-component closure inside a flat family

Source: literature/stacks-project/more-morphisms.tex, Tag 0GSJ
(lemma-flat-associated-equidimensional), part (2), specialized to a fibre-component
generic point; Tag 0GSI (lemma-associated-point-specializes)
(blueprint: lem-trf-flat-fibre-component-closure-dimension).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

open TopologicalSpace TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def unitStalkAddEquiv (X : Scheme.{u}) (x : X) :
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf)) ≃+ X.presheaf.stalk x :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm.addCommGroupIsoToAddEquiv

private theorem unitStalkAddEquiv_germ (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    unitStalkAddEquiv X x
      (germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf U x hx r) =
      X.presheaf.germ U x hx r := by
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) (Opposite.op (⟨U, hx⟩ : OpenNhds x))) r

private def unitStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf)) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  { unitStalkAddEquiv X x with
    map_smul' := by
      intro r m
      obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
      obtain ⟨V, hxV, m, rfl⟩ := exists_germ_eq
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
      rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U)
          x ⟨hxU, hxV⟩ r,
        ← germ_res_apply (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          (homOfLE inf_le_right : U ⊓ V ⟶ V) x ⟨hxU, hxV⟩ m,
        ← PresheafOfModules.germ_smul (R := X.presheaf)
          (SheafOfModules.unit X.ringCatSheaf).val]
      change unitStalkAddEquiv X x
          (germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf _ x _ _) =
        _ * unitStalkAddEquiv X x (germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf _ x _ _)
      rw [unitStalkAddEquiv_germ, unitStalkAddEquiv_germ]
      exact map_mul _ _ _ }

private theorem unit_flat {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (x : X) :
    Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          (SheafOfModules.unit X.ringCatSheaf))) := by
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  apply Module.Flat.of_linearEquiv (M := X.presheaf.stalk x)
  exact { unitStalkAddEquiv X x with
    map_smul' := fun r m ↦ (unitStalkLinearEquiv X x).map_smul
      ((f.stalkMap x).hom r) m }

private theorem unit_relative_associated {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFiniteType f] (t : S) (B : Set (f.fiber t))
    (hB : B ∈ irreducibleComponents (f.fiber t)) (y : f.fiber t)
    (hy : IsGenericPoint y B) :
    f.fiberι t y ∈ Scheme.Modules.relativeAssassin f
      (SheafOfModules.unit X.ringCatSheaf) := by
  have ha := (fibre_component_relative_associated f t B y hB hy).1
  have ht : f (f.fiberι t y) = t := by
    have h := Set.range_subset_iff.mp (f.range_fiberι t).le y
    exact h
  change f.asFiber (f.fiberι t y) ∈ Scheme.Modules.associatedPoints _
  generalize hz : f.fiberι t y = z at *
  have hzy : f.fiberι t y = z := hz
  subst t
  have he : f.asFiber z = y := by
    apply (f.fiberι (f z)).isEmbedding.injective
    simpa using hzy.symm
  rw [he]
  have : IsLocallyNoetherian (f.fiber (f z)) := by
    dsimp [Scheme.Hom.fiber]
    infer_instance
  have hu := (isAssociatedPrime_iff.mp ha)
  let := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso (f.fiberι (f z))).1
  let e := ((RingedSpace.moduleStalkFunctor (f.fiber (f z)).toRingedSpace y).mapIso
    (asIso (Scheme.Modules.tensorPullbackObjUnitToUnit (f.fiberι (f z))))).toLinearEquiv
  let e' := e.trans (unitStalkLinearEquiv (f.fiber (f z)) y)
  change _ ∈ RingTheory.annihilatorAssociatedPrimes _ _
  refine ⟨hu.1, ?_⟩
  obtain ⟨r, hr⟩ := hu.2
  refine ⟨e'.symm r, hr.trans ?_⟩
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  exact ⟨fun h ↦ e'.injective (by simpa using h),
    fun h ↦ by simpa using congrArg e' h⟩

private theorem closure_fibre_range {X S : Scheme.{u}} (f : X ⟶ S) (y : X) (s : S) :
    Set.range (f.associatedPointClosureFiberToAmbient y s) =
      closure ({y} : Set X) ∩ (f ⁻¹' ({s} : Set S)) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure {y}, isClosed_closure⟩ : TopologicalSpace.Closeds X)
  change Set.range (I.subschemeι ∘ (f.associatedPointClosureToBase y).fiberι s) = _
  rw [Set.range_comp, Scheme.Hom.range_fiberι]
  have hi : Set.range I.subschemeι = closure ({y} : Set X) := by simp [I]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hi ▸ Set.mem_range_self z, hz⟩
  · rintro ⟨hx, hs⟩
    obtain ⟨z, rfl⟩ := hi.symm ▸ hx
    exact ⟨z, hs, rfl⟩

private def closure_fibre_homeo {X S : Scheme.{u}} (f : X ⟶ S) (y : X) (s : S) :
    (f.associatedPointClosureToBase y).fiber s ≃ₜ
      (Set.inter (closure ({y} : Set X)) (f ⁻¹' ({s} : Set S))) :=
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure {y}, isClosed_closure⟩ : TopologicalSpace.Closeds X)
  let he := I.subschemeι.isEmbedding.comp
    ((f.associatedPointClosureToBase y).fiberι s).isEmbedding
  he.toHomeomorph.trans (Homeomorph.setCongr (closure_fibre_range f y s))

private def original_closure_fibre_homeo {X S : Scheme.{u}} (f : X ⟶ S)
    (t : S) (B : Set (f.fiber t)) (y : f.fiber t) (hy : IsGenericPoint y B) :
    (Set.inter (closure ({f.fiberι t y} : Set X)) (f ⁻¹' ({t} : Set S))) ≃ₜ B := by
  apply Homeomorph.symm
  apply ((f.fiberι t).isEmbedding.homeomorphImage B).trans
  apply Homeomorph.setCongr
  have hb : B = (f.fiberι t) ⁻¹' closure ({f.fiberι t y} : Set X) := by
    rw [← hy.def, (f.fiberι t).isEmbedding.closure_eq_preimage_closure_image]
    simp
  rw [hb, Set.image_preimage_eq_inter_range, f.range_fiberι t]
  rfl

private theorem component_dimension_homeo {A E : Type u} [TopologicalSpace A]
    [TopologicalSpace E] (e : A ≃ₜ E) (D : Set E)
    (hD : D ∈ irreducibleComponents E) :
    e ⁻¹' D ∈ irreducibleComponents A ∧
      topologicalKrullDim (e ⁻¹' D) = topologicalKrullDim D := by
  refine ⟨preimage_mem_irreducibleComponents hD e.isOpenEmbedding ?_, ?_⟩
  · simpa only [e.surjective.range_eq, Set.inter_univ] using hD.1.nonempty
  · exact IsHomeomorph.topologicalKrullDim_eq _
      (e.isEmbedding.homeomorphOfSubsetRange (by simp)).isHomeomorph

/--
Let `f : X ⟶ S` be flat and locally of finite type.  If `B` is an irreducible
component of the scheme-theoretic fibre over `t` and `y` is its generic point,
then every irreducible component `D` of the intersection of the closure of `y`
(in `X`) with the fibre over `s` has the same topological Krull dimension as `B`.
The proof has three steps.  First, the generic point of a component of the
locally Noetherian fibre is associated to its structure sheaf, hence is in the
relative assassin of `𝒪_X` (the fibre-component relative-associated lemma).
Second, apply the pointwise flat-relative-associated-specialization theorem to
`𝒪_X` at the generic point of a component of the reduced closure's fibre;
flatness of `f` supplies its flatness hypothesis. Third, identify that fibre
with the displayed intersection by the closed-subscheme and fibre embeddings.
At `t`, the embedding closure formula and `hy` identify the intersection with
`B`. Homeomorphism invariance of dimension finishes the comparison.
The empty intersection is
allowed because the component quantifier is then vacuous.
(blueprint: lem-trf-flat-fibre-component-closure-dimension).
-/
theorem flat_fibre_component_closure_dimension
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (t s : S) (B : Set (f.fiber t))
    (hB : B ∈ irreducibleComponents (f.fiber t))
    (y : f.fiber t) (hy : IsGenericPoint y B) :
    ∀ (D : Set
      (Set.inter (closure ({f.fiberι t y} : Set X)) ((f.base : X → S) ⁻¹' ({s} : Set S)))),
      D ∈ irreducibleComponents
        (Set.inter (closure ({f.fiberι t y} : Set X)) ((f.base : X → S) ⁻¹' ({s} : Set S))) →
      topologicalKrullDim D = topologicalKrullDim B := by
  intro D hD
  let e := closure_fibre_homeo f (f.fiberι t y) s
  let C := e ⁻¹' D
  obtain ⟨hC, hdim⟩ := component_dimension_homeo e D hD
  let x := genericPoints.ofComponent ⟨C, hC⟩
  have hx : IsGenericPoint x.val C := genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩
  let F := SheafOfModules.unit X.ringCatSheaf
  have : F.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have : F.IsInvertible := SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : F.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : F.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : F.IsFiniteType := inferInstance
  have ha := unit_relative_associated f t B hB y hy
  have hh := flat_relative_associated_specialization f F (f.fiberι t y) ha s C hC x.val hx
    (unit_flat f _)
  have ht : f (f.fiberι t y) = t :=
    Set.range_subset_iff.mp (f.range_fiberι t).le y
  let et := (closure_fibre_homeo f (f.fiberι t y) t).trans
    (original_closure_fibre_homeo f t B y hy)
  calc
    topologicalKrullDim D = topologicalKrullDim C := hdim.symm
    _ = topologicalKrullDim ((f.associatedPointClosureToBase (f.fiberι t y)).fiber
        (f (f.fiberι t y))) := hh.2.2
    _ = topologicalKrullDim ((f.associatedPointClosureToBase (f.fiberι t y)).fiber t) :=
      congrArg (fun z ↦ topologicalKrullDim
        ((f.associatedPointClosureToBase (f.fiberι t y)).fiber z)) ht
    _ = topologicalKrullDim B := IsHomeomorph.topologicalKrullDim_eq _ et.isHomeomorph

end AlgebraicGeometry
