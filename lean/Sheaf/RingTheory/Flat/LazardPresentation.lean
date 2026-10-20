/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Lazard presentation of a tensor-exact module

Source: Stacks Project, Algebra, Tag 058G, forward direction of Lazard's theorem.
(blueprint: lem-kun-lazard-flat-module)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Module

noncomputable section

private abbrev Coord (R : Type u) [CommRing R] (n : ℕ) :=
  ULift.{max u v} (Fin n →₀ R)

private structure FreeOver (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] where
  rank : ℕ
  hom : Coord.{u, v} R rank →ₗ[R] M

private instance freeOverCategory (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    SmallCategory (FreeOver R M) where
  Hom i j := { f : Coord.{u, v} R i.rank →ₗ[R] Coord.{u, v} R j.rank // j.hom.comp f = i.hom }
  id i := ⟨LinearMap.id, rfl⟩
  comp f g := ⟨g.val.comp f.val, by rw [← LinearMap.comp_assoc, g.property, f.property]⟩
  id_comp _ := by apply Subtype.ext; rfl
  comp_id _ := by apply Subtype.ext; rfl
  assoc _ _ _ := by apply Subtype.ext; rfl

private def freeDiagram (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    FreeOver R M ⥤ ModuleCat.{max u v} R where
  obj i := ModuleCat.of R (Coord.{u, v} R i.rank)
  map f := ModuleCat.ofHom f.val

private def freeCocone (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] : Cocone (freeDiagram R M) where
  pt := ModuleCat.of R M
  ι := { app i := ModuleCat.ofHom i.hom
         naturality _ _ f := by exact ModuleCat.hom_ext f.property }

private noncomputable def finiteCoordEquiv (R : Type u) [CommRing R]
    (N : Type (max u v)) [AddCommGroup N] [Module R N] [Free R N] [Module.Finite R N] :
    N ≃ₗ[R] Coord.{u, v} R (Fintype.card (Free.ChooseBasisIndex R N)) :=
  ((Free.chooseBasis R N).reindex (Fintype.equivFin _)).repr.trans
    (ULift.moduleEquiv.symm)

private theorem freeOver_common (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] (i j : FreeOver R M) :
    ∃ (k : FreeOver R M) (_ : i ⟶ k) (_ : j ⟶ k), True := by
  classical
  let e := finiteCoordEquiv.{u, v} R (Coord.{u, v} R i.rank × Coord.{u, v} R j.rank)
  let p := i.hom.coprod j.hom
  let k : FreeOver R M := ⟨_, p.comp e.symm.toLinearMap⟩
  refine ⟨k, ⟨e.toLinearMap.comp (LinearMap.inl R _ _), ?_⟩,
    ⟨e.toLinearMap.comp (LinearMap.inr R _ _), ?_⟩, trivial⟩
  · ext x
    simp [k, p]
  · ext x
    simp [k, p]

private instance freeOverFiltered (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Flat R M] :
    IsFiltered (FreeOver R M) where
  nonempty := ⟨⟨0, 0⟩⟩
  cocone_objs := freeOver_common R M
  cocone_maps {i j} f g := by
    have h : j.hom.comp (f.val - g.val) = 0 := by
      rw [LinearMap.comp_sub, f.property, g.property, sub_self]
    obtain ⟨n, a, y, hp, ha⟩ := Flat.exists_factorization_of_comp_eq_zero_of_free h
    let e : (Fin n →₀ R) ≃ₗ[R] Coord.{u, v} R n := ULift.moduleEquiv.symm
    let k : FreeOver R M := ⟨n, y.comp e.symm.toLinearMap⟩
    refine ⟨k, ⟨e.toLinearMap.comp a, ?_⟩, ?_⟩
    · ext x
      simpa [k] using LinearMap.congr_fun hp.symm x
    · apply Subtype.ext
      change (e.toLinearMap.comp a).comp f.val = (e.toLinearMap.comp a).comp g.val
      have hh : a.comp f.val = a.comp g.val := by
        simpa only [LinearMap.comp_sub, sub_eq_zero] using ha
      exact congrArg (fun l ↦ e.toLinearMap.comp l) hh

private def vectorMap (R : Type u) [CommRing R]
    {N : Type (max u v)} [AddCommGroup N] [Module R N] (x : N) :
    Coord.{u, v} R 1 →ₗ[R] N :=
  (Finsupp.linearCombination R (fun _ : Fin 1 ↦ x)).comp ULift.moduleEquiv.toLinearMap

private def unitVector (R : Type u) [CommRing R] : Coord.{u, v} R 1 :=
  ULift.up (Finsupp.single 0 1)

private theorem vectorMap_unit (R : Type u) [CommRing R]
    {N : Type (max u v)} [AddCommGroup N] [Module R N] (x : N) :
    vectorMap.{u, v} R x (unitVector.{u, v} R) = x := by
  simp [vectorMap, unitVector]

private def elementObject (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] (m : M) : FreeOver R M :=
  ⟨1, vectorMap.{u, v} R m⟩

private theorem freeCocone_colimit (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    Nonempty (IsColimit (freeCocone R M)) := by
  classical
  have formula (s : Cocone (freeDiagram R M)) (i : FreeOver R M) (x : Coord.{u, v} R i.rank) :
      s.ι.app (elementObject R M (i.hom x)) (unitVector.{u, v} R) = s.ι.app i x := by
    let f : elementObject R M (i.hom x) ⟶ i := ⟨vectorMap.{u, v} R x, by
      ext z
      simp [elementObject, vectorMap, Finsupp.linearCombination_apply,
        Finsupp.sum, map_sum, map_smul]⟩
    have h := congrArg (fun q ↦ q.hom (unitVector.{u, v} R)) (s.w f)
    change s.ι.app i (vectorMap.{u, v} R x (unitVector.{u, v} R)) =
      s.ι.app (elementObject R M (i.hom x)) (unitVector.{u, v} R) at h
    rw [vectorMap_unit] at h
    exact h.symm
  let desc (s : Cocone (freeDiagram R M)) : M →ₗ[R] s.pt :=
    { toFun m := s.ι.app (elementObject R M m) (unitVector.{u, v} R)
      map_add' a b := by
        obtain ⟨k, f, g, _⟩ := freeOver_common R M
          (elementObject R M a) (elementObject R M b)
        let x := f.val (unitVector.{u, v} R)
        let y := g.val (unitVector.{u, v} R)
        have hx : k.hom x = a := by
          simpa [x, elementObject, vectorMap_unit.{u, v}] using
            LinearMap.congr_fun f.property (unitVector.{u, v} R)
        have hy : k.hom y = b := by
          simpa [y, elementObject, vectorMap_unit.{u, v}] using
            LinearMap.congr_fun g.property (unitVector.{u, v} R)
        rw [← hx, ← hy, ← map_add, formula, formula, formula, map_add]
      map_smul' r a := by
        let i := elementObject R M a
        have ha : i.hom (unitVector.{u, v} R) = a := vectorMap_unit.{u, v} R a
        rw [← ha, ← map_smul, formula, formula, map_smul]
        rfl }
  refine ⟨{ desc := fun s ↦ ModuleCat.ofHom (desc s)
            fac := ?_
            uniq := ?_ }⟩
  · intro s i
    apply ModuleCat.hom_ext
    ext x
    exact formula s i x
  · intro s m hm
    apply ModuleCat.hom_ext
    ext x
    have h := congrArg (fun q ↦ q.hom (unitVector.{u, v} R)) (hm (elementObject R M x))
    change m.hom (vectorMap.{u, v} R x (unitVector.{u, v} R)) =
      s.ι.app (elementObject R M x) (unitVector.{u, v} R) at h
    rw [vectorMap_unit] at h
    exact h

/-- A module whose right tensor functor preserves short exact sequences is a
colimit of finite free modules indexed by a small nonempty directed partial order.

Source: Stacks Project, Algebra, Tag 058G (theorem-lazard), forward direction.
(blueprint: lem-kun-lazard-flat-module)

Proof:
1. Apply the hypothesis to an injection and its quotient sequence to obtain
flatness in the sense of def-weil-pbc-flat-ring-map.
2. Form the small category of finite coordinate modules equipped with maps to M.
Direct sums give common successors. The finite-relation factorization consequence
of lem-weil-pbc-flat-equational-criterion, already proved in Mathlib, equalizes
parallel arrows by factoring their common target map through a finite free module
and annihilating their difference. Thus this category is filtered.
3. The forgetful diagram has its canonical cocone with vertex M. For any other
cocone, evaluate its rank-one component at the unit vector to define a map on M.
The arrow sending the unit vector to an arbitrary vector proves compatibility.
Common successors prove additivity, and rank-one objects prove homogeneity and
uniqueness. This gives the colimit universal property of def-weil-pbc-category-colimit.
4. Mathlib's directed replacement of a small filtered category gives a final
functor from a small nonempty directed partial order in the same universe.
Finality transports the colimit universal property. Each restricted stage is
linearly equivalent to its finite coordinate module; uniqueness of colimits
makes the canonical descending map an isomorphism. -/
theorem exists_directed_finite_free_presentation
    (R : Type u) [CommRing R] (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (hM : ∀ (A B C : Type (max u v))
      [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
      [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
        Function.Injective (f.rTensor M) ∧
        Function.Exact (f.rTensor M) (g.rTensor M) ∧ Function.Surjective (g.rTensor M)) :
    ∃ (I : Type (max u v)) (_ : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·)) (F : I ⥤ ModuleCat.{max u v} R)
      (ι : F ⟶ (Functor.const I).obj (ModuleCat.of R M)),
      (∀ i : I, ∃ r : ℕ, Nonempty ((F.obj i) ≃ₗ[R] (Fin r → R))) ∧
        IsIso (colimit.desc F (Cocone.mk (ModuleCat.of R M) ι)) := by
  classical
  have : Flat R M := Flat.iff_rTensor_preserves_injective_linearMap.mpr (by
    intro A B _ _ _ _ f hf
    exact (hM A B (B ⧸ LinearMap.range f) f (LinearMap.range f).mkQ hf
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)).1)
  obtain ⟨I, hI, hdir, hne, G, hG⟩ := IsFiltered.exists_directed (FreeOver R M)
  let := hI
  let := hdir
  let := hne
  let := hG
  let F := G ⋙ freeDiagram R M
  let c := (freeCocone R M).whisker G
  have hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv G (freeCocone R M)).symm
      (freeCocone_colimit R M).some
  refine ⟨I, hI, hne, hdir, F, c.ι, ?_, ?_⟩
  · intro i
    refine ⟨(G.obj i).rank, ⟨?_⟩⟩
    exact ULift.moduleEquiv.trans (Finsupp.linearEquivFunOnFinite R R (Fin _))
  · exact ((colimit.isColimit F).nonempty_isColimit_iff_isIso_desc).mp ⟨hc⟩

end

end Module
