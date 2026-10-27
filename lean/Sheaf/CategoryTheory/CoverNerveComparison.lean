/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Canonical comparison of the nerve of one covering

Source: Stacks Project, Cohomology on Sites, Tag 0D6X, proof of
`lemma-pullback-injective-pre-limp`, and Sites, Tag 00WV, conditions (1) and (2)
for the one fixed covering (blueprint: lem-trf-continuous-cover-nerve-comparison).

The comparison is constructed from the chosen tuple universal property. Its
invertibility needs preservation only of base changes of the fixed covering's members.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SiteCechComplex

/-- The canonical comparison into a chosen tuple product of the image family.
The universal property determines its data uniquely by the mapped projections;
no preservation hypothesis or choice of an unspecified isomorphism is used.
Source: Stacks 0D6X, iterated fibre-product identity and its canonical projections;
03AK, tuple universal property (blueprint: lem-trf-continuous-cover-nerve-comparison). -/
noncomputable def functorComparison {C D : Type u} [Category.{u} C] [Category.{u} D]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (F : C ⥤ D) (S : SiteCechComplex f hom)
    (P : SiteCechComplex (fun t ↦ F.obj (f t)) (fun t ↦ F.map (hom t)))
    (n : ℕ) (t : Fin (n + 1) → T) : F.obj (S.W n t) ⟶ P.W n t :=
  (P.universal n t (F.obj (S.W n t)) (fun k ↦ F.map (S.pr n t k))
    (fun k ↦ (F.map_comp (S.pr n t k) (hom (t k))).symm.trans
      ((congrArg (fun h : S.W n t ⟶ U ↦ F.map h) (S.comm n t k)).trans
        (F.map_comp (S.pr n t 0) (hom (t 0)))))).exists.choose

/-- Cover-local preservation identifies every positive-length tuple product and all
its index maps. `PreservesLimit (cospan a (hom t)) F` expresses invertibility of the
canonical binary pullback comparison: the requisite pullbacks exist by the two
site axioms and the two covering assumptions. It asserts nothing about other covers.

Source: Stacks 0D6X, proof of `lemma-pullback-injective-pre-limp`, using only
00WV(1),(2) for this covering
(blueprint: lem-trf-continuous-cover-nerve-comparison).

Proof plan, following the six steps of the node:
1. The tuple universal property of def-weil-pbc-site-cech-complex applied to the
mapped source projections defines `functorComparison` and gives its projection equations.
For a singleton tuple it is the comparison between the prescribed degree-zero choices.
2. Induct on positive tuple length. Split off the last member. By the source site
axiom in def-weil-pbc-sites-and-cohomology the binary pullback of that member along
the prefix structure map exists. The tuple universal properties identify the chosen
long tuple with this binary pullback: construct both maps from the projections;
check their composites on each projection.
3. The image covering gives the corresponding target binary pullback. The hypothesis
`hbase` identifies it with the image of the source binary pullback. Compose this
binary comparison with the mapped source rebracketing isomorphism.
4. Given a compatible tuple of arrows from a target test object, the induction
hypothesis lifts its prefix uniquely. The prefix is nonempty, so its structure
map agrees with the last arrow over the base. Step 3 then lifts the whole tuple
uniquely. Thus the mapped source long tuple has the target tuple universal property.
5. Both it and the independently chosen target tuple are universal. Their unique
projection-compatible map, precisely `functorComparison`, is therefore invertible.
6. For any index map, compose each side of the asserted equality with the k-th
target projection. Use `indexMap_pr`, the comparison projection equation, and
functoriality: both composites are `F.map (S.pr n t (α k))`. Tuple uniqueness
implies equality. This includes repetitions, permutations, faces and degeneracies.
An empty covering has no positive-length tuples; no final object is used. -/
theorem cover_nerve_comparison {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (F : C ⥤ D) {T : Type u} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U)
    (himage : Presieve.ofArrows (fun t ↦ F.obj (f t)) (fun t ↦ F.map (hom t)) ∈
      K (F.obj U))
    (hbase : ∀ (t : T) (V : C) (a : V ⟶ U), PreservesLimit (cospan a (hom t)) F)
    (S : SiteCechComplex f hom)
    (P : SiteCechComplex (fun t ↦ F.obj (f t)) (fun t ↦ F.map (hom t))) :
    (∀ (n : ℕ) (t : Fin (n + 1) → T) (k : Fin (n + 1)),
      functorComparison F S P n t ≫ P.pr n t k = F.map (S.pr n t k)) ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → T), IsIso (functorComparison F S P n t)) ∧
    (∀ (n m : ℕ) (t : Fin (n + 1) → T) (α : Fin (m + 1) → Fin (n + 1)),
      F.map (S.indexMap t α) ≫ functorComparison F S P m (t ∘ α) =
        functorComparison F S P n t ≫ P.indexMap t α) := by
  sorry

end CategoryTheory.SiteCechComplex
