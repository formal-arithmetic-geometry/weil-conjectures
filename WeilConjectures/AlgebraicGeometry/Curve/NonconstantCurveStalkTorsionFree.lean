/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Nonconstant maps to integral curves give torsion-free stalk modules

Source: Stacks Project, `literature/stacks-project/curves.tex`, Tag 0CCK, lemma-flat;
`literature/stacks-project/morphisms.tex`, Tag 0CC1, lemma-dominant-between-integral
(blueprint: `lem-a1-nonconstant-curve-stalk-torsion-free`).

The statement records the nonconstant-to-dominant argument for an integral source and
one-dimensional integral target, the induced generic-point and stalk injections, and the
resulting torsion-free stalk modules.  Its five proof steps are: dimension and generic-point
existence; dominance from the two-point image; generic function-field injections; the germ
square and stalk injectivity; and cancellation in the domain stalks.
-/

@[expose] public section

set_option autoImplicit false


universe u

open CategoryTheory

namespace AlgebraicGeometry

/--
A nonconstant morphism from an integral scheme to an integral curve is dominant, has injective
maps on all stalks, and makes each source stalk torsion free over the target stalk.

Source: Stacks Project, `literature/stacks-project/curves.tex`, Tag 0CCK, lemma-flat, proof;
`literature/stacks-project/morphisms.tex`, Tag 0CC1, lemma-dominant-between-integral, (2) implies
(6) (blueprint: `lem-a1-nonconstant-curve-stalk-torsion-free`).

Proof:
1. By `def-pc-curve` and `def-pc-integral-scheme`, both schemes are nonempty and irreducible.
   Their generic points exist by `lem-sc-scheme-sober`; `def-pc-dimension` together with
   `lem-pc-scheme-dimension-local-rings` identifies the curve's dimension-one hypothesis with
   topological Krull dimension one.
2. Let `z = f (genericPoint X)`. Continuity places every image point in the closure of `z`.
   If `z` is not the generic point of `Y`, a strict specialization in its proper irreducible
   closure would give a chain of length two, contradicting dimension one. The image would then
   be a singleton, contrary to the two-point hypothesis; hence `z` is generic and `f` is dense.
3. The generic stalks are fields and every stalk embeds in its function field by
   `lem-sc-integral-scheme-stalks-in-function-field`. The generic stalk map is a unital map of
   fields and is injective.
4. For each `x`, the square formed by the stalk map and the two maps to generic stalks commutes
   on germs, using `def-weil-pbc-module-stalk` and the locally ringed-space morphism interface.
   The target-to-function-field composite is injective, so the stalk map is injective.
5. Both stalks are domains and the stalk map is injective. Thus a nonzero target element maps to
   a nonzero source element, and cancellation in the source domain gives the asserted
   torsion-free condition.
-/
theorem Scheme.Hom.nonconstant_curve_stalk_torsion_free {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] (sY : Y ⟶ Spec (.of k)) [IsIntegralCurve sY]
    (f : X ⟶ Y) (h_nonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) :
    f (genericPoint X) = genericPoint Y ∧ DenseRange f ∧ ∀ x : X,
      IsDomain (Y.presheaf.stalk (f x)) ∧ IsDomain (X.presheaf.stalk x) ∧
        Function.Injective (f.stalkMap x) ∧
          ∀ (a : Y.presheaf.stalk (f x)) (b : X.presheaf.stalk x),
            a ≠ 0 → (f.stalkMap x) a * b = 0 → b = 0 := by
  have hdim : topologicalKrullDim Y ≤ 1 := by
    rw [IsIntegralCurve.topologicalKrullDim_eq_one (f := sY)]
  have hgeneric (z : Y) (hz : z ≠ genericPoint Y) :
      genericPoint Y ∉ closure ({z} : Set Y) := by
    intro h
    have hle : closure ({genericPoint Y} : Set Y) ⊆ closure ({z} : Set Y) :=
      closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure
    have heq : closure ({z} : Set Y) = Set.univ := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · rw [← (genericPoint_spec Y).def]
        exact hle
    have hzgen : IsGenericPoint z (closure ({z} : Set Y)) := isGenericPoint_closure
    have hηgen : IsGenericPoint (genericPoint Y) (closure ({z} : Set Y)) := by
      rw [heq]
      exact genericPoint_spec Y
    exact hz (hzgen.eq hηgen)
  have hgen : f (genericPoint X) = genericPoint Y := by
    by_contra hne
    let z : Y := f (genericPoint X)
    have hz : z ≠ genericPoint Y := by simpa [z] using hne
    let U : Y.Opens := ⟨(closure ({z} : Set Y))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : IsOpen (U : Set Y) := U.isOpen
    have hηU : genericPoint Y ∈ U := by
      change genericPoint Y ∉ closure ({z} : Set Y)
      exact hgeneric z hz
    have hneU : (U : Set Y).Nonempty := ⟨genericPoint Y, hηU⟩
    have hzU : z ∉ U := by
      change z ∉ (closure ({z} : Set Y))ᶜ
      exact fun h' ↦ h' (subset_closure (Set.mem_singleton z))
    have hclosed : IsClosed ({z} : Set Y) :=
      IsOpen.isClosed_singleton_of_mem_compl hdim hU hneU hzU
    have hsubset : ∀ x : X, f x = z := by
      intro x
      have hs : z ⤳ f x := (genericPoint_specializes x).map f.continuous
      have hm : f x ∈ closure ({z} : Set Y) := hs.mem_closure
      rw [hclosed.closure_eq] at hm
      exact Set.mem_singleton_iff.mp hm
    obtain ⟨x₁, x₂, hx⟩ := h_nonconstant
    exact hx (by rw [hsubset x₁, hsubset x₂])
  have hdense : DenseRange f := by
    have hd : Dense (Set.range f) := by
      apply (dense_of_genericPoints_subset (α := Y))
      rw [genericPoints_eq_singleton]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨genericPoint X, hgen.trans hy.symm⟩
    exact hd
  have hgeneric_inj : Function.Injective (f.stalkMap (genericPoint X)).hom := by
    let e : Y.presheaf.stalk (f (genericPoint X)) ≅
        Y.presheaf.stalk (genericPoint Y) :=
      eqToIso (congrArg (fun y : Y => Y.presheaf.stalk y) hgen)
    let g := e.inv ≫ f.stalkMap (genericPoint X)
    have hg : Function.Injective g.hom := by
      exact RingHom.injective _
    intro a b hab
    apply e.commRingCatIsoToRingEquiv.injective
    apply hg
    change g.hom (e.hom a) = g.hom (e.hom b)
    simpa [g, Category.assoc] using hab
  have hstalk_inj (x : X) : Function.Injective (f.stalkMap x).hom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm _ bot_le
    intro r hr
    change (f.stalkMap x).hom r = 0 at hr
    obtain ⟨U, hxU, s, rfl⟩ := Y.presheaf.exists_germ_eq r
    rw [f.germ_stalkMap_apply] at hr
    have he : X.presheaf.germ (f ⁻¹ᵁ U) x hxU (f.app U s) =
        X.presheaf.germ (f ⁻¹ᵁ U) x hxU 0 := by simpa using hr
    obtain ⟨W, hxW, i, j, hij⟩ := X.presheaf.germ_eq x hxU hxU _ _ he
    have hηW : genericPoint X ∈ W := by
      exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
        (by simpa using (show (W : Set X).Nonempty from ⟨x, hxW⟩))
    have hηzero : X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X)
        (i.le hηW) (f.app U s) = 0 := by
      rw [← X.presheaf.germ_res_apply i (genericPoint X) hηW, hij]
      simp
    have hηU : f (genericPoint X) ∈ U := i.le hηW
    have htargetzero : Y.presheaf.germ U (f (genericPoint X))
        hηU s = 0 := by
      apply hgeneric_inj
      rw [f.germ_stalkMap_apply]
      simpa using hηzero
    have hszero : s = 0 := by
      apply (germ_injective_of_isIntegral (X := Y)
        (f (genericPoint X)) hηU)
      simpa using htargetzero
    simp [hszero]
  refine ⟨hgen, hdense, ?_⟩
  intro x
  refine ⟨inferInstance, inferInstance, hstalk_inj x, ?_⟩
  intro a b ha hab
  have hfa : (f.stalkMap x).hom a ≠ 0 := by
    intro hzero
    exact ha ((hstalk_inj x) (by simpa using hzero))
  exact (mul_eq_zero.mp hab).resolve_left hfa


end AlgebraicGeometry
