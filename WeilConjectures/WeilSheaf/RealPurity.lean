/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Purity of real lisse Weil sheaves on curves, and lisse loci

This file states, for Weil sheaves on curves over a finite field `k₀`, three results of the
section on the purity of real sheaves which the Deligne–Laumon estimate on the affine line
uses:

- `AlgebraicGeometry.WeilSheaf.exists_isPunctuallyPureOfWeight_of_isReal`: an irreducible
  constituent of an `ι`-real lisse Weil sheaf on a smooth geometrically connected affine curve
  is punctually `ι`-pure of some real weight (blueprint `thm-rp-real-lisse-purity-affine`).
- `AlgebraicGeometry.WeilSheaf.exists_isLisse_upperStar`: a Weil sheaf on an irreducible
  scheme of finite type over `k₀` is lisse on a nonempty open (blueprint
  `fin2-lem-lisse-dense-open`).
- `AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`: a lisse Weil
  sheaf on a smooth geometrically connected curve which is punctually pure of weight `w` on a
  nonempty open is punctually pure of weight `w` everywhere (blueprint
  `cor-wf-unramified-boundary-purity`).

They are nodes of the blueprint subsections `sk-p-real-purity` and `sk-p-real-semi`, whose
formalisation for Weil sheaves is pending; the representation-theoretic form of the first one
is `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Curve

variable {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]

/-- **Purity of real lisse sheaves on an affine curve.** Let `G` be an `ι`-real lisse Weil sheaf
on a smooth geometrically connected affine curve `V` over `k₀`. Every irreducible constituent
`S` of `G` — an irreducible lisse sheaf which is a quotient of a lisse subsheaf `B` of `G` — is
punctually `ι`-pure of some real weight (namely its determinant weight).
(blueprint: `thm-rp-real-lisse-purity-affine`, subsection `sk-p-real-purity`) -/
theorem exists_isPunctuallyPureOfWeight_of_isReal [IsAffine V] (ι : PadicAlgCl l →+* ℂ)
    {G : WeilSheaf k₀ l V} (hG : G.IsLisse) (hreal : G.IsReal ι) {S : WeilSheaf k₀ l V}
    (hS : S.IsIrreducibleLisse) {B : WeilSheaf k₀ l V} (hB : B.IsLisse) (i : B ⟶ G) [Mono i]
    (p : B ⟶ S) [Epi p] :
    ∃ v : ℝ, S.IsPunctuallyPureOfWeight ι v :=
  sorry

/-- **Purity extends over the missing points.** Let `G` be a lisse Weil sheaf on a smooth
geometrically connected curve `V` over `k₀`, and let `U ⊆ V` be a nonempty open on which `G` is
punctually `ι`-pure of weight `w`. Then `G` is punctually `ι`-pure of weight `w` on all of `V`:
at a point of `V ∖ U` the inertia acts trivially on the lisse sheaf `G`, so the stalk is the
inertia-invariant boundary stalk of the restriction, which is pure of weight `w`.
(blueprint: `cor-wf-unramified-boundary-purity`, consequence clause, subsection `sk-p-real-semi`)
-/
theorem IsLisse.isPunctuallyPureOfWeight_of_upperStar (ι : PadicAlgCl l →+* ℂ)
    {G : WeilSheaf k₀ l V} (hG : G.IsLisse) (U : V.Opens) (hU : (U : Set V).Nonempty) {w : ℝ}
    (hw : ((WeilSheaf.upperStar U.ι).obj G).IsPunctuallyPureOfWeight ι w) :
    G.IsPunctuallyPureOfWeight ι w :=
  sorry

end Curve

/-- **Lisse on a nonempty open.** A Weil sheaf `F` on an irreducible scheme `X` of finite type
over `k₀` is lisse on a nonempty open `U ⊆ X`.
(blueprint: `fin2-lem-lisse-dense-open`, subsection `sk-p-real-purity`) -/
theorem exists_isLisse_upperStar {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IrreducibleSpace X]
    (F : WeilSheaf k₀ l X) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ ((WeilSheaf.upperStar U.ι).obj F).IsLisse :=
  sorry

end AlgebraicGeometry.WeilSheaf
