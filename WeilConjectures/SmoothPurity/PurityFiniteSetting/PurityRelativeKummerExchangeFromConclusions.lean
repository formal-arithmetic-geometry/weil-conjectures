/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-! # Exchange from the relative Kummer computations over both bases

Source: blueprint latest, relative Kummer proof, Step 3 and comparison paragraph
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Conditional exchange for an arbitrary map of k-schemes, assuming the relative
computations on both bases. This does not assert any relative computation itself.
Source: blueprint latest, sk-lem-sp-reduction/prop-pur-gm-relative-kummer.proof.md,
Step 3 and comparison paragraph
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).

Proof: the actual line and punctured-line squares are cartesian. Pullback preserves
the coordinate unit, and naturality of the ordinary Kummer boundary with the
normalized root insertion and finite twist comparison gives the displayed equality
of coordinate classes. Apply the etale/pro-etale comparison's unit and edge
identities to the assumed relative conclusions on B and B', obtaining the etale
unit, generator and vanishing hypotheses over both bases. For the affine square,
apply the degree-zero exchange criterion: the exchange-unit identity makes its
H0 map invertible and every other homology object is zero. For the punctured square,
apply the exchange-generators criterion with the coordinate class and the canonical
twist pullback. Its unit identity handles degree zero; its edge identity and the
Kummer naturality just proved identify the degree-one map with the two generator
isomorphisms. Higher positive degrees vanish by the two relative computations;
negative degrees vanish by left exactness on the degree-zero coefficient objects.
The cohomological criterion makes both etale exchanges invertible. Finally both
projections are affine, hence qcqs, and the specified comparison conjugates these
etale exchanges to the displayed pro-etale exchanges. This argument does not assume
that either base or g is of finite type. -/
theorem relative_kummer_base_change_of_relative_conclusions
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    {B' B : Scheme.{u}} (g : B' ⟶ B)
    (a : B ⟶ Spec (CommRingCat.of P.field.k))
    (hB : P.RelativeKummerConclusions h B a)
    (hB' : P.RelativeKummerConclusions h B' (g ≫ a)) :
    P.KummerBaseChangeConclusions h g a := by sorry

end WeilConjectures.PurityFiniteSetting
