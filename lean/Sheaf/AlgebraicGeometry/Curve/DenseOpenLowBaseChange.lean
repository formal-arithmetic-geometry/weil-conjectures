/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Paper.ZeroDimensionalCohomology
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Dense-open field-extension comparison ingredients -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Simultaneous degree-zero and degree-one comparison bijections transfer across
extension by zero from a dense open, for one algebraically closed field extension.
Source: Stacks Project, Tag 0GJA, proof (five-term exact sequence and remark (c)).
(blueprint: lem-pbc-x2-dense-open-low-base-change)

Proof: The reduced closed complement is a finite union of spectra of k, since density
excludes the generic points of the Noetherian curve. Its base change is the corresponding
union of spectra of k'. Closed direct image is exact and its cohomology is that of the
complement. The degree-zero comparison is the product of the canonical stalk comparisons,
which are bijections; positive cohomology vanishes over both fields. The open-closed
short exact sequence and its inverse image therefore give the commuting five-term ladder
0 -> H⁰(G) -> H⁰(F) -> H⁰(B) -> H¹(G) -> H¹(F) -> 0, with the canonical cohomologyMap
as vertical maps. If the two G maps are bijections, the five lemma gives both F maps.
Conversely the first four-term diagram gives injectivity and surjectivity at H⁰(G),
and the last five-term diagram gives the bijection at H¹(G), using both F bijections
and the B bijection. Empty complements and empty schemes give the same exact diagram. -/
theorem dense_open_low_base_change (Λ : Type (u + 1)) [CommRing Λ]
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (∀ q : ℕ, q ≤ 1 → Function.Bijective (cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)) ↔
    (∀ q : ℕ, q ≤ 1 → Function.Bijective (cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q)) := by
  sorry

end AlgebraicGeometry.IsCurve
