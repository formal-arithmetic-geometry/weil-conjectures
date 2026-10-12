/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Unconditional finiteness of all cohomology groups is invariant under restriction
and extension by zero across a dense open of a curve.
Source: Stacks Project, Tag 0GJA, proof, the five-term sequence and finite boundary term.
(blueprint: lem-pbc-a3-dense-open-cohomology-finiteness).

Proof: Write G = j_!j^*F and B = i_*i^*F for the reduced closed complement. The dense
open contains all generic points of X. The Noetherian complement has dimension zero
and is a finite union of k-rational points. H^0(B) is a finite product of finite stalk
modules: constructibility gives finite generation and the coefficient ring is finite.
All positive cohomology of B vanishes. The open-closed short exact sequence gives
0 -> H^0(G) -> H^0(F) -> H^0(B) -> H^1(G) -> H^1(F) -> 0 and bijections above degree one.
If all H^q(F) are finite, H^0(G) injects into H^0(F), and H^1(G) has finite kernel
(a quotient of H^0(B)) and finite image in H^1(F). Conversely H^0(F) has finite kernel
H^0(G) and finite image in H^0(B), and H^1(F) is a quotient of H^1(G). In higher degrees
use the bijections. The zero boundary for U=X and empty X gives the same argument.
Neither a prime annihilator nor properness is required. -/
theorem dense_open_cohomology_finiteness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (∀ q : ℕ, Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)) ↔
    (∀ q : ℕ, Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q)) := by
  sorry

end AlgebraicGeometry.IsCurve
