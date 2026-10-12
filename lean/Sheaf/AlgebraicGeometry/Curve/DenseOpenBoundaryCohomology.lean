/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

-- The modules of the geometric proof plan remain reachable while this theorem is open.
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.Paper.ZeroDimensionalCohomology
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Cohomology of the closed boundary of a dense open curve

Source: Stacks Project, Tag 0GJA, proof of lemma-restrict-to-open.
(blueprint: lem-pbc-g2-dense-open-boundary-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The closed-boundary sheaf has finite degree-zero cohomology and zero positive-degree cohomology.
Source: Stacks Project, Tag 0GJA, proof of lemma-restrict-to-open, finite stalk product.
(blueprint: lem-pbc-g2-dense-open-boundary-cohomology).

Proof: Since X is finite type over k, it is Noetherian. A dense open meets each irreducible
component at its generic point. Thus its closed complement in a space of dimension at most
one has dimension zero. It is a finite set of closed points, each with residue field k.
The vanishing ideal gives the reduced induced closed subscheme Z on that complement.
The pullback of F to Z has finite stalks: constructibility gives finitely generated
Lambda-modules, and Lambda is finite. The etale cohomology of this zero-dimensional scheme
is the finite product of those stalks in degree zero and zero in positive degrees.
The closed immersion i is finite, so its direct image is exact and Leray identifies
H^q(X, i_*i^*F) with H^q(Z, i^*F). Forgetting the module structure preserves these
identifications. This proves the two conclusions. For U = X, Z is empty, the product is the
zero group, and the same argument applies; for empty X both conclusions are immediate. -/
theorem dense_open_boundary_cohomology (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (U : X.Opens) (hU : Dense (U : Set X)) :
    let I := Scheme.IdealSheafData.vanishingIdeal U.compl
    let B := (I.subschemeι)_*[ModuleCat.{u + 1} Λ].obj
      ((I.subschemeι)^*[ModuleCat.{u + 1} Λ].obj F)
    let B' := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj B
    Finite (Sheaf.H B' 0) ∧ (∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H B' q)) := by sorry

end AlgebraicGeometry.IsCurve
