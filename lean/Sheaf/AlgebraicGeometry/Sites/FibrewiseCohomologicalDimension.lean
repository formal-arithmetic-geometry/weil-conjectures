/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension

/-!
# Fibrewise cohomological dimension over an algebraically closed field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
fin4-lem-fibrewise-cohomological-dimension.md
(blueprint: fin4-lem-fibrewise-cohomological-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A constructible sheaf with the finite coefficients of smooth base change on a finite-type
scheme of dimension at most `d` over an algebraically closed field has zero ordinary etale
cohomology in degrees greater than `2 * d`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`fin4-lem-fibrewise-cohomological-dimension.md`
(blueprint: fin4-lem-fibrewise-cohomological-dimension).

Proof: The coefficient convention supplies a positive integer `N` annihilating the ring.
Thus `N` kills every local section of the underlying abelian sheaf, which is torsion in the
local-section sense of `def-weil-pbc-etale-sheaves`. An algebraically closed field is
separably closed, since each irreducible minimal polynomial has degree one. The vanishing
of `lem-kun-03qu-sep-closed` gives torsion cohomological dimension at most zero for its
spectrum, in the sense of `def-sc-etale-torsion-cd`. If `X` is empty, the empty covering
forces all abelian sheaf sections, and hence their cohomology, to vanish. Otherwise its
actual dimension `e` satisfies `0 ≤ e ≤ d`. Apply `thm-sc-finite-type-torsion-cd` with ground
field bound zero and dimension `e`. It yields vanishing above `2 * e`, hence above `2 * d`.
Cohomology here is the ordinary derived-section cohomology of
`def-weil-pbc-etale-cohomology`, applied to the underlying abelian sheaf in degree zero. -/
theorem subsingleton_cohomology_of_isAlgClosed_of_constructible
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton
      ((cohomology AddCommGrpCat.{u + 1} X q).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
