/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Relative finite Tor dimension of a perfect complex

Source: Stacks Project, More on Morphisms, Tag 0B6G, verification of condition (3),
and `more-morphisms-lemma-check-perfect-stalks`.
(blueprint: lem-pc-perfect-relative-finite-tor).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact source locally of finite type over a Noetherian base,
stalkwise finite Tor dimension of the morphism gives relative finite Tor dimension
of every perfect complex. Properness and derived direct image are not needed.
Source: Stacks Project, More on Morphisms, Tag 0B6G, condition (3), and
`more-morphisms-lemma-check-perfect-stalks`, implication (3) to (2).

Proof: a locally finite-type map to a Noetherian scheme is pseudo-coherent.
The stalk criterion for perfect morphisms upgrades the pointwise bounds to finite
Tor bounds on neighbourhoods; this step uses pseudo-coherence, not just compactness.
Thus the structure sheaf locally has finite Tor dimension over the inverse-image
structure sheaf. Intersect this cover with the strictly perfect neighbourhoods of E.
If a representative has terms in [r,s] and the structure sheaf has Tor amplitude
[-d,0], its finite free terms have that amplitude, their retracts do too, and the
finite complex has amplitude [r-d,s], by its filtration by terms. Quasi-compactness
selects finitely many such neighbourhoods and gives one interval [a,b] on X.
Choose a complex K representing E and a K-flat resolution P of its restriction of
scalars. Tensoring P with any inverse-image-structure-sheaf module computes the
relative derived tensor. The stalkwise bounds imply its homology vanishes outside
[a,b], for every module. Enlarge the interval if necessary to have a ≤ b.
For empty X, use [0,0]; the zero complex likewise has amplitude in [0,0].
(blueprint: lem-pc-perfect-relative-finite-tor). -/
theorem perfect_hasFiniteTorDimensionOver
    {X Y : Scheme.{u}} [CompactSpace X] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    HasFiniteTorDimensionOver f E := by sorry

end AlgebraicGeometry.Scheme
