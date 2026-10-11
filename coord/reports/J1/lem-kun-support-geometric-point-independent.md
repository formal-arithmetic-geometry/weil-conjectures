## Worker report

The module states `AlgebraicGeometry.Scheme.isZero_sheafFiber_iff_of_same_image`;
its proof is `sorry`. The node has no `stmt_deps`. It uses Mathlib's
`AlgebraicGeometry.Scheme.pointSmallEtale` from
`Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and the associated
`CategoryTheory.GrothendieckTopology.Point.sheafFiber`.

Statement comparison:

- `X` is `{X : Scheme.{u}}`; there is no base-field, finiteness, or
  nonemptiness assumption.
- `x ∈ X` is represented by the common image expressed by
  `(h : s default = s' default)`. Every point over which both geometric
  points lie is allowed.
- The two geometric points are `s : Spec (.of Ω) ⟶ X` and
  `s' : Spec (.of Ω') ⟶ X`. The fields are separately bound with
  `[Field Ω] [IsAlgClosed Ω]` and `[Field Ω'] [IsAlgClosed Ω']`.
- The etale sheaf of abelian groups is
  `(F : Sheaf X.smallEtaleTopology Ab.{u + 1})`. The abelian coefficient
  category makes the zero-stalk assertion meaningful, as in the support
  definition `def-kun-support`.
- `F_{bar x} = 0` is
  `IsZero ((pointSmallEtale s).sheafFiber.obj F)`; the primed clause uses
  `s'`. `IsZero` means a zero object, without requiring equality to the
  chosen representative of the zero object. The `↔` is exactly simultaneous
  vanishing.
- The support clause is the direct consequence of this equivalence and
  the node's stated definition of support by nonvanishing of a geometric
  stalk; there is no separate support declaration yet, and no support
  hypothesis is needed by this theorem.

Edge cases: the empty scheme is permitted (the quantified points then have
no instances); no restriction on the characteristic or on residue-field
extensions is imposed. The two geometric points may be equal. Both stalks
may be zero. The fields are separate and may have different cardinalities
within the scheme universe.

Searches: `msearch.py ... leanfinder` with "the stalk of an etale sheaf of
abelian groups at two geometric points above the same scheme point is zero
simultaneously" returned etale-locus results, none about stalks. `msearch.py
... loogle` with `AlgebraicGeometry.Scheme.pointSmallEtale,
CategoryTheory.GrothendieckTopology.Point.sheafFiber` returned zero hits.
`msearch.py ... grep` with `pointSmallEtale|sheafFiber|geometric.*stalk` in
`AlgebraicGeometry/Sites` found `EtalePoint.lean`'s point construction but no
independence theorem. `rg` in `WeilConjectures`, Mathlib, and `lean/Sheaf`
found no `isZero_sheafFiber_iff_of_same_image`; the source search for the
node ID found none. Existing source uses `pointSmallEtale` and `sheafFiber`
in other stalk results, but none states simultaneous zero stalks above the
same underlying point.

The blueprint and Stacks source trees cited by the node are absent from this
read-only repository copy. I checked the node's full statement and three
proof steps in its JSON record and the related `def-kun-support` node.

## Second reading by J1

The node introduces a scheme `X`; a point `x ∈ X`; geometric points
`bar x` and `bar x'` over `x`; and an etale sheaf of abelian groups `F`.
The Lean renders these as `{X : Scheme.{u}}`, two morphisms
`s : Spec (.of Ω) ⟶ X` and `s' : Spec (.of Ω') ⟶ X`, with separate
`[Field Ω] [IsAlgClosed Ω]` and `[Field Ω'] [IsAlgClosed Ω']` assumptions,
and `F : Sheaf X.smallEtaleTopology Ab.{u + 1}`.  The common-image
hypothesis is exactly `h : s default = s' default`; since `Spec Ω` and
`Spec Ω'` each have a unique point, this is the node's `x` together with
both points lying over it, without unnecessarily binding a redundant `x`.

The conclusion's first clause, `F_{bar x} = 0`, is rendered as
`IsZero ((pointSmallEtale s).sheafFiber.obj F)`; the primed clause is the
same expression with `s'`, and the connective and quantifier order are the
node's `↔` for the fixed `s`, `s'`, and `F`.  The final support-independence
sentence is the stated consequence of this equivalence and is not a second
formal predicate, since the support definition is a separate node.  No
mismatch was found and no Lean change was required in this second reading.

Edge cases checked: `X` may be empty (then there are no such morphisms), the
two geometric points may coincide, both stalks may be zero, and `Ω` and `Ω'`
may be different algebraically closed fields.  No characteristic, residue
field, finiteness, nonemptiness, or Noetherian hypothesis is added; `n = 0`
and zero-object cases are irrelevant to this statement and are not excluded.
The single universe `u` is forced by `Scheme.{u}` and still permits every
Mathlib geometric point admitted by `pointSmallEtale`.

Searches independently confirmed the worker's result: `rg` over Mathlib and
`WeilConjectures/`, plus the `msearch.py` LeanFinder, Loogle, and grep
queries recorded above, found only the generic `pointSmallEtale` and
`sheafFiber` constructions and no independence theorem or support
definition.  The source-tree search for the node id and theorem name also
found no existing declaration.
