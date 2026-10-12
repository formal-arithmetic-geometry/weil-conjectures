## What changed

Proved `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreCompletion` with
its existing signature and visibility. Its two new proof-only imports separate scheme
functoriality from the distinguished structural fibre. Transport by the affine
presentations and `Spec.preimage` gives the ring homomorphism. Evaluating the structural
square at the B closed point and applying the singleton-fibre assertion proves that its
spectrum map preserves closed points; Mathlib then proves locality.

Added `Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality`. Its public theorem
`AlgebraicGeometry.Scheme.exists_strictHenselizationSchemeMap` is proved, without new holes.
The private cone helper reindexes the existing spectrum cone, uses the affine Gamma-Spec
unit, and extends it along the initial representative functor. The private pointed
pullback functor is a concrete construction. Pullback projections give a cone, and its
lift through the other limit supplies the required map over g. Neither private helper
contains `sorry`; no arbitrary data is selected from an unproved existence theorem.

Added `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber` for the one unfinished part:
the structural fibre over the original geometric point is its singleton closed point.
The statement only involves one scheme and one local affine presentation. It assumes no
compatible morphism g, constructs no ring map, and is strictly a part of the argument.
Its docstring gives the affine-chart/triple-colimit proof, including both implications.
The two existing triple-comparison statements named in its node are the intended route
for its next worker; they are not newly restated here.

Updated the original node's proof, proof dependencies and proof origin; its statement
and Lean record are unchanged. No existing public imports changed. A declaration-scoped
`linter.unusedVariables.funArgs false` retains the original existential binder `hφ`,
which does not occur in its conclusion, without an unused-argument warning. All three
modules compile with `lcompile.py --all` without warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreCompletion`
(node `compatible-strict-henselization-core-completion`): 1 of 1 original holes closed.
The item's module now contains no `sorry`.

Also proved the new
`AlgebraicGeometry.Scheme.exists_strictHenselizationSchemeMap`
(node `lem-weil-pbc-strict-henselization-scheme-functoriality`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint`
(node `lem-weil-pbc-strict-henselization-closed-fiber`), whose proof is exactly `by sorry`.
There are no other holes in the delivery. This is a decomposition of the original
hole, with the scheme construction actually proved, not a net decrease in holes.
No claim is made that the original result is free of `sorryAx` transitively.

## No longer needed

No original library module is pruned. The original direct proof dependencies
`def-weil-pbc-strict-henselization-limit` and
`def-weil-pbc-strict-henselization-structural-map` are retained transitively through
the two new lemmas, rather than discarded. Both original public imports
are required by the unchanged statement. The scheme functoriality proof uses the existing
strict-henselization construction and its structural-map characterization. The entire
unit route in `dag/units/sk-thm-p1.json` is retained.

The second reading also removed redundant explicit Mathlib imports from the two
new modules (Final, OverAdjunction and Prime.Topology); their APIs remain available
through the public structural-map import. This removes no module from the existing
target import closure.

The stronger pointed residue functoriality APIs in
`Sheaf.Paper.StrictHenselizationFunctoriality` and
`Sheaf.Paper.StrictHenselizationMapExists` are not needed by this proof and were never
imported. No pruning of their other users is claimed.

## Where the brief, the DAG or earlier work was wrong

The original node's single step describes a construction but lists only definitions as
its dependencies. Those definitions suffice for the scheme morphism, as the new Lean
proof demonstrates, but they do not alone assert that the closed point maps to the
closed point. The singleton-fibre theorem records precisely this missing geometric
input, sourced to Stacks Tags 04HX, 04GW and 04GP. In particular Tag 04GU is in the
Algebra chapter, not `etale-cohomology.tex`. The local literature files are absent on
this machine, so the official Stacks tag pages were read for these assertions.

An unused possible route revealed a separate problem:
`STATEMENT-DISPUTED: AlgebraicGeometry.strictHenselizationPointedMap_factorization`
(`lean/Sheaf/Paper/StrictHenselizationPointedMap.lean`) quantifies over every ring map ψ
without requiring ψ to be the selected geometric-point evaluation. For S = Spec k,
Ω = k algebraically closed, the strict-henselization ring is k and the relative separable
closure is k. Taking ψ to be a nonidentity automorphism (for example complex conjugation
when k = ℂ) changes the geometric point and violates the claimed factorization at the
identity neighbourhood. A characterization hypothesis is missing. This declaration and
its importing residue construction are not used in this delivery. No unheld module was
adapted: none of this delivery's interface changes forces an adaptation.

## New nodes

`lem-weil-pbc-strict-henselization-scheme-functoriality` records the proved map of strict
henselization schemes over g, with the complete cone-extension and pullback proof.
It lives in `StrictHenselizationSchemeFunctoriality.lean` and introduces no hole.

`lem-weil-pbc-strict-henselization-closed-fiber` records the unique distinguished fibre
in one local affine presentation. It lives in `StrictHenselizationClosedFiber.lean`
and is the only new unfinished theorem. Its proof plan names the existing chart-to-triple
comparison and strict-henselization triple colimit properties. The statement was checked
on field presentations (closed point zero), on generic geometric points (the fibre is
still a field), and on nonclosed geometric points in a nonlocal base. The singleton
fibre is a property of the structural map, not a claim that its point is closed in S.

There are no change records because no existing interface or statement was changed.

## Second reading by P1

1. Compared the existing module against the repository with `diff -u`: its sole
   declaration's signature and visibility are byte for byte unchanged. No existing
   definition or other module is changed; no change record is necessary. Restored
   the original docstring, preserving the existing declaration's documentation.
2. Compiled all three modules locally without errors or warnings. The only direct
   hole is `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint`.
   No forbidden declaration or hollow definition occurs. A scratch `#print axioms`
   check reports only propext, Classical.choice and Quot.sound for
   `AlgebraicGeometry.Scheme.exists_strictHenselizationSchemeMap`; the item and the
   fibre lemma also report sorryAx. The delivery tool additionally probes every
   constant, including private helpers. Data in the pointed pullback is constructed;
   the chosen limit cones are characterized by their universal properties.
3. Read the new fibre statement and its complete docstring proof, the two existing
   triple-comparison declarations, and the local-structure proof. Stacks
   [04HX](https://stacks.math.columbia.edu/tag/04HX),
   [04GW](https://stacks.math.columbia.edu/tag/04GW) and
   [04GP](https://stacks.math.columbia.edu/tag/04GP) support the colimit identification,
   maximal ideal and quotient argument. The statement is true for a field, for a
   generic geometric point, and for a point not closed in S; it asserts a singleton
   fibre, not closedness in S. An arbitrary affine isomorphism preserves the unique
   closed point. New leanfinder search for the distinguished fibre and loogle search
   for comap/closedPoint, together with repository searches for fibre and closed-point
   APIs, found no duplicate that proves this assertion. The map theorem and the fibre
   theorem are distinct strict parts of the original argument, not a restatement.
4. Read the proof from the item downward: Spec.preimage, the structural square and
   Mathlib's closed-point criterion are a direct reduction. Reviewed the extended
   cone, Gamma-Spec transport and concrete pointed pullback. The fibre comparison
   still needs structural compatibility of the chart/colimit isomorphism; it is not
   a hole that closes by applying the existing local-structure theorem alone.
   Removed redundant explicit imports of Mathlib.CategoryTheory.Limits.Final and
   Mathlib.CategoryTheory.MorphismProperty.OverAdjunction from the new map module,
   and Mathlib.RingTheory.Spectrum.Prime.Topology from the new fibre module; each
   module still compiles because the necessary APIs are already publicly imported
   by StrictHenselizationStructuralMap. No original module or node is pruned: both
   old direct dependencies remain used transitively. Read sk-thm-p1.json, including
   realized; none of its statement or step nodes is bypassed or changed.
5. Compared the three node records with their declarations and proofs. Existing
   statement and Lean signature records agree with the unchanged signature; new
   signatures agree verbatim with the Lean. proof_deps equals the union of uses,
   proof_origin describes the actual reductions, and new nodes carry their source,
   searches, blueprint ancestry and creation records. The fibre node records its
   remaining triple-comparison route. Verdict: deliverable decomposition, one
   original hole closed and one simpler hole added, with the scheme map fully proved.

Second reading changed only the restored existing docstring, the three redundant
imports of new modules, and this report. No proof or statement repair was needed.
