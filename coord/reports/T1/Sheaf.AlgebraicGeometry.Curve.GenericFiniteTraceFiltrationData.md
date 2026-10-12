## What changed

The signature of `AlgebraicGeometry.IsConnectedCurve.exists_generic_finite_trace_filtration_data`
is unchanged. Its proof now obtains coarse geometric/trace data, refines each chain, and
postcomposes the original cohomology injection with the pushed-forward endpoint isomorphisms.
Injectivity is proved by applying the inverse cohomology maps componentwise.

Added `GenericPrimeCoarseFiltrationRefinement`, whose theorem
`AlgebraicGeometry.IsConnectedCurve.exists_prime_filtration_of_coarse` is fully proved.
It uses the already proved source-library `ObjectProperty.filtrationClosure_iff`, closure under
extensions, and Mathlib `prop_biprod`. Induction on the binary-sum dimension handles trivial
finite vector spaces; induction on the coarse chain handles the successive extensions.
The extracted finite chain is extended to natural indices using `min`. This closes the
basis-flag refinement portion of the original plan without introducing a hole for it.

Added `GenericFiniteCoarseTraceFiltrationData` for the remaining Galois/Sylow/trace construction.
Its quotients may be finite iterated binary direct sums of prime constants, rather than
rank-one prime constants. All seven original proof-dependency imports move to this module.
The item's only proof imports are the two new modules. The DAG now records this factorization.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.IsConnectedCurve.exists_generic_finite_trace_filtration_data`
(node `lem-sc-generic-finite-trace-filtration-data`).

Fully proved the new refinement theorem:
`AlgebraicGeometry.IsConnectedCurve.exists_prime_filtration_of_coarse`
(node `lem-sc-generic-prime-coarse-filtration-refinement`). It has no direct or imported hole
in its proof route through the source-library extension-closure lemmas.

Added one named hole, whose proof is exactly `:= by sorry`:
`AlgebraicGeometry.IsConnectedCurve.exists_generic_finite_coarse_trace_filtration_data`
(node `lem-sc-generic-finite-coarse-trace-filtration-data`). Its docstring contains the complete
remaining construction. This is a decomposition (one hole closed, one added), with a fully
proved refinement and transport argument, not a complete proof of the underlying trace theorem.

All three modules compile locally without warnings. The refinement proof covers empty chains
and zero-dimensional quotients through its zero constructor; the parent proof allows the empty
family of curves without imposing nonemptiness.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
- `Sheaf.RepresentationTheory.SylowModuleFiltration`
- `Sheaf.FieldTheory.OpenSubgroupFixedField`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTrace`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `WeilConjectures.SixFunctors.Finite.GlobalSections`
- `WeilConjectures.SixFunctors.Finite.Exact`

These remain dependencies of the coarse construction, so none is globally pruned. Their node
IDs likewise move from the item's immediate proof dependencies to the coarse construction.
No unit-level route is bypassed, and no whole module is claimed to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement or unit route was found. The Sylow theorem
supplies finite trivial prime-field vector-space quotients without a rank bound. The original
plan's basis refinement is therefore a genuine additional step; it is now implemented through
the proved generic extension-closure API. LeanSearch returned Internal Server Error; LeanFinder
and local searches supplied the other checks. The blueprint source path cited by the existing
node is not present in this machine's literature directory; the numbered proof and source
attribution supplied by that node were used for the decomposition.

## New nodes

`lem-sc-generic-finite-coarse-trace-filtration-data`:
`lean/Sheaf/AlgebraicGeometry/Curve/GenericFiniteCoarseTraceFiltrationData.lean` contains the
remaining coarse construction. It retains every geometric, finite-stalk, and trace hypothesis;
only the rank-one refinement has been removed from its obligation.

`lem-sc-generic-prime-coarse-filtration-refinement`:
`lean/Sheaf/AlgebraicGeometry/Curve/GenericPrimeCoarseFiltrationRefinement.lean` contains the
fully proved categorical refinement, valid for arbitrary schemes and independent of trace,
normalization, finite geometric stalks, and curves. No change record is needed: existing
signatures, definitions, and public imports are unchanged.

## Second reading by T1

1. Compared the entire existing module with the repository using `diff -u`. The only
   changes are its private proof imports and the body of
   `exists_generic_finite_trace_filtration_data`; its signature, docstring, definitions
   (there are none), and public imports are byte-for-byte unchanged. No change record
   is required. Verdict: pass.
2. Compiled all three modules in import order using `lcompile.py --all`, without errors
   or warnings. Scratch copies with `#print axioms` show exactly `propext`,
   `Classical.choice`, and `Quot.sound` for `exists_prime_filtration_of_coarse`; the coarse
   theorem and parent additionally show `sorryAx`. The only direct sorry is the reported
   coarse theorem, with a full construction in its docstring. No forbidden declarations,
   hollow definitions, or global data selected from a mere existence theorem occur.
   The parent chooses witnesses locally within a proof of a proposition. Verdict: pass
   as a decomposition, not an axiom-free proof of the trace theorem.
3. Read the coarse and refinement statements against their Lean signatures and the
   existing trace node's source attribution (blueprint affine-generic-second paragraphs
   1--2). The coarse construction retains all geometric, torsion, finite-stalk, model,
   and injectivity clauses, but omits basis-flag refinement; its obligation is strictly
   a part of the original argument. It is not an unchanged statement under a new name.
   Read the actual Sylow, stalk-equivalence, fixed-field, trace-degree, finite exactness,
   and finite cohomology interfaces. Their role is consistent with the remaining sketch.
   The source blueprint file is absent locally, so no claim of rereading that unavailable
   text is made. Refinement works for arbitrary schemes: induction on the direct-sum
   dimension and then the coarse length uses extension closure, and canonical cokernels
   give short exact complexes. Checked n=0, d=0, varying primes, and empty Fin r:
   none needs a nonzero quotient or a nonempty family. Independent LeanFinder search
   for finite-module restriction/transfer returned Hilbert 90 and group-cohomology
   functoriality, not this geometric assertion. Loogle does not know the upstream-only
   `ObjectProperty.filtrationClosure`. Local searches of Lean, upstream Curve, upstream
   ObjectProperty/Extensions, and the DAG found the proved extension-closure tools but
   no duplicate of either new statement. Verdict: pass; the remaining construction
   cannot be closed in a few minutes using those interfaces.
4. Read the refinement proof top-down and the upstream `filtrationClosure_iff` and its
   extension-closure instance. This uses the proved categorical API directly rather
   than adding a hole for basis flags. Endpoint transport postcomposes with H.map of
   the pushed-forward isomorphism; applying H.map of its inverse reduces equality to
   the original injection. The proof imports of the parent are precisely its two used
   helpers; refinement's extension API is a private import. All seven former immediate
   proof-dependency nodes remain under the coarse node, as the report explains; none
   is claimed globally pruned. `dag/units/sk-prop-cd-affine.json` has unchanged `realized`
   lists (all empty), and this decomposition preserves the finite-module/trace route
   of the item's plan. Verdict: pass.
5. Compared the parent's new three DAG steps with its actual Lean proof, and the two
   new nodes with their signatures, proof steps, dependencies, source, origin, creation,
   blueprint, chapter, unit, and search records. The refinement's steps use proved
   upstream categorical results, with no open proof dependency. The coarse node retains
   all seven original proof dependencies. Found one inaccurate phrase in its last step:
   it said prime-constant quotients rather than finite sums of prime constants. Repaired
   that phrase and made the refinement's upstream API references explicit. Verdict:
   pass after these repairs.

Second reading changed documentation only: added source and blueprint citations to both
new module headers, corrected the coarse node's quotient description, clarified proved
upstream API references in the refinement node, and removed trailing whitespace from the
parent proof. No signature, proof term, or import changed. One original direct hole is
closed and one new direct hole added (net zero); the added categorical refinement is
fully proved. No whole module is pruned.
