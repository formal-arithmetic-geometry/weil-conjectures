## What changed

Reduced `CategoryTheory.cohomology_colimit_sites_exact_ladder` to two strictly separate
construction steps, retaining its entire signature and docstring. The first new module
constructs normalized coefficients, injective middle terms, cokernels and a short exact
colimit sequence. The second constructs the cohomology diagrams, maps, stage properties
and squares from that sequence. It supplies formulas identifying the target maps with
Yoneda products, but does not assume target kernel-image exactness.

The main module proves that last assertion using Mathlib's
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`. It transports a class killed by
β into the cokernel Ext group, obtains a preimage in the middle Ext group, transports
that preimage back into b.pt, and verifies its image using the supplied α₀ formula.
The witness construction and cohomology assembly are distinct parts of the original
DAG plan, not renamed copies of the target.

The original continuation contains proof binders unused in its final proposition;
its unused-variable lint is disabled locally without changing any binder. A local
heartbeat allowance covers elaboration of its dependent sheaf-pullback endpoints.
No definitions, existing statements, public imports, or other modules were changed.

## Proved and sorry left

Closed: `CategoryTheory.cohomology_colimit_sites_exact_ladder`
(node `lem-weil-pbc-colimit-sites-exact-ladder`). This is a decomposition, not a
sorry-free mathematical proof: one original hole was closed and two holes were added.

Added and still sorry:

- `CategoryTheory.cohomology_colimit_sites_short_exact_systems`
  (`lem-weil-pbc-colimit-sites-short-exact-systems`).
- `CategoryTheory.cohomology_colimit_sites_boundary_diagrams`
  (`lem-weil-pbc-colimit-sites-boundary-diagrams`).

There are no remaining sorries in the item's module and no other added holes.
Both added holes are named public theorems in separate modules, each with its source,
full proof sketch and DAG node. The two additional Mathlib leaf nodes add no holes.

Edge cases checked: n=0 still uses positive degree n+1 for stage surjectivity;
zero coefficient systems yield zero sequences; a filtered category need not be a
poset. In particular the original φ need not satisfy an identity law. The explicit
normalized system As and projection pA are therefore essential. Only its canonical
inverse images and the supplied degree n+1 stage groups are required to be unchanged;
no degree-zero isomorphism Fs→As is assumed. Identity laws for the new middle and
cokernel cohomology transitions are explicit construction conclusions.

## No longer needed

Removed direct proof imports:

- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `Sheaf.Paper.ColimitSitesInjectiveSystem`.

The first, fourth and fifth remain planned dependencies of the short-exact-system
construction node; their mathematical work is not pruned. The generic right-derived
long exact sequence and injective-vanishing nodes
`lem-weil-pbc-derived-functor-long-exact` and
`lem-weil-pbc-derived-functor-injective-vanishing` are replaced on this route by the
existing Ext API recorded in the two new Mathlib leaves. Their modules are
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` and
`Mathlib.CategoryTheory.Abelian.RightDerived`. Public imports of
`Sheaf.CategoryTheory.SiteCohomologyPullback` and
`Sheaf.CategoryTheory.ColimitSites` stay. The former still reaches some removed
imports transitively; no claim is made that those modules leave the global closure.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No change to the original statement or proof route was necessary. The DAG's
normalization sentence is substantial: using Fs itself as the first term of a
normalized stage short exact sequence would incorrectly force identity actions.
The new interface exposes As, compatible projections and the exact comparison
isomorphisms rather than hiding that issue.

The generic right-derived declarations in the original plan require a bridge to
Sheaf.H', which is defined by Ext. Mathlib already supplies the needed Ext exactness
and positive-degree injective vanishing directly; these avoid that bridge.

The local checkout has no copies of the cited Stacks TeX documents. The source was
read from the official Stacks pages for Tags 0EXZ, 09YP and 0739. The blueprint ancestor
query returned None for this already-split item; new nodes preserve the ancestor
recorded in its existing blueprint.from instead. All searches recorded in the nodes
were actually run with msearch.py. There are no forced adaptations.

## New nodes

`lem-weil-pbc-colimit-sites-short-exact-systems`: normalization, compatible embedding,
cokernels and their short exact colimit; new module
`Sheaf.CategoryTheory.CohomologyColimitSitesShortExactSystems`, one hole.

`lem-weil-pbc-colimit-sites-boundary-diagrams`: assembly of stage cohomology diagrams
and comparison squares from fixed normalized short exact systems; new module
`Sheaf.CategoryTheory.CohomologyColimitSitesBoundaryDiagrams`, one hole.

`lem-weil-pbc-ext-covariant-boundary-exact`: attaches Mathlib's existing
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`, read at
Ext/ExactSequences.lean:159. No new Lean declaration or hole.

`lem-weil-pbc-ext-injective-positive-vanishing`: attaches Mathlib's existing
`CategoryTheory.Abelian.Ext.subsingleton_of_injective`, read at
Ext/EnoughInjectives.lean:110. No new Lean declaration or hole.

No change records are needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered exact-ladder module against the repository version. Existing declaration signatures and definitions are unchanged byte for byte; only proof imports, local options, and proof bodies differ. Verdict: pass.
2. Compiled all three delivered Lean modules with `lcompile.py`; the modules compile without errors. The exact-ladder target has no remaining `sorry`, and the only remaining holes are the two named split-off public theorems listed above. No forbidden declarations or hollow definitions were found. Verdict: pass.
3. Checked both split-off statements and their docstrings and DAG nodes. They are strictly smaller construction and assembly interfaces needed by the target, with sources and explicit proof sketches; they do not restate the target. Edge cases in the report remain valid. Verdict: pass.
4. Reviewed imports and proof route. Removed imports are recorded above; the proof uses the Ext exactness API and preserves the unit route. Verdict: pass.
5. Checked the DAG proof/proof_deps/proof_origin against the delivered proof and verified the new nodes contain the required Lean records and metadata. Verdict: pass.

Changed nothing during second reading; the delivery is ready for dry-run and delivery.

## Second reading by K2

1. I compared the delivered exact-ladder module with the repository version using `diff`.
   Existing declaration signatures and definitions are unchanged byte for byte; the changes
   are proof imports, local options, and proof bodies. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`. Compilation succeeds with
   no errors. The target has no remaining `sorry`; the only holes are the two named split-off
   public theorems listed above. No forbidden declarations or hollow definitions occur. Verdict:
   pass.

3. I checked both split-off statements, their docstrings, and their DAG nodes. Each is a needed
   and strictly smaller construction or assembly interface, with matching source, proof sketch,
   and metadata; neither restates the target. The stated edge cases remain consistent. Verdict:
   pass.

4. I reviewed the proof route and imports. The proof uses the existing Ext exactness API for the
   final kernel-image step, removes the listed unused imports, and keeps the realized unit route.
   Verdict: pass.

5. I checked the DAG `proof`, `proof_deps`, and `proof_origin` against the Lean proof and checked
   the new nodes' Lean records and required metadata. They agree. Verdict: pass.

I changed only this report by recording this second reading; no Lean or DAG files required repair.
