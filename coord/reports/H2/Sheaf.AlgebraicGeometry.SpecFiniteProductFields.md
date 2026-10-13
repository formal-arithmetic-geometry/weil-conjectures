## What changed

Completed and checked the earlier sandbox proof of
`AlgebraicGeometry.spec_finite_product_fields` in
`Sheaf.AlgebraicGeometry.SpecFiniteProductFields`. The existing theorem signature,
visibility are unchanged. The second reader corrected the imports as recorded below. The proof uses Mathlib's classification and
homeomorphism for the spectrum of a finite product, singleton spectra of fields,
and the existing instance that the spectrum of a projection is an open immersion.
Its final step identifies the source with the open range using
`IsOpenImmersion.isoOfRangeEq` and proves the requested factorization.

Updated the existing node's proof, proof_deps and proof_origin to describe this
route. No definitions, statements, other modules or new nodes were introduced.
The unit `sk-thm-p1` and all its realized steps are preserved: this node and the
removed localization dependency are below those steps.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.spec_finite_product_fields`
(node `lem-weil-pbc-spec-finite-product-fields`). Added 0 holes; split off 0.
There are no remaining `sorry`s in the delivered module and no dependencies on
unproved project statements. Local compilation succeeded without warnings.
The finite-product classification includes the empty product: the equivalence
with `Fin 0` yields an empty spectrum and cardinality zero, and the factor clauses
are vacuous. The proof works uniformly in the fields and their universe.

## No longer needed

Removed the redundant direct imports `Mathlib.RingTheory.Spectrum.Prime.RingHom`
and `Mathlib.RingTheory.Spectrum.Prime.Topology` (both already provided transitively).
Changed `Mathlib.AlgebraicGeometry.Limits` from public to proof-only `import`.
Added `public import Mathlib.AlgebraicGeometry.Restrict`, which supplies the
statement's open subscheme, inclusion and spectrum/open-immersion definitions.
No Sheaf or WeilConjectures proof-dependency module is needed by this proof.
Removed from this node's proof dependencies:

- `lem-weil-pbc-principal-localization-open-immersion`: use the existing Mathlib
  projection open-immersion instance instead of a separate project lemma.
- `def-weil-ring-localization-away`: the proof no longer constructs a localization
  or factors through one. Mathlib's internal localization argument is already proved.

The affine-spectrum and open-immersion definition nodes remain. These are removals
from this node's route; other users of the removed nodes may still need them.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt already contained a complete compiling Mathlib proof, but
lacked the DAG update, report and successful delivery dry run. This delivery
supplies those missing parts. The DAG's explicit localization construction is
unnecessary because Mathlib already proves the projection is an open immersion.
No mathematical statement error or forced adaptation was found.

## Second reading by H2

1. **Unchanged statements: PASS.** Compared the sole delivered Lean module with
   the repository using `diff`. The existing declaration signature, visibility,
   universe and hypotheses are byte for byte unchanged; the only edits are its
   proof and imports. No definitions or new declarations were introduced.
2. **Kernel proof: PASS.** Independently compiled the original proof and the final
   module with `lcompile.py`, without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.spec_finite_product_fields` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`. Scanned for forbidden declarations,
   attributes and `sorry`; none occur. The open is constructed as `f.opensRange`,
   and its isomorphism comes from the proved equal-range theorem, with no arbitrary
   witness chosen from an unproved existence theorem.
3. **Split statements: PASS (none).** No new statements, nodes or holes were added.
   Checked the empty-index case: the spectrum equivalence is with `Fin 0` and the
   factor assertions are vacuous; for one factor it is a singleton. Independent
   Loogle search for `"PrimeSpectrum", "Field"`, Lean Finder search for
   `finite product fields spectrum singleton factors discrete cardinality`, and
   repository searches confirm the existing Mathlib pieces used by this proof.
4. **Shortest route and pruning: PASS after import correction.** The proof already
   assembles proved Mathlib facts directly; no further reduction is necessary.
   Inspected the projection instance in `Limits`: it proves the localization route
   internally. Removed the two redundant spectrum imports and privatized the
   proof-only `Limits` import, using public `Restrict` for the statement. The report
   lists both removed old proof dependencies. Inspected `dag/units/sk-thm-p1.json`:
   neither this auxiliary node nor the removed localization nodes realizes its
   statement or steps, so no unit route is bypassed. The sole direct importer,
   `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`, compiles unchanged against the
   sandbox's compiled final module; its private import exports nothing downstream.
5. **DAG agrees: PASS.** Compared the existing node against the repository. Only
   `proof`, `proof_deps`, `proof_origin` changed, and they match classification,
   the sigma homeomorphism, cardinality/discreteness, and the projection's open
   range isomorphism. The two retained dependency nodes record the Mathlib
   spectrum and open-immersion definitions used by the statement and proof.

Second-reading changes: imports and this report only; the complete proof was kept.
The public import correction is recorded in
`coord/changes/H2-spec-finite-product-fields-imports.md`.
