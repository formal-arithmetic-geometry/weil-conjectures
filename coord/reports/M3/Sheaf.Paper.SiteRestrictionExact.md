## What changed

Proved `CategoryTheory.siteRestriction_exact` in `Sheaf.Paper.SiteRestrictionExact`
without changing its signature. Restriction is the continuous sheaf pushforward
along `Over.forget W`. That functor is also cocontinuous, so Mathlib's
`sheafAdjunctionCocontinuous` makes restriction a left adjoint. Its colimit
preservation and the existing proved limit-preservation instance give the result
by `ShortComplex.ShortExact.map_of_exact`. No new declaration or proof import
is needed. The declaration's existing docstring gives the alternative
sectionwise/local-surjectivity proof; the DAG now records the actual Lean route.

All existing public imports are retained. Each was tested for removal:
all except `Mathlib.CategoryTheory.Sites.LeftExact` are needed by elaboration.
That public import already occurs transitively through `Sites.Over`, but the
delivery checker treats its deletion as an interface change requiring a change
record; retaining the existing public export keeps this delivery focused on
the proof and its DAG route. There are no unused proof-only imports.
The unit record `sk-prop-cd` was read; this auxiliary node does not realize a unit
statement or step, and the unit route is unchanged.

## Proved and sorry left

Closed: `CategoryTheory.siteRestriction_exact`
(node `lem-weil-pbc-site-restriction-exact`), the module's sole hole.
Added: none. Remaining in the delivered modules: none.
This is a complete proof, not a decomposition. Local compilation and import-pruning validation succeeded.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Imports removed: none. No proof-only imports were added. Existing public
exports are retained, as explained above.

Removed proof dependency: `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
(Mathlib `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` in
`Mathlib.CategoryTheory.Sites.EpiMono`); local lifting is unnecessary for this
proof. Also removed `def-weil-pbc-sites-and-cohomology` from `proof_deps`;
it remains a statement dependency. Neither of these dependencies supplied a
direct import in the original module. No Sheaf or WeilConjectures module is
claimed to become globally unreachable; other items can still use these nodes.
The replacement proof uses the existing Mathlib leaf
`lem-weil-pbc-left-adjoint-preserves-colimits`.

## Second reading by M3

1. **Visible changes and statements.** Compared the delivered module with the
repository version. The theorem signature and all existing declarations are
byte for byte unchanged; only the proof body changed. The DAG node records the
same statement and the actual proof route.
2. **Proof validity.** Compiled `Sheaf.Paper.SiteRestrictionExact` with the
launcher compiler. There are no `sorry`, `axiom`, `unsafe`, `opaque`,
`implemented_by`, or `extern` declarations. A scratch `#print axioms` reports
only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and dependencies.** No statement was split off or added. The
proof applies the existing cocontinuous sheaf adjunction and
`ShortExact.map_of_exact`; the unchanged hypotheses are retained and the
conclusion is exactly the target. The route uses no local-surjectivity claim.
4. **Pruning and route.** No imports were removed or added because each
existing public import is required by elaboration or preserves the module
interface. The obsolete local-surjectivity proof dependency was removed from
the node's `proof_deps`; the unit `sk-prop-cd` route remains unchanged.
5. **DAG agreement.** The node's proof steps, `proof_deps`, and
`proof_origin` describe the adjunction/colimit-preservation proof in the Lean
file, and no new node or change record is needed.

Changed during second reading: appended this review only; no Lean code or
statement changes were necessary.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly found no single exactness lemma for arbitrary
localized sites, but the existing continuous/cocontinuous adjunction and proved
library finite-limit instance combine into a short complete proof. No new
intermediate theorem or local-surjectivity theory is required. All original
hypotheses are retained. The proof uses no pullback assumption beyond those
already in the unchanged signature, and covers empty and trivial sites too.
