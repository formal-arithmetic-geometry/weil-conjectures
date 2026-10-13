## What changed

Proved `AlgebraicGeometry.finiteLocallyFree_restrict_tilde_of_principalOpen_projective`
without changing its statement or existing docstring. Added two private proved helpers:
`sectionsLocalizationEquiv` constructs the linear localization comparison for principal-chart
sections; `exists_free_neighborhood_of_projective_sections` applies the finite standard free
cover and the existing source-library free-restriction theorem. The main proof factors the
charts through U, composes the free neighbourhood maps, proves they cover U, and transports
finite local freeness along `overFunctorEquiv`. Added proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`. Updated the existing node's proof,
proof dependencies and proof origin. No definitions, public signatures or other modules changed.
Single-file compilation succeeds in about 14 seconds. The cover is indexed by points of U,
so empty U works without a nonemptiness assumption; zero modules use the finite empty basis.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.finiteLocallyFree_restrict_tilde_of_principalOpen_projective`
(node `lem-sc-principal-open-finite-projective-tilde`). Holes closed: 1. Holes added: 0.
No `sorry` remains in any delivered module. Both private helpers are completely proved.
This is a proof, not a decomposition.

## No longer needed

Removed proof-only import `Sheaf.AlgebraicGeometry.TildePrincipalLocalizationTransport`.
Node `lem-weil-pbc-tilde-principal-localization-transport` is not needed by this proof: its
stronger comparison along arbitrary affine isomorphisms is replaced by a directly proved
linear comparison on the canonical principal chart. Its module may remain needed elsewhere.
The finite standard free cover dependency is retained. All original public imports are
retained because this delivery preserves the existing public interface.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error found. The DAG's first dependency supplied more
transport data than needed. The proved source library already supplies the free-restriction
and covering criteria needed after the algebraic standard free cover. The unit realization
record is unchanged and no unit statement or step is bypassed.

## Second reading by V1

1. Compared the delivered module with the repository version. The public theorem statement,
   docstring, and existing declarations are unchanged byte for byte; only the proof-only import
   and proof body differ, as described above. Verdict: pass.
2. Compiled the module with `lcompile.py`; there are no errors, warnings, `sorry`s, forbidden
   declarations, or hollow definitions. Axioms of the target are exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and private helpers against the imported library and searched for
   existing localization/free-cover results. The helpers are strictly intermediate facts and no
   split-off statements were added. Verdict: pass.
4. The proof uses the source-library free-cover and finite-local-freeness criteria, while directly
   proving only the needed principal-chart linear equivalence. The obsolete transport import and
   dependency are pruned; the unit route and realization are kept. Verdict: pass.
5. The node's proof steps and `proof_deps` agree with the Lean proof, with the standard-free-cover
   node as its sole DAG dependency; no new nodes or change records are required. Verdict: pass.

Second reading changed only this report by adding the review record. No Lean or node repairs
were needed. The proof's arbitrary choices occur within theorem proofs, not in definitions.
