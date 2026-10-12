## What changed

Replaced the first worker's two interfaces with two genuine parts of the resolution
argument, in `Sheaf.AlgebraicGeometry.EtaleZariskiDerivedSectionsAcyclicLeray` and
`Sheaf.AlgebraicGeometry.EtaleCohomologyNaturalDerivedEvaluation`.
The existing theorem `AlgebraicGeometry.Scheme.Modules.etaleZariskiNaturalAcyclicLeray`
keeps its signature byte for byte. Its proof now composes the proved natural Zariski
object-cohomology/right-derived-sections isomorphism with acyclic derived-sections
Leray and the inverse of the natural etale standard-Ext/derived-evaluation comparison.
Naturality is proved by applying injectivity of the last comparison and composing
three naturality equations. All newly introduced imports of this existing module
are proof-only. The unusedVariables linter is suppressed only for the unchanged
existing theorem, whose signature names an acyclicity proof in the family type.
No existing definition or public import changed; no change record is necessary.

## Proved and sorry left

Direct hole closed:
`AlgebraicGeometry.Scheme.Modules.etaleZariskiNaturalAcyclicLeray`
(node `lem-sc-etale-zariski-natural-acyclic-leray`).

Holes added and still open:
- `AlgebraicGeometry.Scheme.Modules.etaleZariskiDerivedSectionsAcyclicLeray`
  (node `new-etale-zariski-derived-sections-acyclic-leray`): only the natural
  comparison of the two right-derived evaluation functors on T-acyclic sheaves;
  it does not mention either Ext model.
- `AlgebraicGeometry.Scheme.Modules.etaleCohomologyNaturalDerivedEvaluation`
  (node `new-etale-cohomology-natural-derived-evaluation`): only the natural
  standard-large constant-integer Ext/derived-terminal-evaluation comparison;
  it does not involve a Zariski site, direct image, or acyclicity hypothesis.

This is a decomposition, not an axiom-clean proof. One existing direct hole is
closed and two narrower holes are added, for net minus one hole closed in the
import closure before any global pruning. The target still uses sorryAx through
these two explicitly named theorem holes. There is no definition with sorry or
with an arbitrary witness selected from an unproved existence theorem. Existential
families are eliminated only inside the theorem proof. The Zariski isomorphism is
selected from an already proved theorem, preserving its naturality as an isomorphism
of functors rather than selecting unrelated objectwise equivalences.

## No longer needed

Removed the following direct proof imports of the target module:
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
- `Mathlib.CategoryTheory.Abelian.Injective.Ext`
- `Sheaf.Paper.ZariskiEtaleSheafLeftExact`
- `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`

Every old proof_dep except `lem-sc-site-cohomology-right-derived-sections`
ceases to be a direct proof dependency of the target:
`lem-weil-pbc-zariski-etale-sheaf-left-exact`,
`lem-weil-pbc-site-pullback-abelian-underlying`,
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`lem-weil-pbc-site-sheaves-enough-injectives`,
`lem-weil-pbc-ext-via-injective-resolution`,
`new-sheaf-cohomology-derived-evaluation`, and
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`.
They remain needed by the resolution arguments of the new component nodes and
are retained as their planned proof dependencies, with the corresponding
proof-only imports and the shared instance imports. No library module is claimed
pruned from the complete target import closure.

Discarded the unlanded `new-acyclic-leray-equivalences` and
`new-acyclic-leray-naturality` nodes and their two modules. They are not part of
this delivery. Removed the original misleading linter-only change record.

## Where the brief, the DAG or earlier work was wrong

The first worker asserted that EVERY arbitrary family of additive equivalences
commutes with coefficient morphisms. Its proof sketch only supports a comparison
constructed from resolutions, not arbitrary equivalences. Objectwise choices of
noncentral automorphisms need not commute with endomorphisms (e.g. a sign change
on one summand and a summand swap on a nonzero doubled group). Thus the unrestricted
naturality assertion cannot justify the target. The existence interface also
concluded only True, so it imposed no condition linking its chosen family to the
claimed resolution construction. Both were removed rather than weakening the
existing target or preserving an unsupported assertion.
The old report incorrectly called the decomposition a proof and claimed the
split-off dependencies were needed to state the new interfaces. They are planned
proof dependencies; they do not occur in their signatures. This report distinguishes
the decomposition and its actual net holes explicitly.

The existing general `exists_cohomology_resolution_evaluation_natural_succ`
only states naturality for endomorphisms of one sheaf and one resolution. It
cannot be applied as the required simultaneous comparison for every F -> G.
The general objectwise derived-evaluation theorem does not supply naturality or
the target's standard large Ext model. Neither is duplicated by a restatement.
A brief attempt to close the natural standard-Ext comparison using the proved
Ext/derived-Hom theorem exposed additional universe reindexing obligations;
no partial proof or auxiliary sorry from that attempt is delivered.

## New nodes

`new-etale-zariski-derived-sections-acyclic-leray` separates the pushforward of an
acyclic injective resolution and the identity of its section complexes from Ext.
Its proof and dependency union record inverse-image exactness, preserved
injectives, enough injectives, and comparison-map homotopy. Its statement does
not require a HasExt model or even terminality of i(top).

`new-etale-cohomology-natural-derived-evaluation` separates the constant-integer
standard large Ext computation from direct-image Leray. It includes the universe
lift/unlift and cross-object naturality in its docstring proof and node. The
small-model objectwise theorem and the endomorphism resolution-evaluation theorem
were inspected; neither already states this result. Both new nodes have actual
LeanSearch, LeanFinder, Loogle and Mathlib grep logs in searches.jsonl; unavailable
services are recorded as unavailable. Repository/source searches additionally
checked derived-functor composition, rightAcyclic, ExtRightDerivedHom, and terminal
evaluation using different queries from the first worker.

## Second reading by N3

1. Compared the existing target module to the repository version. The declaration
   signature is byte for byte identical. There are no changed existing definitions,
   public imports, or additional hypotheses. Only proof imports, a scoped linter
   option, and the theorem proof changed. The discarded change record claimed an
   interface change where none existed and was removed.
2. All three delivered files compile locally through lcompile.py in import order.
   The only remaining sorry occurrences are the complete proofs of the two named
   component theorems above. No axiom, unsafe, opaque, implemented_by, extern, or
   sorry inside a definition occurs. Scratch-copy #print axioms probes for all three declarations returned exactly
   propext, Classical.choice, Quot.sound, and sorryAx; no other axioms occur.
   All three files compile without errors or warnings (2.2 s, 4.1 s, 22.7 s).
3. Rejected and removed arbitrary-equivalence naturality. Checked the replacement
   statements using the resolution arguments in their docstrings, including zero
   coefficients, n=0 (cohomological degree one), the empty scheme, identity
   coefficient morphisms, and independence of acyclicity proofs. They each remove
   an entire independent part of the target's argument and are strictly simpler.
   Neither merely renames the target. Mathlib and the upstream/library comparisons
   were searched; objectwise and endomorphism results are ingredients, not matches.
4. The shortest available proved Zariski natural isomorphism is now actually used.
   The composition and all three naturality equations are written in the target.
   The report lists every unused old direct proof_dep, distinguishes relocated
   proof plans from actual closure pruning, and does not claim pruned modules.
   `dag/units/sk-prop-cd.json` has empty realized statement and step lists; no
   realized unit node or chapter route is bypassed or changed.
5. Read all delivered nodes against the Lean signatures and proof. The target's
   proof and proof_deps describe precisely its three-way composition; the two new
   nodes have self-contained statements, sources, full resolution proof plans,
   dependency unions, search records, creation and blueprint provenance, and
   verbatim Lean signatures. The original target statement and other owned fields
   stay unchanged.

Second reading changed the two unsound/inadequate interfaces, rebuilt the proof
using the existing proved Zariski comparison, replaced their nodes with valid
component nodes, scoped the linter option, removed the misleading change record,
and corrected the report's proof count and pruning claims.
