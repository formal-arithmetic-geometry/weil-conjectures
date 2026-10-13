## What changed

The unchanged target theorem
`AlgebraicGeometry.Scheme.nonempty_punctured_h_addEquiv_injective_quotient`
now has a complete Lean proof. It composes the cohomology comparison with the
homology image of an isomorphism of complexes.

Four new modules make the original three-step plan explicit:

- `PuncturedSectionsComplex` constructs the sections functor, complex and
  restriction cochain map from Mathlib's tilde and evaluation functors.
- `PuncturedInjectiveRestrictionExact` states kernel equality and surjectivity
  of restriction for one injective module.
- `PuncturedSectionsTorsionQuotient` proves the chain-level quotient comparison
  from that restriction lemma. It constructs the short exact sequence degreewise,
  uses Mathlib's degreewise criterion, and identifies the two cokernels by
  uniqueness of colimits.
- `PuncturedFlasqueResolutionCohomology` states the cohomology computation for
  any open in a Noetherian affine scheme.

The existing target module gains only proof imports. Its public imports and
signature are unchanged. All five modules compile individually via lcompile.py.
Explicit ring-category arguments avoid expensive unification at tilde.toOpen.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.nonempty_punctured_h_addEquiv_injective_quotient`
(node `lem-sbc-punctured-injective-quotient-cohomology`).

Also proved:
`AlgebraicGeometry.Scheme.nonempty_injective_quotient_iso_punctured_sections`
(node `lem-sbc-punctured-sections-torsion-quotient`). The sections constructions
and their zero-map/naturality proofs contain no holes.

Added exactly two named theorem holes, each in its own new module:

- `AlgebraicGeometry.Scheme.injective_punctured_restriction_exact`
  (node `lem-sbc-punctured-injective-restriction-exact`).
- `AlgebraicGeometry.Scheme.nonempty_open_h_addEquiv_injective_sections`
  (node `lem-sbc-punctured-flasque-resolution-cohomology`).

This is a decomposition, not an unconditional proof: one upper hole closed and
two lower holes added, giving net minus one hole. The chain-level assembly and
homology composition are complete. No data are selected from an unproved mere
existence theorem.

## No longer needed

No original import, dependency definition, node or module is pruned. The original
proof dependencies remain needed for the statements or new intermediate steps;
the item's proof_deps now records its two actual comparison lemmas.

The unused and invalid zero_addEquiv helper and its unlanded auxiliary node from
the earlier sandbox attempt were removed. The rejected restatement comparison
was discarded; it is absent from the final delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the entire target hole in place and added an invalid
zero-group helper. The absence of a direct existing comparison is not an obstacle
to this stage: the geometric computation has now been decomposed into the two
strictly separate tasks above, with its chain-level glue proved in Lean.

The original node's three prose steps named only definitions. The revised DAG
records the concrete sections complex, the single-module restriction calculation,
the proved chain-level comparison, and the independent acyclic-resolution
comparison. The unit route is preserved. The new cohomology lemma needs neither
locality nor the puncture hypothesis; the restriction lemma has no resolution or
cohomology degree. These are not restatements of the target.

Read Stacks Tags 09T2, 0A6T and 0BK0 online. The new statements were checked on
W empty (including m=0 and Artinian local rings), and the cohomology comparison
also on W equal to the whole affine scheme and on degree zero. No target or
existing definition was changed. Existing generic flasque acyclicity declarations
do not provide either complete comparison; searches are recorded on the new nodes.

## New nodes

`def-sbc-punctured-sections-complex`: concrete sections functor, complex and
restriction morphism; module `PuncturedSectionsComplex`.

`lem-sbc-punctured-injective-restriction-exact`: kernel and surjectivity for one
injective module; module `PuncturedInjectiveRestrictionExact`; left sorry.

`lem-sbc-punctured-sections-torsion-quotient`: isomorphism of complexes obtained
from the degreewise short exact sequences; module `PuncturedSectionsTorsionQuotient`;
proved from the single-module restriction lemma.

`lem-sbc-punctured-flasque-resolution-cohomology`: cohomology from the concrete
sections complex on any open; module `PuncturedFlasqueResolutionCohomology`;
left sorry.

All four nodes inherit the original chapter and unit. Their statements introduce
all objects, their docstrings give full proofs in words, and their Mathlib searches
record LeanSearch's service failure, LeanFinder/Loogle results and source grep.
No interface change to an existing module requires a change record or adaptation.

## Second reading by T4

1. Compared the delivered target module with the repository version: the theorem
signature and all existing declarations are byte-for-byte unchanged; only proof
imports and the target proof were added. The four auxiliary modules and four node
files are new split-offs declared in this report.
2. Compiled all five modules with lcompile.py. There are no forbidden declarations,
no hollow definitions, and the only remaining `sorry`s are the two named split-off
theorems listed above. The target theorem has a complete proof; its construction
uses only the allowed comparison isomorphisms and no extra axioms.
3. Read each split-off statement and its docstring against the cited Stacks tags.
The restriction theorem is the exact kernel/surjectivity calculation, the sections
complex is a concrete degreewise construction, the quotient theorem is the needed
chain-level comparison, and the flasque-resolution theorem is the independent
cohomology comparison. None restates the target or weakens it; edge cases m = 0,
empty W, degree zero, and W equal to the whole affine scheme are addressed.
4. The target DAG proof and proof_deps now match the two declarations used in its
Lean proof. The auxiliary node proof_deps match their imports and theorem bodies;
the unit route remains through the explicit sections complex, restriction exactness,
chain quotient, and resolution comparison. No unused original import was removed.
5. No shorter existing Mathlib or library theorem supplies either geometric
comparison. Searches recorded in the nodes found only general injective-resolution,
primary-component, and cokernel APIs, so the four explicit nodes are necessary.

Changed only the target proof and imports, added the four auxiliary modules and
their DAG nodes, and recorded the target proof-dependency pruning. No existing
definition or target statement was changed.
