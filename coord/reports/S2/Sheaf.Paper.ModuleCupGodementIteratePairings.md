## What changed
Replaced the rejected arbitrary-family collapse reduction with two structured intermediate
modules. `ModuleCupGodementIteratePairingsCanonical` states the coordinatewise beta datum and
its recursively generated family; `ModuleCupGodementIteratePairingsCanonicalCollapse` states
collapse compatibility for that recursively generated family. The target imports the latter
and combines the two intermediate results. The target proof has no `sorry`. This is a decomposition: one upper hole closed and two
lower holes added, not an unconditional proof. Beta includes naturality, germ-unit and
multiplication laws, so the collapse lemma does not assume a merely coface-compatible family.

## Proved and sorry left
Hole closed (1): `moduleCup_godement_iterate_pairings`. Holes added (2):
`moduleCup_godement_iterate_pairings_canonical_exists` and
`moduleCup_godement_iterate_pairings_collapse_of_canonical`. Net closed minus added: -1.
This is a decomposition, not an unconditional proof.

The target declaration `moduleCup_godement_iterate_pairings` is reduced to the two named
intermediate declarations. The new declarations
`moduleCup_godement_iterate_pairings_canonical_exists` and
`moduleCup_godement_iterate_pairings_collapse_of_canonical` remain `sorry`, with nodes
`new-module-cup-godement-iterate-pairings-canonical-exists` and
`new-module-cup-godement-iterate-pairings-canonical-collapse`.

## No longer needed
No existing library import or module is pruned. The old direct proof dependencies
`def-sc-module-cup-godement-model` and `def-sc-module-cup-godement-codegeneracies`
are replaced in the target node's `proof_deps` by the two intermediate nodes. They
remain statement dependencies and are used by the intermediate proofs, so neither
is globally unnecessary. The rejected scratch modules
`ModuleCupGodementIteratePairingsInsertions` and `ModuleCupGodementIteratePairingsCollapse`
are excluded from this delivery; that is not pruning a module of the library.

## Where the brief, the DAG or earlier work was wrong
The earlier collapse helper quantified over an arbitrary family satisfying only coface
compatibility; that implication is false. The replacement hypotheses encode the recursive
coordinatewise construction used by the source proof.

## New nodes
`new-module-cup-godement-iterate-pairings-canonical-exists` and
`new-module-cup-godement-iterate-pairings-canonical-collapse` are added as the two strictly
smaller construction and compatibility steps described above.

## Second reading by S2

1. Compared the delivered target with the repository using `diff -u`. Its existing
   signature and docstring are byte-for-byte unchanged; the only Lean changes are
   a plain proof import and the proof body. The two other modules are new. No
   existing definition or signature changes; no change record or adaptation needed.
2. Compiled all three modules in dependency order with `lcompile.py --all`.
   Only the two reported public named theorems contain `sorry`; the structure is
   ordinary data with law fields, and no definition chooses data from an unproved
   existence theorem. A scratch `#print axioms` check of all three theorems showed
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The scratch copy
   was removed. The target uses both intermediate results with the very same beta
   and p, and passes their exact recursion and initial-value hypotheses.
3. Read Banerjee arXiv:1004.1491, section 1.1.4, the paragraph defining the
   cosimplicial cup pairing, and Stacks Tag 0FKR's adjunction construction.
   The coordinatewise module-sheaf construction is an adaptation of that argument,
   not a quotation of a theorem about the present concrete Lean definitions.
   For the existence lemma, on an open U the x-coordinate (x in U) is the tensor
   of the two x-coordinates; the stalk tensor comparison gives its target.
   Restriction preserves this formula; germ representatives prove the unit and
   multiplication identities. At n=0 the unit insertion identity is beta.unit
   followed by T(id)=id. For higher n and index zero, beta.unit followed by unit
   naturality gives the assertion; successor indices use beta.naturality and
   T of the induction hypothesis. For collapse at n=0, substitution gives
   (mu tensor mu);beta;T(p0) on one side and
   beta(TF,TG);T(beta);T(T(p0));mu on the other: beta.multiply and mu naturality
   identify them. For general n index zero is the same calculation at T^nF,T^nG;
   successor indices use beta.naturality and T of the lower collapse identity.
   Thus the new statements separate construction/unit compatibility from
   multiplication compatibility; neither restates the whole target. The collapse
   proof does not need beta.unit (corrected the contrary docstring claim).
   Checked empty X (all maps unique), zero F or G (zero tensors), and a one-point
   scheme (coordinate pairing is ordinary stalk tensoring). No nonempty or
   nonzero assumption is used. Searched Mathlib again via leanfinder for
   "lax monoidal monad iterated multiplication tensor compatibility", Loogle for
   `CategoryTheory.Functor.LaxMonoidal.μ_natural`, and grep for
   `Godement|godement|monoidalMonad|MonoidalMonad`. Only generic monad and lax
   monoidal identities were found; the concrete Godement construction is not
   packaged as a functor/monad to which they apply directly. Also searched both
   Lean roots and the DAG for tensor/skyscraper pairings and the new names: no
   duplicate of either intermediate theorem. The elementary-looking collapse
   induction additionally needs concrete functoriality and multiplication
   naturality, so it cannot be closed by a short application of those generic APIs.
4. The target assembles the construction and its collapse compatibility directly.
   The target's proof-only import is plain `import`; the new public imports supply
   the concrete objects, maps, tensor structure and beta type used in signatures.
   No existing public import is removed. Checked `dag/units/sk-prop-av-cube.json`:
   its realized statement and step lists are empty, and this reduction retains the
   original node below that unit; no realized unit step or chapter route is bypassed.
   Corrected the pruning report: excluded rejected scratch files are not library
   modules pruned, and both old definition dependencies remain needed downstream.
5. Compared each Lean theorem statement with its node's `lean.statement` and each
   proof with `proof`, `proof_deps`, and `proof_origin`. The target has precisely
   the two applied intermediate dependencies. Both new nodes cite the concrete
   model and codegeneracy definitions used in their constructions. Repaired their
   informal statements to self-contained TeX, filled blueprint ancestor/place and
   `same_as`, and appended the searches actually run in this reading. Added a
   source/blueprint docstring for the beta structure and corrected the collapse
   docstring and node proof to identify the two beta laws actually used.

Holes closed: `moduleCup_godement_iterate_pairings` (1). Holes added:
`moduleCup_godement_iterate_pairings_canonical_exists` and
`moduleCup_godement_iterate_pairings_collapse_of_canonical` (2). This is a
one-to-two decomposition, net -1 closed hole before global pruning, not an
unconditional proof or a claim of positive sorry-ledger progress.
