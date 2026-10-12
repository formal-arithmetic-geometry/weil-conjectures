## What changed

Replaced the sole sorry in `lean/Sheaf/RingTheory/FiniteLocalHenselian.lean`,
`HenselianLocalRing.finite_local_henselian`, with the existing three-step DAG plan
made into Lean. Its signature is unchanged. No public imports changed. The second reading adds the proof-only import
`WeilConjectures.Mathlib.RingTheory.Idempotents` to reuse its local-ring idempotent lemma.

For a finite A-algebra C, `Module.Finite.trans` makes C finite over R. A proved
private universe adapter combines
`existsUnique_algHom_of_henselianLocalRing_etale` with
`finite_algebra_is_product_local_rings`. It follows the ULift adapter already
proved in `FiniteOverHenselianLocalProduct`, without importing that module (which
imports this item). Surjective coordinate projections make each local factor
finite over A. Mathlib's integral maximal-ideal contraction theorem shows that
the extension of A's maximal ideal is contained in each factor's maximal ideal.

The proved private helper `product_idempotent_lifting` handles any ideal in a
finite product whose coordinate images lie in the respective maximal ideals.
`Ideal.piOrderIso` makes the coordinate quotient maps jointly injective. Each
coordinate quotient is nonzero and local, so its idempotents are zero or one.
The same zero-one vector lifts, and nontriviality gives uniqueness. A quotient
ring equivalence and the product algebra equivalence transport the lift back to
C. The existing idempotent/simple-root equivalence and `HenselianLocalRing.TFAE`
finish the proof. The empty index set is allowed throughout; no nonzero
hypothesis on C is added.

Source read: Stacks algebra.tex, label `lemma-finite-over-henselian`, part (2),
in the locally available Stacks copy at `/home/ubuntu/c1-stacks-review/algebra.tex`.
This explicitly reduces the result to the finite-product characterization.
The declaration docstring and DAG route already state the componentwise glue
implemented here; therefore no node update is needed.

Searches: LeanFinder for a module-finite local algebra over a henselian local
ring returned root-lifting definitions and TFAE, without a transfer theorem;
Loogle `HenselianLocalRing, Module.Finite` returned no hits; the launcher's grep
search returned no hits. Direct searches of Mathlib and both library roots also
found no independent transfer theorem that avoids this module or its users.

## Proved and sorry left

Closed: `HenselianLocalRing.finite_local_henselian`
(node `lem-weil-pbc-finite-local-henselian`), 1 of 1 original holes.
Added holes: none. Remaining holes in delivered modules: none.

Both remaining private helpers are proved; the third, duplicated helper was removed
in the second reading in favor of the upstream proved declaration
`IsIdempotentElem.eq_zero_or_one_of_isLocalRing`. Local compilation passes without warnings.
An explicit `#print axioms HenselianLocalRing.finite_local_henselian` reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`: the last comes from
existing imported dependencies, not from a new or remaining hole in this delivery.
Thus this closes the item relative to its stated proof dependencies, as stage 3
requires; it does not claim that the transitive library proof is axiom-clean yet.

## No longer needed

None. All three original proof imports are used directly:
`Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`,
`Sheaf.RingTheory.HenselianEtaleRetraction`, and
`Sheaf.RingTheory.HenselianLocalRootLifting`.
The finite-algebra-local-radical Mathlib leaf is used through maximal-ideal
contraction. No planned dependency node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The second reading found and removed
a duplicated local-ring idempotent calculation already present in the upstream library. The retraction theorem states its
base and algebra in one universe, whereas the finite-product theorem needs
neighborhoods in `max u v`; the proved ULift adapter resolves this without
changing either statement. The expected Stacks checkout is absent from this
clone, but an existing local Stacks copy supplied the source text.


## Second reading by H2

1. **Unchanged interface: PASS.** Compared the complete module with the repository
   using `diff`. The existing declaration `HenselianLocalRing.finite_local_henselian`
   retains its signature byte for byte, and its original docstring is unchanged.
   There are no definitions, change records, other delivered modules, or new public
   statements. The public imports are unchanged; added imports are proof-only.
2. **Proof and axioms: PASS relative to the imported open dependencies.** Compiled
   the original delivery and the repaired module with the authorized local compiler.
   Scanned for `sorry`, axioms and prohibited implementation escapes: none in the
   delivered Lean module. A scratch copy prints the axioms of the public theorem and
   both private helpers. The componentwise helper uses only `propext`,
   `Classical.choice`, `Quot.sound`; the finite-product adapter and public theorem
   also use `sorryAx` from existing imported open proofs. No hole is added here.
3. **Split statements: PASS (none).** There are no split-off statements or new nodes.
   Read the two proved private helpers. For the product lemma, the proper coordinate
   ideals ensure nonzero quotient rings; nontriviality prevents zero and one from
   becoming equal. For the empty index set, injectivity and uniqueness hold for the
   singleton function type, so the zero algebra is covered. No injectivity or local
   map hypothesis was silently added to the original theorem.
4. **Top-down route and pruning: PASS, with one repair.** Repeated a LeanFinder search
   for henselianity ascending to a module-finite local algebra, and grep searches of
   Mathlib and both library roots. No independent transfer theorem was found. The
   grep did find `IsIdempotentElem.eq_zero_or_one_of_isLocalRing` in the upstream
   `WeilConjectures.Mathlib.RingTheory.Idempotents` module: removed the private duplicate
   and used that theorem through a plain import. All three original proof imports
   are directly used, and all four old proof-dependency nodes remain needed. Read
   `dag/units/sk-thm-iff.json`, including `realized`: the item changes no unit step or
   route. Read Stacks `lemma-finite-over-henselian` part (2) and its proof in the local
   source copy; its finite-algebra reduction agrees with this implementation.
5. **DAG agreement: PASS.** Read `lem-weil-pbc-finite-local-henselian` and its dependencies.
   The Lean follows its three steps: etale retraction and finite local product,
   maximal-ideal contraction by the recorded Mathlib leaf, then unique idempotent
   lifting and the root-lifting equivalence. Its `proof`, `proof_deps`, and
   `proof_origin` remain accurate. There are no new node fields to validate.

Changed only the duplicated proved helper and its uses, added the upstream proof-only
import, and corrected the report to describe the two remaining helpers. Closed 1 of 1
original holes; added 0 holes; split off 0 statements; pruned no dependency modules.
