## What changed

Completed `Module.flat_and_flat_of_flat_fibre_noetherian` in its original module,
with its original signature and visibility. Added proof-only imports of
`Mathlib.RingTheory.LocalRing.RingHom.Basic` and `Mathlib.RingTheory.Nakayama`.
The proof implements the existing seven-step plan: transport the fibre to the
quotient module, construct the surjective tensor comparison by ideal-span
induction, deduce injectivity from base flatness, apply the existing local
criterion in Filtration, use Nakayama upstairs, construct faithful flatness,
and invoke the existing FlatPermanence theorem.

The tensor comparison is a local proof, with compatibility with the two
multiplication maps checked by tensor induction. The quotient equivalence is
explicitly promoted to a linear equivalence over the quotient ring. The
restriction-of-scalars instance needed by FlatPermanence is identified using
the given scalar tower. No existing dependency is adapted, no new declaration
is introduced, and the original DAG route and unit route are retained.

## Proved and sorry left

Closed the sole original hole:
`Module.flat_and_flat_of_flat_fibre_noetherian` (node
`lem-weil-pbc-criterion-flatness-fibre-noetherian`). One of one holes closed;
zero holes added or split off. No `sorry` remains in the delivery. This is a
proof, not a decomposition. The delivery dry run checks the declaration's
axioms as well as compilation.

## No longer needed

No original imports, nodes, or proof dependencies are pruned: both original
proof imports, FlatPermanence and Filtration, are used. All new proof imports
are used. The earlier sandbox attempt's unlanded FlatFibreData,
FlatFibreLocalCriterion, FlatFibreTensorInjective,
FaithfullyFlatOfLocalNontrivial, and FlatDescentFromFaithful modules and four
proposed nodes have been removed from the delivery. They are not library
pruning and add no work items. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The original brief and seven-step DAG plan are usable unchanged. The earlier
sandbox attempt did not compile and its report omitted holes in FlatFibreData
and incorrectly counted the already-proved local-criterion wrapper as a hole.
Its proposed `flat_fibre_quotient_nontrivial` was false: without finiteness,
a nonzero module over a local ring can have zero closed fibre (for example
the fraction field of a nonfield discrete valuation ring). The completed
proof instead uses the supplied finiteness over S', Nakayama there, and
locality of S to S', exactly as the original plan requires. The quotient
equivalence in that attempt was only S-linear, which is insufficient for
transporting flatness over S/I; the completed proof checks the stronger
quotient-linear structure. None of these abandoned helper statements is
delivered.

## Second reading by N3

1. Interface preservation: PASS. Diffed the only delivered module against
   the repository version. The entire existing theorem header, its universes,
   namespace, visibility, docstring, and original public imports are byte for
   byte unchanged. Only its proof and two proof-only imports were added.
   No definitions or auxiliary declarations are delivered; no change record
   is needed.
2. Proof and axioms: PASS. Independently compiled the complete sandbox with
   lcompile.py, with no errors or warnings (3.9 seconds). Compiled a scratch
   copy with `#print axioms Module.flat_and_flat_of_flat_fibre_noetherian`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the delivered Lean for sorry and forbidden declarations: none.
   Read the quotient-linear equivalence, ideal-span induction proving tensor
   surjectivity, commuting multiplication maps and injectivity argument,
   Nakayama over S', and the scalar-action identification for descent.
   The argument uses finite generation over S', never an unsupported finite
   generation assumption over S. No arbitrary data is chosen from an
   unproved existence theorem.
3. Split statements: PASS (none). The sole original hole is closed and zero
   holes are added. No split-off statement, new module, or new node remains
   in the delivered set. For edge cases, a field base gives I = 0 and the
   fibre hypothesis already gives S-flatness; zero M is excluded by the
   original Nontrivial assumption. The infinite nonzero module with zero
   closed fibre discussed above is not admitted without finiteness over S'.
4. Route and pruning: PASS. Repeated LeanFinder with the different query
   "finite module flat over base and flat quotient over extended maximal
   ideal implies intermediate algebra flat" and searched Lean/Mathlib for
   flat fibre criteria. The results concern localization, formal smoothness,
   or faithful flatness of an algebra; none supplies this theorem. The
   existing proved local criterion and FlatPermanence are both applied.
   All six old proof dependencies are used, including Nakayama and the
   faithfully-flat constructor recorded as Mathlib leaves. No original
   dependency is unused, so `No longer needed` is complete. The new imports
   provide locality/Jacobson facts and the exact Nakayama theorem used.
   Both are ordinary proof-only imports. Read sk-thm-p1.json `realized`:
   this tool lemma replaces no realized unit step and changes no unit route.
5. DAG agreement: PASS. Read the item's seven proof steps, proof_deps,
   proof_origin, and each dependency's Lean or Mathlib mapping. They match
   the completed argument, including the existing Filtration criterion,
   Submodule.eq_bot_of_le_smul_of_le_jacobson_bot,
   Module.FaithfullyFlat.mk, and the FlatPermanence descent. No DAG edits
   are required. The source statement and first-paragraph argument were
   also checked against [Stacks Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
   because the cited local algebra.tex is absent on this machine.

Second reading changed only this report: recorded the independent review,
axiom check, and fresh search. The Lean proof needed no repair.
