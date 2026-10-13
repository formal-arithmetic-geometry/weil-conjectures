## What changed

Replaced the proof hole in
`Algebra.strictHenselization_completion_noetherian_faithfullyFlat` with a complete Lean
argument. Its statement, universes, binders and public imports are unchanged.
The argument obtains locality and the extended maximal ideal of the strict henselization,
proves finite generation by mapping generators of the base maximal ideal, and identifies
the quotient as `IsLocalRing.ResidueField C`. The existing quotient completion criterion
then gives Noetherianity. The existing completion-flatness theorem supplies flatness;
Mathlib's finite-generation completion-locality lemmas and flat-local faithful-flatness
lemma give the other two conjuncts. No Noetherianity of C is assumed or imported.

Added the private proof imports `Sheaf.RingTheory.StrictHenselizationLocalMaximalIdeal`,
`Mathlib.RingTheory.AdicCompletion.LocalRing`, and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`. Added the structural comparison statement
`Algebra.strictHenselization_local_maximalIdeal` in its own module and node. It has no
Noetherian hypothesis and concerns C itself, not its completion. Updated the item's DAG
proof, proof dependencies and proof origin to the compiled route.

Compilation: both delivered modules compile together in dependency order through
lcompile.py; the main module also compiles alone against the sandbox overlay. The
unnecessary experimental Noetherian.Basic import was removed and the main module
recompiled successfully. Mathlib searches found the completion-locality and faithful-flat
lemmas. LeanSearch returned an HTTP internal-server error, recorded as unavailable.

## Proved and sorry left

Closed the item's sole direct hole:
`Algebra.strictHenselization_completion_noetherian_faithfullyFlat`
(node `lem-sc-strict-henselization-completion-noetherian`). No direct sorry remains in the
item's module.

Added one direct hole:
`Algebra.strictHenselization_local_maximalIdeal`
(node `lem-sc-ring-strict-henselization-local-maximal-ideal`, module
`Sheaf.RingTheory.StrictHenselizationLocalMaximalIdeal`). Its entire proof is `by sorry`;
its docstring and node give the category equivalence, colimit comparison and maximal-ideal
transport argument. This is a decomposition, not a sorry-free proof of the target:
one upper hole closed and one strictly lower structural hole added, net zero direct holes.
The existing dependency `Algebra.strictHenselization_completion_flat` still contains
its own sorry and is used as intended. No existing dependency module was edited.

The new statement was checked on the field case (the extended maximal ideal is zero
and the strict henselization is the separable closure), on an already strictly henselian
local ring (C is A up to the pointed-colimit comparison), and on general non-Noetherian
local rings (the triples construction still supplies locality and the same maximal
ideal). The zero-ring case is excluded by IsLocalRing A and the given map to the field K.
It uses no completion or Noetherianity conclusion from the item or its callers.

## No longer needed

Removed the direct import `Sheaf.RingTheory.StrictHenselizationTriples` from the item's
module. Its role is now below the new structural comparison: the new module imports it
and its node uses `lem-weil-pbc-strict-henselization-triples`. Thus that module and node
are retained in the target closure, not claimed as pruned. The old direct proof dependency
`lem-weil-pbc-strict-henselization-triples` is replaced by
`lem-sc-ring-strict-henselization-local-maximal-ideal` in the item's `proof_deps`;
the triples node remains a transitive dependency of the new comparison. No original
proof-dependency module becomes unnecessary in the import closure. The existing flat-local Mathlib leaf is still used through
its faithfully-flat clause. No new inverse-limit unit-construction lemma is needed:
Mathlib `AdicCompletion.isLocalRing_of_fg` and
`AdicCompletion.algebraMap_isLocalHom_of_fg` cover that step without assuming C is
Noetherian. No modules are claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The plan said that the triples theorem supplies locality and the extended maximal ideal
for the arbitrary C appearing in the ring predicate. Its actual Lean signature is about
an existential cocone of `Scheme.etaleResidueTriplesRingDiagram`. The predicate
`Algebra.IsStrictHenselization` instead uses a cocone in CommAlgCat of etale algebras
pointed in K. No existing declaration connects these two signatures. The new node states
precisely the structural consequence of the missing comparison; no source statement or
existing signature was changed. The triples theorem is retained as a generic tool below
this node, so the unit route is preserved. The unit record sk-thm-br has no realization
entry assigned to the item that is bypassed by the proof.

Read the source statements and proofs at https://stacks.math.columbia.edu/tag/04GP,
https://stacks.math.columbia.edu/tag/04GW and
https://stacks.math.columbia.edu/tag/06LJ. The local source tex files are not present in
this remote checkout. The complete comparison argument is written in the new docstring;
the remaining work is its Lean implementation. The existing scheme-pointed colimit
local-structure module has a different statement and does not provide this comparison
for the ring predicate. Searches of the repository and the imported blueprint found
no declaration of the required ring-predicate consequence.

## New nodes

`lem-sc-ring-strict-henselization-local-maximal-ideal` is the local-ring and maximal-ideal
consequence of the ring strict-henselization predicate, without Noetherianity. It is a
strictly smaller input to the completion proof: it says nothing about completion,
flatness or faithful flatness. Its source is Tags 04GP(2),(4) and 04GW. The proof first
identifies pointed etale algebras with etale residue triples, then identifies their
A-algebra colimits and transports the local structure and extended maximal ideal.
Its sole new Lean module is
`lean/Sheaf/RingTheory/StrictHenselizationLocalMaximalIdeal.lean`. The new node inherits
sec-curve-estimates and sk-thm-br and records real LeanFinder, Loogle, grep and unavailable
LeanSearch queries. No change record is needed: no existing signature or definition,
public import, visibility or instance changed.

## Second reading by W2

1. PASS: Compared the delivered item with the repository using diff and separately
   checked its theorem signature byte for byte. Only private proof imports and the
   proof body differ. The new module introduces only its named structural theorem;
   no existing definition, signature, visibility, or public import changes.
2. PASS: Independently compiled both modules in dependency order with lcompile.py:
   26.8 seconds for the structural module and 3.7 seconds for the item, without errors
   or warnings. A scratch axiom probe against the sandbox overlay printed only
   propext, Classical.choice, Quot.sound and sorryAx for each delivered theorem.
   The item has no direct sorry; the new named structural theorem has exactly one.
   There are no forbidden declarations, hollow definitions, or data constructions
   choosing arbitrary witnesses from unproved existence theorems. The existing
   completion-flatness dependency remains open, as reported.
3. PASS: The structural theorem is strictly smaller than the item: locality and the
   extended maximal ideal of C, with no Noetherianity or completion conclusion.
   Read the pointed-algebra predicate, triples theorem, and the comparison proof
   in the docstring. A map to K determines its prime by its kernel and its residue
   embedding uniquely; morphisms commute with K, so the stated equivalence and
   colimit transport establish the claimed result. Field and already strictly
   henselian cases agree, and the argument requires no Noetherian assumption.
   Independently checked Stacks [04GP](https://stacks.math.columbia.edu/tag/04GP)
   and [04GW](https://stacks.math.columbia.edu/tag/04GW). Fresh LeanFinder search
   for filtered colimits of pointed etale algebras, Loogle search `IsLocalRing,
   Ideal.map`, and Mathlib grep for henselization/pointed-etale colimits found no
   direct replacement. Repository searches also found no ring-predicate comparison:
   StrictHenselizationLocalStructure concerns a scheme neighbourhood colimit;
   EtaleTripleStrictHenselizationIdentification concerns two triples cocones.
   These do not close the new comparison in a few minutes.
4. PASS: Read the proof from the upper theorem downward. Finite generation and the
   residue-field quotient supply exactly the general completion criterion's
   hypotheses; Mathlib's finite-generation locality lemmas avoid assuming that C
   is Noetherian. Flatness and the local map give faithful flatness directly via
   the existing Mathlib leaf. Proof-only additions are plain imports; existing
   public imports are needed by the signature. The structural module retains the
   triples proof-route import. The unit sk-thm-br has empty realized entries for
   its statement and sole step, so no assigned realization is bypassed. No module
   is pruned. Clarified the removed direct triples dependency in No longer needed.
5. PASS: Compared the old and new item nodes: only proof, proof_deps and proof_origin
   change. Their steps track the Lean proof, and proof_deps equals their uses.
   The new node has the required source, searches, creation, blueprint, chapter,
   unit and verbatim Lean statement fields; its route uses triples and colimit
   comparison, without referring back to the completion item. The report correctly
   records one upper hole closed and one lower hole added as a net-zero decomposition.

Second-reading changes: clarified the direct-versus-transitive triples dependency
in the pruning report and added this independent review. No Lean or node repair was
needed. The structural comparison remains the single new split-off statement.
