## What changed

Repaired reviewer X-6acd0 (head 6acd0cac5), point 4. Corrected
`AlgebraicGeometry.RingedSpace.coherent_cokernel_relations_local` to the exact
neighbourhood conclusion requested in the return: every x ∈ U has V ≤ U
containing x, a finite-free map ψ to G.over V, and an epimorphism from kernel ψ
to the overMap restriction of kernel g. Its hypotheses, name, and visibility stay
unchanged. Replaced the disputed docstring by the complete local lifting,
finite-image-generation, and relation-kernel argument. Retained the P¹
counterexample as historical explanation, rather than disputing the corrected
statement.

Adapted only the proof and necessary proof imports of
`Sheaf.AlgebraicGeometry.CoherentCokernelRelations` (currently unclaimed). It
now chooses neighbourhoods, proves they cover the slice site, obtains finite
type there by coherence and the epimorphism, transports generators through the
iterated-slice equivalence, and applies finite-type locality. Its existing
signature and visibility are unchanged. Two proof-only `import all` lines reuse
proved private helpers of CoherentFiniteTypeSubKernel and
CoherentKernelConditionRestriction; no helper or new node is introduced.

Updated both existing nodes' proof metadata to the actual local route. Updated
the local node's natural-language statement and lean.statement and added the
complete statement_change record. Added
`coord/changes/coherent-cokernel-relations-local.md` with old/new signatures,
all import users, the direct declaration user, its holder, and the forced edits.

## Proved and sorry left

Original item holes closed: none (0 of 1). Holes added: none. Split off: none.
This is a statement correction and forced downstream proof repair, not a hole
closure or decomposition. The corrected public named theorem
`AlgebraicGeometry.RingedSpace.coherent_cokernel_relations_local`, node
`lem-weil-pbc-coherent-cokernel-relations-local`, remains exactly `:= by sorry`.
Its docstring supplies its source and full mathematical proof.

The already proved
`AlgebraicGeometry.RingedSpace.coherent_cokernel_relations` is re-proved from
that corrected assertion by a complete compiling Lean proof of finite-type
locality. No sorry is added to it or to any other module. Both delivered modules
compile without warnings using lcompile.py; the delivery probe checks their
axioms, with the existing named local hole accounting for sorryAx.

## No longer needed

No existing imports, nodes, or modules are pruned. The adapted theorem's direct
DAG proof dependencies are now the local assertion, coherence, the finite-type
epimorphic-image theorem, and the two existing helper modules used for locality
and transport. The local lifting and snake-lemma steps are still needed below
the corrected local assertion; they are not pruned from the library. The
previous rejected auxiliary/factorization statement is still absent.

The adapted parent node drops these old direct proof-dependency edges:
`lem-weil-pbc-ringed-space-module-exactness-local-lifting`,
`lem-weil-pbc-module-finite-type-image-extension`,
`lem-weil-pbc-snake-lemma-abelian`,
`lem-weil-pbc-abelian-exact-epi-cokernel`, and
`def-weil-sheaf-of-modules-category`. Local lifting and the snake lemma
remain dependencies of the local assertion; the other edges are replaced by
the finite-type epi image and proved locality/transport helpers. This records
edge pruning only: no Lean import or globally unreachable module is claimed
as pruned. The local node retains all its old proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The previous fixed-U assertion omitted the source's shrinking and was false.
On P¹_k with F = I_p ≅ O(-1), G = O, U = X and g : O → k(p), kernel g is O(-1).
A map O^m → O is a row of constants with free kernel, whereas every map from a
free sheaf to O(-1) vanishes. Hence its kernel cannot surject onto kernel g.
The old auxiliary merely restated that false existential with extra data.

The former downstream proof used that false global assertion directly. The
new proof uses the neighbourhood conclusion and locality, preserving the
original downstream statement. The parent node's DAG metadata had not recorded
its actual use of the local replacement, although its Lean proof imported and
applied it; this delivery aligns that metadata. The unit sk-thm-p1 and its
realized route are unchanged.

## Statement corrected

Corrected node: `lem-weil-pbc-coherent-cokernel-relations-local`.
Its statement_change records the original statement verbatim, reason, source,
date, author, and original proof/proof_deps (both changed). The base node had
no earlier statement_change. A complete source JSON scan found no DAG node
whose stmt_deps or proof_deps cited this local node, so the base citer list is
empty; none is omitted from the record. The actual Lean declaration user is
`Sheaf.AlgebraicGeometry.CoherentCokernelRelations`, whose theorem remains true
and is adapted in this delivery. The delivered parent node now cites the local
node as part of the repaired route. All transitive import users are listed in
the change record; their interfaces retain the same meaning.

## Forced adaptations

Module: `Sheaf.AlgebraicGeometry.CoherentCokernelRelations`, holder: unclaimed.
Compiled the original module against the changed local module. It fails at the
old fixed-U application with the following compiler error:

```
CoherentCokernelRelations.lean:48:9: error: Tactic `rcases` failed:
`x✝ : ∀ x ∈ U, ∃ V, ∃ (hVU : V ≤ U), x ∈ V ∧ ∃ m ψ e, Epi e`
is not an inductive datatype
```

Necessary edits: added the two proof-only imports at lines 11–12; replaced the
original proof at lines 48–52 by the neighbourhood-cover and locality argument
at lines 50–92. The neighbourhood quantifiers force replacing the original
existential unpacking. Coherence and the epi give finite type on each V;
the slice equivalence identifies that restriction with the over-site restriction
used by LocalGeneratorsData; finiteType_of_cover combines those local generator
covers to conclude on U. The two imports provide exactly the existing proved
private locality and transport helpers used in these steps. All existing
signatures and visibility are identical. No other lines of the adapted Lean
module change. The adapted module compiles against the changed dependency.
The change record names the module, holder, compiler error, forced lines, and
all users.

## Second reading by K4

1. Compared both delivered modules with the repository using diff. The sole
   interface change is the explicitly recorded neighbourhood conclusion of
   `coherent_cokernel_relations_local`. Its hypotheses, name and visibility are
   unchanged. The downstream `coherent_cokernel_relations` signature and
   docstring are byte-for-byte unchanged; its only edits are the necessary
   proof and two proof-only imports. No definition or target is changed.
   Verdict: the correction is disclosed and the forced adaptation preserves
   the downstream statement.
2. Compiled both modules together through lcompile.py, without errors or
   warnings. Compiled scratch copies of the actual delivered files with
   #print axioms for both public theorems. Both lists contain only propext,
   Classical.choice, Quot.sound and sorryAx. The sole delivered sorry is the
   named local theorem, exactly `by sorry`, with its source, full argument and
   existing node. The downstream proof has no hole. No forbidden declaration
   or attribute, and no data definition or arbitrary existence-based data
   choice, is introduced. Verdict: the proof repair typechecks, conditional
   on the explicitly retained local hole; zero holes are closed or added.
3. There are no new split-off statements or nodes. Read the corrected local
   theorem against Stacks 01BY (lemma-coherent-abelian), proof of (3), at
   https://stacks.math.columbia.edu/tag/01BY (the cited local tex file is absent
   on this machine). The finitely many cokernel sections lift after shrinking;
   the finite-type image has local finite generators; projection of the
   combined relation kernel is locally surjective by subtracting a combination
   of those image generators. The overMap target is exactly the restriction
   of the original kernel. Coherence is used only downstream to make the
   combined kernel finite type. Checked empty U, rank zero, f = 0, and the
   one-point case; no quasi-compactness or global lifting is assumed. The P¹
   example refutes the old fixed-U conclusion, not the corrected one.
   Verdict: the corrected assertion is true and supplies precisely the local
   input the downstream proof needs.
4. Searched Mathlib via msearch Loogle for SheafOfModules.IsFiniteType and grep
   for GeneratingSections, CoversTop and overMap, and searched upstream and
   lean/Sheaf for cokernel relations and finite-type locality. Read the existing
   finiteType_of_cover, finiteType_pushforward_leftAdjoint, finiteType_of_iso,
   and coherent_iterated_slice_relations. The latter concerns finite-free maps
   into iterated restrictions of coherent G, not transport of the arbitrary
   overMap restriction of kernel g, so it does not replace this argument.
   The proof reuses proved generator/locality helpers and the existing epi
   image theorem; both added imports are proof-only. Read sk-thm-p1.json's
   realized fields: neither delivered node is a unit realization being
   bypassed, and no unit route is changed. Verdict: retain the Lean argument;
   explicitly list all removed old direct dependency edges, without claiming
   a globally pruned module.
5. Read both node files and compared changed fields against the baseline.
   The local natural-language and lean.statement match the corrected Lean
   signature, and its statement_change retains the old statement, route and
   dependencies. Its local lifting, finite-image and relation-kernel plan
   matches its docstring. The parent's three steps track the covering proof,
   coherence/epi-image argument, and proved private locality/transport helpers
   actually used in Lean. Its proof_deps are the union of those uses. Verified
   the baseline contains no DAG citer of the local node; the corrected parent
   now records its actual use. Verdict: metadata agrees with the delivery.

Second-reading changes: updated the change record's transitive-user inventory
from 925 to 933, adding the eight users present in the current source baseline;
completed the report's list of old direct proof-dependency edges removed from
the adapted parent. Added this independent reading. No Lean code or node
required repair, and no hole was closed or split off.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CoherentCokernelRelations
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ljj1f56p/lean/Sheaf/AlgebraicGeometry/CoherentCokernelRelations.lean:48:9: error: Tactic `rcases` failed: `x✝ : ∀ x ∈ U, ∃ V, ∃ (hVU : V ≤ U), x ∈ V ∧ ∃ m ψ e, Epi e` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-ljj1f56p/.lbuild) [3.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
