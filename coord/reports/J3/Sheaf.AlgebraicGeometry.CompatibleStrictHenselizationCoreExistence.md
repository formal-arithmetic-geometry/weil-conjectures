## What changed

Closed the single hole in
`AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreExistence`.
The theorem signature and original public imports are unchanged. Added proof-only imports of
`Sheaf.Paper.StrictHenselizationFunctoriality` and
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`.
Four proved private helpers identify the integral point residue embedding, transport it along a
field spectrum map, descend a separable embedding through a separably closed field, and
construct the required residue map for a single geometric point.
The final proof combines the single-point constructions on the actual coordinate-ring colimits,
with identity spectrum isomorphisms. No data definition or new public interface is introduced.
Updated the existing node's proof, proof_deps and proof_origin to describe the Lean argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreExistence` (node `compatible-strict-henselization-core-existence`): one of one holes. No new holes were added. Existing lower declarations used by `strictHenselizationResidue` remain outside this delivery. Local single-file compilation succeeds without warnings.

## No longer needed

No imports, planned dependency nodes, or modules were removed. The proof-only imports remain necessary.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempted to add a split-off public properties theorem and to alter a lower factorization node. Those changes were not necessary for this item and were removed. The target statement and existing lower interfaces remain unchanged.

## Earlier second reading (a previous round; superseded)

1. **Interface: pass.** Compared the delivered module and node with the repository using
   `diff -u`. The sole existing theorem's entire signature is byte-for-byte unchanged,
   including hι, both integral factorization hypotheses, all field assumptions, the
   existential ring structures, both spectrum isomorphisms, both universal homeomorphisms,
   and both structural equations. No definition changes, change records, or forced
   adaptations occur. Only four private proved helpers and two plain proof imports are added.

2. **Proof and axioms: pass, conditional on existing lower holes.** Single-file lcompile
   succeeds without warnings. A scratch copy with `#print axioms` for all five declarations
   shows only propext, Classical.choice and Quot.sound for the first three helpers; the
   single-point helper and public theorem additionally use sorryAx through existing
   strict-henselization results. No delivered sorry, axiom, unsafe, opaque, implemented_by,
   extern, or data definition occurs. A and B are the actual strictHenselizationRing colimits.
   The residue equivalence δ is taken from an ExistsUnique statement with pointed equations,
   not from arbitrary unproved existence; η is obtained from a fully proved upstream theorem.
   Checked the field descent in WeilConjectures.Mathlib.FieldTheory.IsSepClosed (lines 71–92),
   the integral polynomial transport in Mathlib's RingHom.IsIntegralElem.of_comp, and the
   upstream purely inseparable universal-homeomorphism instance. Injectivity of β gives
   η ∘ algebraMap = b; hb then gives integrality of every element of k over E. Flatness and
   surjectivity justify cancellation of ν for arbitrary target schemes.

3. **Split statements: pass (none).** Zero new holes or public statements are split off.
   The private descent lemma also works when E = F or β is an isomorphism; it imposes no
   characteristic restriction. For a nontrivial purely inseparable extension of a separably
   closed field, integrality remains necessary and gives precisely the residue universal
   homeomorphism. Empty schemes admit no input field-valued point. Confirmed the reported
   lower-interface dispute: the universally quantified pointed-map factorization permits
   a residue automorphism over ℚ moving √2, although a pointed neighbourhood fixes its
   embedding. This delivery uses the correct existential pointed residue conclusion of
   strictHenselizationResidue and does not exploit that excessive quantifier directly.
   The unresolved dependency is explicitly reported above; it is not repaired in this item.

4. **Route and pruning: pass.** Searched the project by strictHenselizationResidue and the
   existence declaration, and searched Mathlib through msearch grep by field descent,
   integral composition and purely inseparable spectra. Read the matching proved upstream
   descent theorem rather than recreating it. The four helpers supply the necessary residue
   identification, integral descent and scheme factorization, with no restatement hole.
   Every public import supplies a notion in the signature; both new plain imports supply
   proof results. No old proof dependency is discarded, so `## No longer needed` is complete.
   Read sk-thm-p1's realized statement and steps: they remain unchanged; this item is below
   that unit's realization and the proof supplies its strict-henselization construction.
   Read Stacks [04HX](https://stacks.math.columbia.edu/tag/04HX) for the neighbourhood colimit
   and relative separable residue closure, [03PS](https://stacks.math.columbia.edu/tag/03PS)
   for its spectrum, and [04DY](https://stacks.math.columbia.edu/tag/04DY) for the surrounding
   universal-homeomorphism route. The retained hι is unnecessary for the independent
   one-point existence clauses, and no compatibility conclusion has been removed.

5. **DAG: pass after attribution repair.** The node differs only in proof, proof_deps and
   proof_origin. Its four steps match, respectively, the residue cancellation helpers,
   strictHenselizationResidue, separable descent and integral/purely inseparable construction,
   and flat-surjective cancellation followed by the two applications. The dependency union
   is the two old definition nodes plus lem-weil-pbc-strict-henselization-functoriality,
   whose module actually states strictHenselizationResidue. No new nodes require validation.

Changed in this reading: made the DAG's field-descent attribution explicitly upstream
(WeilConjectures.Mathlib.FieldTheory.IsSepClosed) and added this review with the exact axiom
findings and lower-interface limitation. No Lean repair was needed.

## Second reading by J3

1. Interface: pass. Compared the delivered module and node with the repository. The target theorem signature is byte-for-byte unchanged; only its proof, proof dependencies, and proof origin are updated. No definitions or public interfaces are changed.

2. Proof and axioms: pass. The delivered module compiles with lcompile without warnings and contains no delivered `sorry`, axiom, unsafe, opaque, implemented_by, or extern. The concrete `strictHenselizationRing` colimits are used directly. Existing lower holes are only imported dependencies.

3. Split statements: pass. No new statements or holes are delivered. The proof uses existing `strictHenselizationResidue` and upstream field descent and universal-homeomorphism results.

4. Route and pruning: pass. The unit route through strict henselization functoriality is retained. The two added imports are proof-only and required by the helpers; no original imports or dependency nodes are removed.

5. DAG: pass. The existing node's proof, proof dependencies, and proof origin describe the four helpers and final construction in the Lean file; its statement and statement dependencies are unchanged.

Changed in this reading: removed an erroneous attempted split-off module, node, and change record from the sandbox delivery. No Lean repair was needed.
