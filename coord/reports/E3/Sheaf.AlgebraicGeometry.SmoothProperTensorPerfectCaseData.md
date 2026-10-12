## What changed
The proof of `AlgebraicGeometry.smoothProper_tensor_perfect_case_data` assembles the
quasi-coherent witnesses from `smoothProper_qcoh_data`, the monoidal witness from
`exists_derivedPullbackMonoidalModel`, and the adjunction from
`nonempty_derivedPullbackAdjunction`. Its signature is unchanged. The unused-variable linter setting is scoped to this theorem.

Repaired `SmoothProperQCohData.lean` by proving its theorem from existing declarations.
Its public imports now provide the tensor, pullback and direct-image interfaces;
plain proof imports supply direct-image preservation, pullback preservation, tensor
closure and the quasi-coherent tensor-unit witness. Its docstring cites Tags 08D5,
08DW, 08DX and 09M1. The unused-variable linter option is scoped to this theorem.
Both node records now describe the actual proofs and their dependencies.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.smoothProper_tensor_perfect_case_data`.
The new theorem `AlgebraicGeometry.smoothProper_qcoh_data` is proved from existing
library declarations; no direct sorry remains in either delivered module.
No holes are added by this delivery. These proofs use existing library declarations,
whose transitive dependencies still contain sorry: both scratch `#print axioms` checks
returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
Net direct holes closed: one original hole; holes added: zero. The additional
quasi-coherent theorem is delivered with a complete proof, not as an open split.

## No longer needed
Removed from `SmoothProperTensorPerfectCaseData.lean`:
- `Sheaf.AlgebraicGeometry.PerfectTensorHomDuality`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.

Removed the unused public imports of
`Sheaf.AlgebraicGeometry.PerfectTensorHomDuality` and
`Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint` from the new
`SmoothProperQCohData.lean`. The proofs do not need these modules directly;
no claim is made that they are unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong
The returned delivery unnecessarily left `smoothProper_qcoh_data` as sorry:
existing library declarations supply all its properties. Its source and proof metadata
previously described a projection-formula hole rather than this proof. The parent node
also still described a hole despite its Lean proof being complete. Both are repaired.
The return asks for five quasi-coherent proof dependency IDs but names four distinct
IDs; the record lists those four, exactly the union of the three steps' uses.

## New nodes
`lem-sc-smooth-proper-qcoh-data` records the proved quasi-coherent data theorem.
Its statement fields are unchanged; its source, proof and proof dependencies now
match the proof. The existing parent node is delivered with updated proof metadata.
Change record: `coord/changes/smoothProperTensorPerfectCaseData-lint.md`.

## Earlier second reading (a previous round; superseded)
1. Compared the delivered module with the repository version. The existing target
   declaration has the same signature; only proof imports and proof terms were added.
   Verdict: pass.
2. The repaired modules compile with the launcher. Neither delivered theorem contains
   a direct sorry. Both use existing library declarations; their transitive axioms may
   still include sorry. No axiom declaration or hollow definition was added.
3. The new quasi-coherent data theorem is proved using
   `schemeDerivedDirectImage_preserves_QCoh`, `exists_compact_derivedTensorUnit`,
   `derivedPullback_tensor_preserve_QCoh`, and
   `canonical_derivedTensor_preserve_QCoh`, with homology isomorphism transport.
   Its statement is unchanged and its docstring identifies the sources and argument.
4. The parent proof uses `smoothProper_qcoh_data`,
   `exists_derivedPullbackMonoidalModel`, and `nonempty_derivedPullbackAdjunction`.
   The unused PerfectTensorHomDuality and DirectImage.Sections imports were removed.
   The new module uses four plain proof imports and the three public interface imports.
5. The parent node now records assembly from the quasi-coherent, monoidal-model and
   adjunction nodes. The new node records direct-image preservation, transport from
   the tensor-unit witness, and pullback followed by tensor closure. Their proof_deps
   are exactly the union of the cited IDs, and statement fields remain unchanged.

Items 2–5 were rewritten for this repair as requested by reviewer X-939f5;
this repair does not claim a fresh independent second reading.


## Second reading by E3
1. Compared the original item with the repository by diff and checked its complete
   theorem signature byte for byte. It is unchanged. The only existing Lean
   declaration changes are its proof and theorem-local lint configuration; the
   removed imports were plain proof imports. No definition or target changed.
   The quasi-coherent module is new in this delivery. Verdict: pass.
2. Compiled both modules locally in import order without errors or warnings.
   Compiled scratch copies with `#print axioms` for both delivered declarations:
   each uses exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last comes from existing open dependencies; neither file contains a direct
   sorry, axiom, unsafe/opaque declaration, implementation override, or hollow
   definition. All witness elimination occurs inside theorem proofs. Verdict: pass.
3. Read the new quasi-coherent theorem and the four supplying declarations.
   Properness supplies the direct-image hypotheses; noetherianity supplies the
   compact and quasi-separated hypotheses of the unit-witness theorem. The
   homology isomorphism has the correct direction for transport. Pullback followed
   by canonical tensor closure gives the tensor witness. Zero complexes, identity
   morphisms and empty schemes introduce no additional conditions. This theorem
   omits the monoidal and adjunction conclusions of the item and is strictly a
   part of the argument; it is proved, with no split-off hole. Independent Loogle,
   Lean Finder and grep searches, plus rg over Sheaf and WeilConjectures, found no
   duplicate bundle theorem. Loogle found the single-functor homology isomorphism;
   a direct unit proof would also need its off-degree vanishing argument, whereas
   the existing unit witness gives the present short proof. Verdict: pass.
4. Read the proof top down: existing quasi-coherent preservation declarations
   supply its three properties, then the existing monoidal model and derived
   adjunction supply the remaining witnesses. Proof-only additions are plain
   imports; the new module's public imports supply its signature interfaces.
   The two removed item imports are listed above. The repository parent node's
   old proof_deps is empty, so there are no omitted old dependency IDs to list.
   The associated unit sk-thm-picard-duality has empty realized statement and step
   lists; no realized node or unit route is bypassed. Verdict: pass.
5. Checked both node records against the Lean terms and resolved every dependency
   ID to its declaration (the monoidal model node also lists its existence
   theorem). Both proof_deps lists are exactly the unions of the proof-step uses.
   The new node has source, proof_origin, three searches, creation, blueprint,
   chapter, unit and Lean records, and its docstring gives the argument and source.
   The existing node's statement and statement dependencies are unchanged.
   Verdict: pass.

Changes in this reading: scoped the parent's unused-variable linter option to
its theorem, updated its lint change record, replaced the unused monoidal-model
witness name `hm` by `_`, and recorded the precise axiom and hole counts. The
mathematical proofs and node proof routes required no repair.
