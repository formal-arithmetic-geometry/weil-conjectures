## What changed

Repaired the returned delivery against the current e47efb5a5 source sync. The retained
seven-file version compiled, but its change to the upstream definition
`upperStarCompIso` violates the new source-library gate. This repair removes every
source-library edit and all three consumer adaptations. The delivery now contains
only `CondensedFiniteFamilyHomDescent`, `CondensedOverlapFactorTranspose`, and
`CondensedLocalCoefficientAdjoints`.

The assigned theorem
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_family_hom_factorizations`
is proved with its signature byte-for-byte identical to current sheaf-dag. The
proof constructs the filtered colimit of the actual pulled coefficient modules,
uses finitely presented Hom continuity on each oriented overlap, chooses one
common filtered stage, and transposes the factors in both directions.

The completely proved overlap helper now uses `overlapComparison`, a component
presentation of the unchanged upstream comparison. `comparisonHom` and
`comparisonInv` give explicitly typed components; `componentComparison` reconstructs
a natural isomorphism. Its reconstruction identity is proved generically, and
`overlapComparison_eq_original` specializes that identity to `upperStarCompIso`.
This avoids the expensive structural comparison at coefficient sheaves. The family
proof uses this representation internally and transports both final equations to
the original comparison. No source definition, source declaration, or consumer
proof is delivered.

The retained local-adjoint representation repair constructs the mixed-scalar
underlying map explicitly and proves it equal to the previous canonical adjunct.
Its signatures and meaning are unchanged. The two existing proofs in that module
use the equality API. This module is unclaimed. Its change record is
`coord/changes/C1-condensed-local-adjoint-underlying-map.md`; the downstream table
has been refreshed against the current source. Any target using the repaired
definition requires the prescribed meaning review; the equality theorem identifies
the data exactly. No target text changes.

All three delivery files compile at the ordinary per-file limit: approximately
13–17 seconds for the local-adjoint module, 17–20 seconds for the overlap helper,
and 24–27 seconds for the family proof. The unchanged direct consumer
`CondensedFiniteLocalSubmodules` is also checked against this sandbox overlay.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_family_hom_factorizations`
(node `lem-weil-pbc-condensed-finite-family-hom-descent`). Added 0 holes. This is a
proof from existing library declarations, not a decomposition.

The helper
`AlgebraicGeometry.ProEtale.finiteCoefficient_overlap_factor_transpose`
(node `lem-weil-pbc-condensed-overlap-factor-transpose`) is fully proved. Every
supporting scalar-unit, colimit, transposition, linearity, and representation-equality
lemma is proved. There are zero direct sorries in all three delivered Lean files
and no open split-offs. Imported library obligations may still contribute
transitive `sorryAx`; no claim is made that the target closure is axiom-free.

## No longer needed

Removed proof import `Sheaf.Paper.CondensedCoefficientFamilyHomStage` and proof
dependency `lem-weil-pbc-condensed-coefficient-family-hom-stage`: generic
`condensed_fp_hom_stage` suffices. Removed
`def-weil-pbc-condensed-e-module-category` from this proof's dependencies: actual
pulled coefficient rings avoid coefficient normalization. Other modules may still
reach these nodes; this is pruning of this proof route. The blueprint unit route
is retained.

The overlap helper needs no direct proof import of
`CondensedCoefficientComplexDiagram`, because the local-adjoint definition publicly
supplies that API. Duplicate private scalar-unit proofs and unused generic
transitivity/identity helpers remain removed. The earlier scalar-extension-carrier
experiment is excluded.

This repair additionally excludes the retained edits to
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`,
`WeilConjectures.WeilSheaf.UpperStarComp`, and
`Sheaf.AlgebraicGeometry.ProEtaleLocalQuotientVanishing`. These modules remain in the
library unchanged; they are not withdrawals. The obsolete source-comparison change
record is removed from the sandbox delivery.

The second reading also removes the redundant direct proof import
`Sheaf.Paper.ProfinitePointPullback` from the family module and its direct DAG
proof dependency `lem-weil-pbc-profinite-point-pullback`. The overlap helper still
imports and uses this module for monoidality of the square comparison; a scratch
removal there fails at that instance, so the helper retains it.

## Where the brief, the DAG or earlier work was wrong

A rebase of the retained seven-file proof alone was insufficient. The new
2026-10-17 source gate permits existing theorem proofs and private helpers in the
source tree, but rejects adding public declarations or changing definition bodies.
The retained source-comparison representation therefore could not be delivered.
Its representation change is now confined to the new Sheaf helper, with a proved
equality to the original comparison and explicit transport in the family proof.

Directly checking equality of the specialized component representation with the
original comparison exhausted kernel heartbeats. Proving the reconstruction
identity for an abstract natural isomorphism, then specializing it, removes that
expensive reduction. The two finite-family equations are still exactly the original
ones. No file or proof was split to evade a timeout; no limit was raised.

The original DAG's coefficient-normalization route is unnecessary. The updated
node proof follows actual pulled coefficient colimits and records the final
comparison transport. The finite-stage argument includes the empty family because
a filtered category supplies an upper object even for an empty finite set. The
transposition argument allows zero modules, empty overlaps, and noninvertible
model maps; it introduces no additional hypothesis.

## New nodes

`lem-weil-pbc-condensed-overlap-factor-transpose`: a fully proved fixed-field,
single-span scalar-adjunction compatibility theorem. Its component comparison is
proved equal to the specified upstream comparison. The theorem assumes an existing
E-linear factor and proves its transpose; it asserts no stage existence, finite
presentation, qcqs condition, invertibility, or finite-family descent. The node's
Lean statement and supporting declaration list reflect this repair. There are no
new holed nodes. The only change record is
`coord/changes/C1-condensed-local-adjoint-underlying-map.md`.

## Second reading by C1

1. **Interfaces and constructions: pass.** Compared every delivered module with
   the read-only repository. The overlap module is new. The family theorem header
   is byte-for-byte identical. All seven existing declaration headers in the
   local-adjoint module, including the private coefficient-unit lemma, are also
   byte-for-byte identical; the enclosing original variable contexts are unchanged.
   The one changed existing definition body is declared in
   `coord/changes/C1-condensed-local-adjoint-underlying-map.md`.
   `canonicalAdjoint_eq_explicit` compares its constructed underlying map with the
   old adjunct, `finiteCoefficientLocalAdjointHom_linear` proves linearity, and
   `finiteCoefficientLocalAdjoint_eq_canonical` proves equality of module maps.
   Thus this construction introduces neither an arbitrary existence witness nor
   a change in target meaning. Rechecked the downstream table with
   `tools/downstream.py --uses finiteCoefficientLocalAdjoint`; its existing users
   are covered. The original direct consumer `CondensedFiniteLocalSubmodules`
   compiles unchanged against the delivered overlay.

2. **Proofs and axioms: pass.** Independently compiled all three modules in import
   order at the ordinary limits: 13.3, 13.7 and 23.2 seconds, without warnings.
   Scanned their actual sources: no direct `sorry`, axiom, unsafe/opaque declaration,
   external implementation, skipped kernel checking, or raised resource limit.
   A scratch copy of the family proof checked `#print axioms` for all 18 public
   declarations listed by the delivered nodes. The only reported axioms were
   `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`. In particular,
   the generic scalar-unit lemmas and component-comparison constructions have no
   `sorryAx`. There are no newly selected data from unproved mere existence.
   One original hole is closed, zero holes are added; this is not a decomposition.

3. **New statement and smaller cases: pass.** There are no open split-offs. Read
   the complete proof of `finiteCoefficient_overlap_factor_transpose`, including
   `pulledScalarHomEquiv_hom`, `squareRestrictIso_hom`, `squareModIso` and
   `factorSquare`. The new theorem assumes an existing E-linear factor at a fixed
   field; it proves its scalar transpose and does not restate stage existence or
   finite-family descent. Neither map to M is assumed invertible. Both composites
   are compared as F-linear maps by the injectivity of the composed adjunction.
   The zero-module, empty-overlap and E=F cases require no cancellation or extra
   hypothesis. For the family theorem, qcqs is used on each pairwise pullback
   exactly at `condensed_fp_hom_stage`; finite presentation is transported by
   `fp_pullback`. The empty index type is covered by filteredness supplying an
   upper object for the empty finite set. Independent LeanFinder search for
   monoidal pullback/scalar-extension transposition found ModuleCat adjunction
   formulas, not this internal-module square theorem; Loogle confirmed the
   naturality lemma used here. Local searches also found `pullbackExtendScalarsIso`
   and the private `local_adjoint` in `CondensedLocalModelGluing`; the latter is a
   downstream consumer and cannot replace this proof without an import cycle.
   The generic existing coequalizer-colimit and fp-pullback lemmas are used.

4. **Top-down route and pruning: pass, one import removed.** The proof constructs
   the pulled coefficient colimit, identifies its actual adjoint legs, applies
   generic fp Hom factorization to all I×I×Bool overlaps, chooses a common upper
   stage, and transposes each factor. The final equations are transported through
   the proved equality `overlapComparison_eq_original`; the reversed square is
   shown to be the inverse comparison. No monicity, inverse identities, or gluing
   are claimed. Both old proof dependencies that disappear are already listed in
   `No longer needed`: the coefficient-family Hom-stage node and the normalized
   E-module-category node. Removed the redundant direct `ProfinitePointPullback`
   proof import from the family module after a clean scratch compile. Testing its
   removal in the overlap helper instead produced the missing monoidality
   instance, so it remains there. Public imports supply public signatures or
   definition data; other added imports are proof-only. Opened
   `dag/units/sk-thm-properbasechange.json`: no realized statement or step is
   bypassed. The archived source path cited by these nodes is absent locally;
   read the current upstream `TwoColimit.lean` (Obj)/(Hom) proof-input paragraphs
   and checked the fully proved scalar calculation directly against the Lean
   statements, rather than claiming to have read the absent archive.

5. **DAG and records: pass after a textual repair.** Existing node changes are
   confined to `lean`, `proof`, `proof_deps` and `proof_origin`. The new node has
   its source, complete statement, three search types, provenance, chapter/unit,
   blueprint ancestry and verbatim Lean statement. Its dependency set is the
   union of its cited steps. The family node describes the actual coequalizer,
   fp-Hom and transpose route. Removed the redundant direct geometric-pullback
   dependency from the family node; the helper still records its own use.
   Corrected two stale sentences in the helper node that referred to a canonical
   identity model isomorphism and composition with its inverse: the actual model
   is definitionally the scalar extension, so neither such step occurs.

Second reading changed the redundant family proof import, its direct DAG
citation, the stale helper proof-description sentences, and this report. The
compiled proof bodies and the declared local-adjoint representation repair are
retained.
