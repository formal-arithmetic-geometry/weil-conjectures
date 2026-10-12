## What changed
Repaired return 5/6 by reviewer X-97d5b (head 97d5b9f2e): removed the unused
`lem-pc-localized-pullback-perfect-model` from all three proof-step `uses` arrays and
from `proof_deps`, and corrected the pruning claim below. Lean proofs are unchanged.
Repaired the landing rejection by removing the private duplicate declarations
`AlgebraicGeometry.Scheme.localizedPullbackFree` and
`AlgebraicGeometry.Scheme.localizedPullbackStrictlyPerfect`, together with the now unused
`localizedPullbackUnitIso` helper. The target now applies the existing proved
`AlgebraicGeometry.localizedPullbackStrictlyPerfect` from
`Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`. The proof-only `import all` makes this
private theorem accessible without changing any visibility in its defining module.
Return H4 by X-1a79a is repaired: deleted the duplicate private
`AlgebraicGeometry.Scheme.moduleIsoEquivalence` definition and added proof-only
`import all Sheaf.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare`. Existing calls
now reuse that module’s private definition. Added
`lem-pc-scheme-iso-derived-restriction-square` to the first proof step’s uses and
`proof_deps`, and updated the change record. The restriction-square construction
and target signature are unchanged. The second reader
scoped `backward.isDefEq.respectTransparency = true` to the remaining two declarations to avoid
slow elaboration under the library's global false setting; no statement or proof term
construction was rewritten. Change record:
`coord/changes/scheme-iso-local-transport-proof-scope.md`. Updated the
node's proof and proof dependencies to record this reuse. No other module is adapted.

## Proved and sorry left
Closed: `AlgebraicGeometry.Scheme.scheme_iso_local_perfect_transport`, one of one original
holes. No sorry remains in this module and no hole is added or split off. The reused
strict-perfectness helper is proved. The concrete local model and restriction square
remain explicit constructions; no witness is chosen from an unproved existence theorem.

## No longer needed
Removed the duplicate `moduleIsoEquivalence` definition, reusing the existing private
definition from `SchemeIsoDerivedRestrictionSquare`. Also removed the duplicate
finite-free and strict-perfectness proofs and their unit helper.
Removed proof imports `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` and
`Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`; the latter is reached through
the new proof import and its concrete localized-pullback definition is still used.
Relative to the repository module, removed `Sheaf.AlgebraicGeometry.DerivedCategory`
because it is publicly imported by `PerfectComplex`.
Earlier rounds also removed redundant proof imports
`Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
`Mathlib.CategoryTheory.Adjunction.Unique`.
The unlanded proposals `new-scheme-iso-local-perfect-transport-model` and
`new-scheme-iso-local-perfect-transport-iso` remain discarded.
Pruned proof dependency `lem-pc-localized-pullback-perfect-model` from all three
proof-step `uses` arrays and from `proof_deps`: no delivered Lean proof invokes its
model-comparison theorem. Its module's concrete localized-pullback definition remains
used through a transitive import. The remaining listed proof dependencies are used;
`lem-pc-derived-pullback-perfect` records the reused strict-perfectness helper's module,
although its main perfectness theorem is not used.

## Where the brief, the DAG or earlier work was wrong
The returned delivery additionally duplicated the private `moduleIsoEquivalence`
definition from `SchemeIsoDerivedRestrictionSquare`; return H4 identifies this exact
duplicate. It is now deleted and reused through `import all`. Earlier returns identified
two already proved private helper theorems in `DerivedPullbackPerfect`. Their privacy does not require a fresh proof: Lean's
`import all` permits reuse. Both duplicates have been removed, rather than renamed.
The obsolete second-reading endorsement has been removed for a fresh independent reading.
Fresh validation: deliver3.py --no-push printed OK for repaired commit 45588e5778.
Local compilation, the delivery axiom probe and preflight passed except for the fresh
second reading, which the dispatcher’s next worker writes. Nothing was pushed.
Two preceding lcompile attempts timed out at 60 seconds while the machine load exceeded
250; the subsequent delivery compile and checks passed under the same limit. The target
signature is byte-for-byte unchanged, Lean lines satisfy the 100-character limit, and
the union of proof-step uses equals proof_deps. Previous validation and the previous
second reading do not endorse this repaired version.
The earlier proposed restriction-comparison split was false because it allowed an
unrelated local model; the repaired proof continues to construct the actual pullback.
The unit record has empty realized statement and step lists; no unit route is bypassed.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations and signatures.** Compared the delivered module with the repository version. The public theorem `AlgebraicGeometry.Scheme.scheme_iso_local_perfect_transport` has the same signature and docstring byte for byte; only proof infrastructure, proof-only imports, and scoped elaboration commands were added. No target statement or public definition changed.

2. **Compilation and axioms.** Compiled the sandbox module with `lcompile.py --all`; it completed successfully with no errors, warnings, or `sorry`. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for the private helper and the target theorem. No forbidden declaration forms occur.

3. **Statements and reuse.** The private `localRestrictionSquare` is an intermediate construction, with a complete source and proof explanation in its docstring, and is used to derive the target. The proof reuses the existing strict-perfectness and module-isomorphism constructions via proof-only `import all`; it does not restate their declarations or add hypotheses to the target. The concrete complex is `Modules.localizedPullback s.hom V`, so no arbitrary witness is selected from an existence theorem.

4. **Pruning and route.** Removed duplicate finite-free, strict-perfectness, unit-isomorphism, and module-equivalence helpers from the earlier delivery. The remaining imports are proof-only and correspond to declarations actually used by the proof. The unit route remains the localization comparison followed by strict-perfect transport and composition with the supplied local model isomorphism; the unit record is unchanged.

5. **DAG agreement.** Updated the node proof steps, `proof_deps`, and `proof_origin` to record the restriction-square construction and reused strict-perfectness theorem. The node statement and target interface remain unchanged. The required change record documents the scoped commands and imports.

The second reading changed only this report: it records the checks above and confirms the repaired proof scope. No additional theorem, definition, split-off hole, or DAG node was needed.

## Second reading by C3

1. **Visible declarations and signatures.** Compared the delivered module against the repository version with `diff`. The target theorem signature and docstring are byte-for-byte unchanged; edits add only proof-only imports, local opens/attributes, scoped elaboration options, and private proof infrastructure.

2. **Compilation and axioms.** `lcompile.py --all` compiled the sandbox module successfully. The source contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The existing axiom probe records only the permitted axioms (`propext`, `Classical.choice`, and `Quot.sound`) for the helper and target.

3. **Statements and reuse.** `localRestrictionSquare` is a strictly intermediate construction with a source and complete proof explanation. It uses the existing private `moduleIsoEquivalence` and strict-perfectness theorem through `import all`; no duplicate declaration or weakened target was introduced. The transported complex is concretely `Modules.localizedPullback s.hom V`, so no arbitrary witness is selected.

4. **Pruning and route.** The delivered proof removes the earlier duplicate helpers and unused proof imports. The remaining proof-only imports support declarations actually invoked. The localization/restriction comparison, strict-perfect transport, and composition route matches the unit route; no unit step is bypassed.

5. **DAG agreement.** The node's proof steps, dependencies, and origin match the imports and declarations used by the Lean proof. The target node remains `split` only as its pre-existing DAG status; this delivery closes its sole module hole and adds no split-off theorem or node.

The second reading changed only this report. No Lean source, node, or change record required repair.
