## What changed

The second reader repaired the returned delivery's still-false finite-source step.
Short exactness alone cannot restrict a middle sheaf, since every F occurs in 0 -> F -> F.
`finite_cokernelPresentation_of_local_presentation` now assumes an explicit lifted short
exact module presentation with finitely generated kernel and a constant first sheaf.
Its conclusion is proved by the first worker's categorical kernel/cokernel calculation,
constant-sheaf pullback comparison, and biproduct comparison. The intermediate statement
change is recorded in coord/changes/finite_cokernelPresentation_of_local_presentation.md.
No definition changes, and no target statement changes.

The new `Sheaf.AlgebraicGeometry.ConstantExtensionPresentationLift` now also records finite
generation of T.X₁, as the finite free construction in Stacks Tag 093U ensures. Its docstring
and node explain this finite-ring step. This is local generator lifting without a cokernel
conclusion, strictly a part of the original argument, not a restatement of the item.

The cover theorem keeps its original signature and its proof, adjusting tuple extraction
for the finite-kernel field. The sole direct caller in
`Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation` keeps its original signature
and visibility; its proof obtains local lift data and passes it to the corrected theorem.
A proof-only import of the new lift module is added there. Existing imports in the adapted
caller were left in place under the forced-adaptation restriction.

## Proved and sorry left

Original unchanged hole closed by name:
`AlgebraicGeometry.Scheme.exists_constantExtension_cokernelPresentation_aux_cover`.
The repaired (different, true) statement of
`AlgebraicGeometry.Scheme.finite_cokernelPresentation_of_local_presentation` is completely
proved; this is a statement correction, not a proof of the old false assertion.
The private categorical helper `extension_presentation` is fully proved.

One new hole added:
`AlgebraicGeometry.Scheme.exists_constantExtension_presentation_lift`, in node
`lem-pc-constant-extension-presentation-lift`. This is the only sorry in the delivered set.
The cover theorem and the existing downstream
`AlgebraicGeometry.Scheme.exists_constantExtension_cokernelPresentation` depend on it.
The unchanged cover hole closed versus the one local-lifting hole added is a decomposition,
not a completed axiom-free proof. Removing the false finite-source hole is separately a
statement repair. No sorry is placed inside a definition and no data definition chooses
an arbitrary witness from an unproved existence assertion.

## No longer needed

The old finite node's `proof_deps` contained
`lem-pc-constant-extension-cokernel-presentation`: no longer used by the corrected categorical
step. Its actual dependency is `def-constructible-constant` plus proved Mathlib/upstream
exactness, kernel/cokernel, and constant biproduct APIs. This also removes the circular plan.
The old aux-cover node also depended on
`lem-pc-constant-extension-cokernel-presentation`; that unused parent dependency is removed
and replaced by the strictly smaller local-lifting step and constant-model computation.

The caller's old plan used `def-constructible-finite`, `def-constructible-constant`,
`lem-constructible-shortexact-local-lift`, `lem-constructible-constant-exact`, and
`lemma-constructible-flc-biproduct` directly. Its new proof uses the local lift node and the
corrected finite categorical step; constant and finiteness facts remain needed below.
No module is claimed pruned from the targets' import closure. No import was removed.

## Where the brief, the DAG or earlier work was wrong

The initial arbitrary-presentation lemma was false, as the independent return E2 reports.
The first repair added only hS, which is insufficient and did not match the node's claim
of finite constant outer terms. It also omitted the required statement-change and interface
change records. The second reader replaces this false route with the actual finite free
presentation/local lifts and proved categorical computation of Stacks Tag 093U.
The statement is corrected rather than claiming a proof of the old false lemma.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation` is unclaimed locally.
Its original final call supplies only arbitrary cokernel data where the corrected theorem
now first expects hS and then lifted short exact module data. That original fails to compile
against the changed item (the delivery tool performs the counterfactual check).
The necessary edits are: import the lift theorem for the proof; obtain its cover rather than
the arbitrary-cokernel cover; pass hS and h𝒰 i to the corrected theorem. No existing signature,
visibility, definition, or docstring of this adapted module changes. All other lines stay.

## New nodes

`lem-pc-constant-extension-presentation-lift` states the finite free local generator-lifting
step alone, with finite kernel, explicit source and complete natural-language proof. The
categorical pushout computation is proved separately, so this is a proper reduction. Search
of project/upstream sources and semantic/type searches found no existing exact declaration.
The existing CommRing SheafOfModules local-lift theorem has different coefficient categories;
generic local surjectivity and finite refinements are the intended bridge.
Upstream FreeLifting exists_lift_freeYoneda also has CommRing coefficients. Upstream
IsFiniteLocallyConstantSheaf.of_shortExact imports this extension route itself, so using it
here would introduce an import cycle; it does not eliminate the local-lifting obligation.

Change record: coord/changes/finite_cokernelPresentation_of_local_presentation.md.

## Statement corrected

`lem-pc-constant-extension-cokernel-aux-finite` now states the proved categorical reduction
from a lifted finite-kernel module presentation. The base has no DAG citers of this helper
(the actual Lean caller is recorded and adapted). Its old prose, proof, and proof_deps are
preserved in statement_change. The downstream extension theorem retains its exact statement.

## Second reading by G2

1. Compared every delivered existing Lean module with the repository. The cover and caller
signatures are byte for byte identical. The finite helper's deliberate correction has the
full interface-change record and node statement_change. No definition or target changed.
The new lift module is new on the base. Verdict: intentional changes fully recorded.
2. Compiled every delivered module through lcompile.py in import order. Only the named new
local-lift theorem contains sorry; no axiom, unsafe, opaque, implemented_by, extern, or hollow
definition. Axiom checks and the delivery probe confirm the allowed trust basis (including
sorryAx only through the documented lifting theorem). Verdict: categorical step proved;
upper cover remains conditional on the one split hole.
3. Read the new statement top to bottom, the Stacks source, and its docstring proof. Finite
ring plus finite free module implies finite kernel, also for noncommutative rings. Empty X
uses an empty cover; zero quotient uses the zero free presentation; nonempty X uses a
geometric stalk to recover finite generation of its constant model. Local surjectivity and
finite common refinement supply simultaneous lifts. The step neither assumes nor concludes
a cokernel presentation. Independent semantic/type/project searches found no matching lemma.
Verdict: true and a strictly smaller part of the argument.
4. Read the categorical proof and searched shorter upstream/Mathlib routes. Existing pushout
recognition APIs would still require the same kernel/epi argument, so retained the compiled
proof. Proof imports in the item and new module are correctly non-public; public imports
supply types in signatures. Checked sk-thm-properbasechange.realized: no unit statement or
step is bypassed. No old proof dependency is silently omitted from the pruning report.
Verdict: valid route below the unit level.
5. Opened all delivered nodes and checked verbatim Lean signatures, proof plans, proof_deps,
source, new-node metadata, and the caller's changed route. Corrected missing change records
and removed the false assumption that short exactness alone justifies finite replacement.
Verdict: DAG now follows the actual proofs and the single remaining local-lifting hole.

Second-reading changes: repaired the finite-source theorem and proved it; strengthened the
new lift step to carry finite kernel; adapted the caller and cover tuple extraction; wrote
change records, statement provenance, actual proof routes, and honest decomposition counts.

Validation completed: the dry run printed OK. All three delivered modules compile, and the
full delivery axiom probe passed. Explicit #print axioms in a scratch copy shows only
propext, Classical.choice, and Quot.sound for extension_presentation and the corrected
finite_cokernelPresentation_of_local_presentation. The cover and local-lift theorems show
those three plus sorryAx from the one named lifting hole. The tool's original-versus-adapted
caller counterfactual passed: original fails against the changed dependency, adapted compiles.
The delivery is CODEX because it repairs an interface and adds a node, not AUTO.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation
Original against changed dependencies failed:
```
/tmp/forced-adaptation-3r7x8gx9/lean/Sheaf/AlgebraicGeometry/ConstantExtensionCokernelPresentation.lean:65:58: error: Application type mismatch: The argument
  h𝒰 i
has type
  ∃ K L φ, Nonempty (cokernel φ ≅ (Etale.upperStar (ModuleCat Λ) (𝒰.f i)).obj S.X₂)
but is expected to have type
  ShortComplex.ShortExact ?m.157
in the application
  @finite_cokernelPresentation_of_local_presentation ?m.153 ?m.154 ?m.155 ?m.156 ?m.157 ?m.158 ?m.159 (h𝒰 i)

(with the modules compiled into /tmp/forced-adaptation-3r7x8gx9/.lbuild) [4.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
