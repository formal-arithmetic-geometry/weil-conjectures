## What changed

Replaced the only sorry in `WeilConjectures.SixFunctors.Integral.BaseChange`,
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`, with a compiling
reduction to exchange over the spectrum of an algebraically closed field. The proof
forms the inner pullback of the base-changed integral morphism and the outer pasted
square, invokes geometric-point exchange twice, cancels the inner exchange and the
composition isomorphisms using the horizontal pasting identity, and detects the original
exchange on all geometric stalks. The lifted stalk comparison avoids an extra manual
universe-lift conversion. The derived theorem's signature and proof are unchanged.

Added three proof-only imports: `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange`,
`WeilConjectures.SixFunctors.BaseChange.Pasting`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`. Added the geometric-point
statement in its own module, with its source, complete proof in words, and DAG node.
No existing public statement, definition, universe, or public import changed. No
Challenge target changed. Local compilation of both modules succeeds without warnings.

The remaining special case is strictly narrower: its base is Spec Omega and its exchange
is one component at F. The delivery proves the passage to arbitrary base schemes and
all components through pullback, pasting, cancellation, stalk comparison, and
conservativity. This is not an application of a renamed unrestricted theorem.

## Proved and sorry left

Reduced `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`
(node `lem-sbc-integral-underived-exchange`): its proof has no sorry.
The previously proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`
still compiles against it. Neither is yet axiom-free transitively, since the new
geometric-point input remains open.

The only sorry in the delivery is
`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isIntegralHom_geometricPoint`,
in `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange`, node
`lem-sbc-integral-geometric-point-exchange`. Its whole proof is `:= by sorry`.
It assumes no torsion, finite type, surjectivity, or residue-field algebraicity.
The documented argument computes the source stalk over a strict henselization, uses
integrality to obtain a henselian pair (B,mB), restricts to Spec(B/mB), then extends the
separably closed residue field to Omega. Its unit-square-counit calculation identifies
these restrictions with the actual exchange map. Edge cases checked in words: empty
fibre and zero sheaf give zero modules; identity squares give invertible comparison
maps; infinite integral fibres are not treated as finite products; transcendental
Omega is handled by the separably closed field-extension sections theorem.

## No longer needed

None of the two original public imports was removed: the derived theorem uses both.
All three added proof imports are used by the compiled proof. No original DAG proof
edges exist for this module to prune, and no module is claimed globally unreachable.
The full proper underived exchange theorem and its proper geometric-point statement
are not needed or imported. Neither are finite approximation, finite direct-image
continuity, or the finite-only product stalk formula needed by the assembly delivered
here. They are not claimed removed from the target closure, since the original Exact
import still reaches the finite theory.

The remaining geometric-point proof plan uses the affine instance of the henselian
proper degree-zero comparison as a tool: apply it to the identity of Spec B, which is
proper even when the original integral morphism is not of finite type. This retains
the original module's strict-henselian fibre route and does not substitute the global
proper base-change theorem. The unit sk-lem-universal-datum has empty realized entries;
no unit statement or step was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

No node has `lean.module = WeilConjectures.SixFunctors.Integral.BaseChange`, and neither
source theorem has a blueprint tag. The similarly named
`lem-weil-pbc-integral-base-change` is the ring-theoretic tensor-product integrality
lemma, not the etale exchange theorem. Added a node for the existing theorem being
reduced as well as the new special-case node, so the compiled assembly is recorded.

The relevant literature files listed as obtained are absent from this read-only clone.
Read the official Stacks pages for Tags 0EYP, 03Q9, 09XK, 09ZH and 0A3I, and compared
their hypotheses with the existing Lean statements. LeanFinder and Loogle returned
actual results; LeanSearch returned Internal Server Error, recorded as unavailable
in the search log and node records, not as evidence of absence. Local source search
found the analogous proper assembly, but it cannot apply to arbitrary integral f.

## New nodes

`lem-sbc-integral-underived-exchange`,
`dag/nodes/sec-smooth-base-change/lem-sbc-integral-underived-exchange.json`, records the
existing source declaration and the actual compiled three-step argument. It belongs
to the integral exchange identity in the proof of blueprint sbc-lem-bc-integral-base,
unit sk-lem-universal-datum.

`lem-sbc-integral-geometric-point-exchange`,
`dag/nodes/sec-smooth-base-change/lem-sbc-integral-geometric-point-exchange.json`, records
the remaining geometric-point special case and its strict-henselian proof. It is stated
in `lean/Sheaf/AlgebraicGeometry/IntegralGeometricPointExchange.lean`. Its proof dependencies
name the existing stalk formula, integral-over-henselian-pair theorem, henselian
restriction theorem, separably closed field-extension sections theorem, stalk
comparison, and geometric conservativity. No change record is needed: the existing
module's interface is unchanged and the new declaration is imported only for proofs.

## Second reading by R1

1. Interface: PASS. Read both complete delivered modules and diffed BaseChange against
   the repository. Both existing theorem signatures, section variables, universes,
   definitions, and public imports are byte-for-byte unchanged. The derived proof is
   unchanged. The three additions to BaseChange are proof-only imports.
2. Proof and axioms: PASS as a reduction, not an axiom-free completion. Both modules
   compile without errors or warnings through lcompile.py --all. A scratch copy with
   #print axioms for all three delivered theorems reports only propext, Classical.choice,
   Quot.sound, and sorryAx. The only explicit sorry is the reported named geometric-point
   theorem, with source, full proof docstring, and node. There are no new definitions or
   forbidden axiom/unsafe/opaque/implemented_by/extern constructs. The original theorem
   now contains a genuine pullback/pasting/cancellation/stalk argument.
3. Split statement: PASS. Checked the arbitrary algebraically closed field and arbitrary
   integral morphism hypotheses against Stacks Tags [0EYP](https://stacks.math.columbia.edu/tag/0EYP),
   [09XK](https://stacks.math.columbia.edu/tag/09XK),
   [09ZH](https://stacks.math.columbia.edu/tag/09ZH), and
   [0A3I](https://stacks.math.columbia.edu/tag/0A3I). Applying the existing henselian
   degree-zero comparison to the identity of Spec B supplies precisely 09ZH without
   assuming f proper. Empty fibres and zero sheaves give zero section modules; identity
   squares give the adjunction comparison isomorphism. Infinite integral fibres require
   no finite-product formula. A transcendental Omega is allowed by 0A3I. Forgetting module
   structure reflects the resulting isomorphism. This special case does not restate the
   unrestricted item. Repeated searches with inverse-image/direct-image and residue-field
   terminology (LeanFinder), component-isomorphism patterns (Loogle), and source rg found
   no duplicate. One Loogle query used an unknown IsIntegralHom identifier and was not
   counted as evidence of absence; the replacement returned NatIso.isIso_of_isIso_app,
   already used in the proof. Search results are in searches.jsonl. The related proper
   theorem requires properness and cannot close this integral case. Closing the remaining
   special case requires formal stalk/restriction identifications beyond a short repair.
4. Route and pruning: PASS. Read the strict-henselian source route and the analogous proper
   assembly. All added imports supply declarations actually used; the original Exact and
   Derived imports remain necessary for the derived theorem. There were no original DAG
   proof dependencies to remove. No longer needed is complete: pruned none. The unit
   sk-lem-universal-datum and its realized fields are unchanged; the integral exchange
   identity remains on its route. Cross-unit stalk and henselian results are generic tools,
   not replacements of the unit's argument.
5. DAG: PASS after metadata repairs. Checked every dependency exists, its Lean record,
   and equality of proof_deps with the union of the proof steps' uses. The assembly node
   matches the two geometric-point applications, pasting cancellation, lifted stalk
   comparison, and geometric conservativity. The remaining node records the correct
   strict-henselian argument, rather than claiming that it is Lean-proved.

Changed only metadata and this review report: recorded both Lean signatures verbatim,
clarified that the underived declaration already exists in the source while keeping
lean.existing=false (the delivery schema requires false when lean.file is delivered),
and recorded cross-unit
lemmas as tool_uses. No Lean proof or statement needed repair. Removed the scratch axiom
probe from the delivery. The original module has two declarations with sorry-free proof
bodies (one newly reduced, one already proved), and one new named theorem remains split off;
the delivered results still depend transitively on sorryAx.
