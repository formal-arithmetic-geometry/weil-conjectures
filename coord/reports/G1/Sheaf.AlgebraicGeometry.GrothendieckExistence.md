## What changed

Replaced the sole hole in `AlgebraicGeometry.grothendieck_existence` with a compiling
reduction, preserving its complete signature and existing docstring. The main module now
constructs a common proper closed support for the two coherent modules: coherence gives
quasi-coherence and finite type, the support characterization supplies two annihilating
proper closed subschemes, and the product of their kernel ideals constructs a common one.
The proof establishes its properness through the finite-union and closed-subscheme
properties, and its annihilation equations by ideal containment on arbitrary opens.

The full-faithfulness part uses bijectivity on this fixed proper closed subscheme, then
proves the original unique-existence conclusion using subtype and function extensionality.
The existence part first obtains a proper closed subscheme annihilating every pushed term
of the system, then algebraizes on that subscheme. The three transport/support gaps are
public theorems in separate new modules with source, complete proof plans, and DAG nodes.
The parent node's proof and dependencies now describe this Lean reduction.

All four modules compiled in import order without warnings. No existing statement,
definition, target, or public import was changed. Only the sandbox was edited; the required
delivery tool performs its own dry-run packaging.

## Proved and sorry left

Closed the direct hole in `AlgebraicGeometry.grothendieck_existence`
(node `prop-weil-pbc-grothendieck-existence`). This is a decomposition, not a
sorry-free mathematical proof: one original hole closed, three lower holes added.
No direct sorry remains in the item's module. The hole-count net is -2 (one closed, three added),
so this delivery claims decomposition only, not a decrease in holes.

The new holes are exactly:

- `AlgebraicGeometry.grothendieckExistence_supported_hom`, node
  `lem-weil-pbc-grothendieck-existence-supported-hom`: bijectivity on one fixed proper
  closed subscheme annihilating both modules, before constructing that subscheme.
- `AlgebraicGeometry.grothendieckExistence_system_support`, node
  `lem-weil-pbc-grothendieck-existence-system-support`: existence of an annihilating
  proper closed subscheme for all pushed terms; its conclusion contains no algebraization.
- `AlgebraicGeometry.grothendieckExistence_supported_system`, node
  `lem-weil-pbc-grothendieck-existence-supported-system`: algebraization assuming one
  fixed proper closed subscheme already annihilates all terms; it does not obtain that
  subscheme from properness of first support.

Each new proof is exactly `:= by sorry`. No data is defined using sorry and no arbitrary
witness is selected to define an object. The common-support scheme is the actual closed
subscheme of the product ideal. The existential witnesses in the proof are eliminated
only to prove propositions.

Edge checks: empty X and zero modules allow the empty annihilating subscheme. If I is zero,
the systems are the constant restrictions and the support assertion reduces to the usual
scheme-theoretic support. If I is the unit ideal, I-adic completeness forces A to be the
zero ring, so X over Spec A is empty. Nonreduced support is retained by using annihilating
ideals rather than merely set-theoretic inclusion. The fixed-support lemmas assume
scheme-theoretic annihilation explicitly and do not infer it from underlying point sets.

## No longer needed

No mathematical dependency module is claimed pruned from the target import closure. The second
reader also replaced `ClosedSubsetProperOverBase` in the new SupportedHom module with the
narrower public `Mathlib.AlgebraicGeometry.Morphisms.Proper` import.
The Chow/projective/devissage argument is still needed for the system-support lemma;
the proper-case and dictionary arguments are still needed for the fixed-support lemmas.
They have moved below the new intermediate nodes, rather than being bypassed.

Removed these direct proof imports from the item (they remain in the indicated new
proof-dependency modules or their transitive imports):

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper`
- `Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre`
- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`
- `Sheaf.AlgebraicGeometry.FormalSystemsPushPull`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceProper`
- `Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules`
- `Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary`
- `WeilConjectures.AlgebraicGeometry.ChowLemma`
- `WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel`

No longer needed directly by the parent node, but retained in the three new nodes' plans:
`lem-weil-pbc-thickening-systems-dictionary`, `def-weil-pbc-coherent-formal-module`,
`lem-weil-pbc-closed-immersion-coherent-equivalence`,
`lem-weil-pbc-formal-completion-fully-faithful-proper`,
`prop-weil-pbc-grothendieck-existence-proper`, `lem-weil-pbc-noetherian-acc-quasi-coherent`,
`lem-weil-pbc-chow-noetherian`, `lem-chow-closed-model`,
`lem-weil-pbc-formal-systems-pullback`, `lem-weil-pbc-support-pullback-finite-type`,
`lem-weil-pbc-pushforward-coherent-on-open`, `lem-weil-pbc-grothendieck-existence-projective`,
`def-weil-proper-morphism`, `lem-weil-pbc-adic-complete-jacobson-radical`,
`lem-weil-pbc-reduced-induced-closed-subscheme`, `lem-weil-pbc-formal-systems-push-pull`,
`lem-weil-pbc-coherent-formal-modules-abelian`,
`lem-weil-pbc-formal-systems-proper-support-serre`.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The current interfaces do not directly compose the dictionary,
closed-immersion equivalence, and proper completion results into the explicit restriction
formulation. The remaining lower lemmas isolate exactly those transport steps and the
support induction, rather than treating the existing sorry dependencies as unavailable.
The parent plan used the intersection ideal for the common support; the product ideal is
equally valid, has its union-support identity directly in Mathlib, and is explicitly
constructed in Lean. This changes no unit statement or realized unit step.

The referenced local `literature/stacks-project/coherent.tex` is absent on this machine;
read Stacks Theorem 088E and Remark 088F at their official tag pages instead:
https://stacks.math.columbia.edu/tag/088E and https://stacks.math.columbia.edu/tag/088F.
LeanSearch returned HTTP Internal Server Error, recorded as unavailable. LeanFinder,
Loogle, Mathlib grep, local source searches and whole-blueprint searches ran; none found
an existing theorem for these support/transport statements. No change record is needed.

A dependency-graph traversal found the pre-existing two-node cycle
`lem-weil-pbc-sheaf-algebraic-structures-objects` ↔
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`. It is present in both the
unchanged repository parent closure and the updated closure. None of the three new nodes
or the updated parent has a dependency path back to itself. Reported here for the
maintainer; no unrelated node was changed.

## New nodes

`lem-weil-pbc-grothendieck-existence-supported-hom` is the fixed-common-support part of
088E's first paragraph. Its proof uses closed-immersion Hom identifications, proper
completion full faithfulness and the thickening dictionary. It does not construct the
common proper support; the main Lean proof does that.

`lem-weil-pbc-grothendieck-existence-system-support` is the support assertion explicitly
proved in 088E after its first paragraph. Its plan retains the original Noetherian
induction, Chow modification, projective extension, Jacobson-radical support argument,
proper pushforward comparison and Serre-subcategory conclusion. It does not algebraize
the original system.

`lem-weil-pbc-grothendieck-existence-supported-system` is the reduction in 088E's first
paragraph to proper existence once one proper closed support is known, with the natural
completion and restriction comparisons. It does not derive the support hypothesis.

## Second reading by G1

1. **Visible declarations.** I compared the delivered parent module with the repository version. The
`grothendieck_existence` signature and all existing declarations are byte-for-byte unchanged;
only its proof and proof-only imports changed. Verdict: pass.

2. **Compilation and axioms.** I compiled all four delivered modules in import order with
`lcompile.py --all`; each compiled without warnings. The three new declarations are named public
split theorems with documented source and proof plans, and the parent contains no `sorry`.
The delivery probe passed. A scratch-copy `#print axioms` check of the parent and all three
split declarations returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`;
there were no other axioms. The parent still depends on the lower holes. Verdict: pass.

3. **Statements and searches.** I checked the three split statements against Stacks Tags 088E
and 088F. `supported_hom` fixes one proper annihilating support, `supported_system` assumes one
such support for every term, and `system_support` only constructs that support. Each is strictly
smaller than the parent and has the required hypotheses and conclusion. LeanFinder, Loogle, Mathlib grep and repository searches found no duplicate of the three
split statements. The generic monotonicity helper did duplicate an upstream theorem, repaired below. Verdict: pass.

4. **Route and pruning.** The parent proof follows the node's four steps: finite-type coherence,
product support construction, fixed-support full faithfulness, then support plus fixed-support
existence. The product ideal is an explicit construction; no unit statement or realized step is
bypassed. Removed imports are proof-only imports now supplied by the three lower modules or their
transitive dependencies, as listed above. Verdict: pass.

5. **DAG agreement.** The parent node's `proof`, `proof_deps`, and `proof_origin` match the Lean
proof. Each new node has a matching Lean theorem, source, proof plan, searches, unit and chapter
fields. Verdict: pass.

I found that the private `idealOfOpens_mono` helper duplicated the generic upstream theorem
`Scheme.IdealSheafData.idealOfOpens_mono` in `Curve.DivisorIdealSheaf`. I removed the private
helper, added a proof-only upstream import, and used that theorem at the two annihilation steps.
Its import closure has no path to this item, and the target closure already imports it. I also
replaced the public `ClosedSubsetProperOverBase` import in the new SupportedHom module with
the narrower `Mathlib.AlgebraicGeometry.Morphisms.Proper` import needed by its signature. The parent DAG step now names the
upstream monotonicity theorem. No statement, definition, target, or unit route changed.
