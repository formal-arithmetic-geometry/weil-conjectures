## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_puncturedMap_basicOpen_appTop_ringEquiv`
by a complete Lean proof from two strictly smaller geometric chart statements.
The existing signature and public imports are unchanged.

The proof identifies the actual nested model chart with a principal open of
`Spec D.matchingRing`. A proved private helper transports Mathlib's affine
principal-open localization along the open immersion, with its exact algebra
map. Another proved helper computes the chart image. The main proof combines
power lifting and kernel torsion into the localization axioms for the target,
then applies `IsLocalization.bijective` and `RingEquiv.ofBijective`. In
particular, the claimed equality of underlying functions is reflexivity;
no unspecified ring equivalence is chosen.

Added proof-only imports of `PuncturedMatchingChartPowerLift` and
`PuncturedMatchingChartKernelTorsion`, two new modules with one public theorem
each. Updated the original node's proof, proof_deps and proof_origin to match.
No definition, target signature or existing public interface changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_puncturedMap_basicOpen_appTop_ringEquiv`
(node `new-sbc-punctured-completion-matching-affine-sections-comparison`).
There are no sorries left in the assigned module. Its two private helpers
`principalOpen_sections_localization` and `principalOpen_image` are proved.

Added these two holes, each exactly a whole public theorem proof:

- `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_power_lift`
  (node `lem-sbc-punctured-matching-chart-power-lift`): every target chart
  section has a power multiple in the image of the unlocalized matching ring.
- `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_kernel_torsion`
  (node `lem-sbc-punctured-matching-chart-kernel-torsion`): a matching-ring
  element vanishing on that chart is killed by a power of the base element.

This is a decomposition: one upper hole closed and two lower holes added,
not an unconditional proof or a net decrease in holes. Neither new theorem
asserts bijectivity or a ring equivalence between the section rings of the
assigned theorem. One proves denominator surjectivity from the unlocalized
ring; the other is only its kernel zero criterion. The Lean proof combining
them also proves the source localization and all algebra-map compatibility.

All three delivery modules compile together using `lcompile.py --all`, with
no errors or warnings. The dry-run delivery check supplies the final static,
signature and axiom checks.

## No longer needed

None: no baseline import, node or module was removed. The sole original
public import is needed for the unchanged statement and actual constructions.
The generic formal-gluing localization and chart-power-lift modules belong
to the remaining geometric lemmas' proof plans, rather than to the combining
proof; they have not been pruned. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node's only proof dependency was the definition of the matching
ring. That definition supplies the constructions and base equations, but
neither geometric chart lifting nor the principal-power kernel criterion.
The two new nodes expose precisely these missing obligations. The algebraic
formal-gluing declarations already exist, but their `FormalGlueing.Data`
arguments are not definitionally the scheme-theoretic matching-ring data.
The affine chart construction, sheaf equalizer identification and map
compatibility remain part of the two explicitly stated geometric obligations.

Source read: Stacks Tags 0BLH (proof, affine chart construction), 05ER (proof,
localized chart comparison using 05EP and 05EQ), and 05EU (tensor/algebra
compatibility), from their official tag pages. The source files are absent
from this machine's read-only literature directory. No new document was needed.

Mathlib searches were run through msearch: LeanSearch returned an internal
server error and is recorded as unavailable; LeanFinder found ordinary
scheme-section numerator/kernel lemmas; Loogle found `IsLocalization.bijective`;
Mathlib grep found no formal-gluing or matching-ring theorem. Repository rg
found the existing module-gluing localization and chart-power-lift statements.
Whole-blueprint searches for formal glueing, matching and punctured found no
duplicate of either new geometric claim.

Edge cases checked mathematically before stating the new lemmas: f=0 and
nilpotent f give empty charts; power lifting is then the lift of the unique
zero section, while a power annihilating f annihilates every matching element.
If U is empty (including a field base), hf forces the same nilpotent case.
Zero chart rings and zero completed components are allowed; neither statement
uses a nonzero denominator or a domain hypothesis. For a nonnilpotent f the
finite generating family can include f since hf implies f lies in the maximal
ideal, so the formal-gluing chart comparison applies to that particular chart.

The ancestor helper returns None because the original nodes' created.item
fields name modules rather than node IDs. The new nodes use the actual
blueprint ancestor `sbc-thm-spreading-finite-etale-galois`, recorded by the
matching-sections definition and finite-gluing parent, with an explicit via
path. Existing fields outside the permitted proof fields were not edited.
The generic algebraic formal-gluing nodes are tools from sk-thm-p1 used in the
new proof plans: they are not a replacement route for the spreading unit.

## New nodes

`lem-sbc-punctured-matching-chart-power-lift`, in
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedMatchingChartPowerLift`, states only
denominator lifting for the actual matching projection. Its docstring gives
the finite affine-chart construction, H0 equalizer identification and use of
the existing formal-gluing power-lift theorem. This isolates the surjectivity
part of the localized comparison.

`lem-sbc-punctured-matching-chart-kernel-torsion`, in
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedMatchingChartKernelTorsion`, states
only the principal-power kernel criterion for that projection. Its proof plan
uses overlap injectivity and a maximum of finitely many killing exponents,
or the existing H0-localization injectivity and zero criterion. It needs no
chart lifting. Both nodes inherit the original chapter and unit, carry the
verbatim Lean signatures, actual search results, source and complete proof
in words. There are no change records because no existing interface changed.

## Second reading by P1

1. Interface preservation: diffed the delivered comparison module against the
   repository file and compared the original theorem signature byte for byte.
   The entire signature, all hypotheses (Noetherian local A, punctured U,
   finiteness of q and s, supplied overlap datum D, and D(f) contained in U),
   and the equality with the actual restricted appTop function are unchanged.
   No existing definition was edited. The only import additions are ordinary
   proof-only imports. The existing node differs only in proof, proof_deps and
   proof_origin. Verdict: pass. Restored the original public theorem docstring;
   its replacement was unnecessary for this delivery.

2. Proof and trust: independently compiled all three modules in import order
   with lcompile.py --all, without errors or warnings. Read both private
   helpers and the complete localization-axiom construction. In the first
   helper, he proves the exact B-algebra-map equality needed to transport the
   localization along appIso; it is not just an abstract ring isomorphism.
   The image helper uses hf to discard the intersection with U and computes
   the principal open of D.baseMap(f). In the main proof, map_units is obtained
   from the source localization, surj uses the power-lift equation, and
   exists_of_eq applies kernel torsion to b-c. IsLocalization.bijective and
   RingEquiv.ofBijective give the claimed map, with equality by reflexivity.
   Scratch copies with #print axioms show only propext, Classical.choice and
   Quot.sound for the helpers, and additionally sorryAx for the main theorem
   and each new open theorem. The two reported open theorems are the only
   textual sorry occurrences; no data, axiom, unsafe, opaque, implemented_by
   or extern was added. Verdict: pass as a decomposition, not a completed
   axiom-free proof of the original statement.

3. Split statements: read the official Stacks pages
   https://stacks.math.columbia.edu/tag/0BLH (affine-chart construction),
   https://stacks.math.columbia.edu/tag/05ER (localized H0 comparison) and
   https://stacks.math.columbia.edu/tag/05EU (tensor/algebra compatibility),
   and the Lean statements of FormalGlueing.h0_chart_power_lift and
   FormalGlueing.exists_unique_bijective_h0_localization. Including f in a
   finite generating family is legitimate: hf and hU imply f is in the
   maximal ideal. Each Y-chart and every intersection is affine because it
   is the preimage under the finite q of a principal affine base chart.
   E is affine because s is finite. Restricting the one supplied overlapIso
   gives the prime/chart identifications, and common restrictions on triple
   intersections give the cocycle; no extra chosen geometric data is assumed.
   Sheaf gluing identifies the compatible chart coordinates with Gamma(Y),
   and compatibility with Gamma(E) is exactly the pullback defining B.
   The target chart is q^{-1}(D(f)) by puncturedMap_over; on sections its
   projection is psi composed with rho by the defining first projection in
   fromPunctured and the Spec-Gamma adjunction. Thus scalar multiplication
   in both statements is exactly multiplication by the displayed baseMap(f).
   The power-lift statement is only denominator surjectivity. The kernel
   statement is only the zero criterion: overlap injectivity kills the prime
   coordinate after inverting f, chart overlap equations kill every other
   coordinate there, and finitely many exponents have a common maximum.
   Neither assertion restates bijectivity of psi. Both are true and strictly
   smaller than the original ring-equivalence claim. Checked f=0, nilpotent f,
   empty U (in particular a field base), empty Y/E, and zero chart rings:
   lifting takes the zero element on empty charts; a nilpotence exponent
   kills every matching element in the kernel claim. No regularity,
   nonzero denominator or domain assumption is being used.
   Independent msearch queries used different wording: LeanFinder for
   localization of the pullback ring of punctured and completed sections,
   Loogle for IsLocalization.bijective, and grep for the compact-open
   numerator/kernel and localization-transport lemmas. Results were only
   ordinary scheme localization tools and the exact combining theorem.
   Repository and upstream rg searches found no duplicate; the completed
   matching-map kernel lemmas concern the completed tensor comparison,
   not this punctured chart projection. The existing algebraic H0 lemmas
   do not supply the geometric equalizer and section-map identifications.
   Closing those identifications requires substantial additional Lean work,
   so neither open geometric statement can be closed in a few-minute repair.
   Verdict: pass; each has a source, full proof in words and matching node.

4. Route and pruning: the proof starts with Mathlib principal-open
   localization, then uses the two strictly smaller geometric claims and
   Mathlib IsLocalization.bijective. Every delivered import is needed for
   its signature or the combining proof. The original proof_deps contained
   only def-sbc-punctured-completion-matching-sections, which is still used;
   hence no old dependency or module is omitted from No longer needed.
   Read dag/units/sk-prop-input-spreading.json: realized has no nonempty
   statement/step entry bypassed here. The chart comparison stays beneath
   the finite-gluing input in the existing spreading route. The generic
   formal-gluing lemmas in sk-thm-p1 are tools for the new geometric proof
   plans, not replacements for a spreading-unit statement or step.
   Verdict: pass, no pruning.

5. DAG agreement: checked each new node's Lean signature verbatim against
   its module, the union of proof-step uses against proof_deps, its source,
   creation record, chapter/unit, blueprint ancestor/via path and recorded
   searches. The original node describes both proved helpers, all three
   localization axioms and the actual RingEquiv construction. The new nodes
   describe respectively the geometric power-lift and kernel obligations
   left open in Lean; their names, claims and proof origins agree.
   Verdict: pass. No node statement or definition was changed.

Second-reading changes: restored the original public theorem docstring and
added this independent review. No proof, signature, definition, import or
node repair was necessary. The accounting remains one original hole closed
and two new holes added (net -1), with no module pruned.
