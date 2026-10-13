## What changed

Closed `AlgebraicGeometry.affineBasisSections_resolution_homology_mono` without changing its
signature. Added proof imports of `ShortComplexSectionComparison` and the new, fully proved
`IntegerSectionAcyclicIncomingKernelImage` module. Private proved helpers establish naturality
of the adjunction-normalized section class comparison. Exact presheaf evaluation transports
this naturality square to the requested native module-valued homology map.

The shorter argument uses the existing short-complex section comparison as a tool from the
proper-base-change unit. It uses only cokernel and homology vanishing at V itself. The term
vanishing, the other affine basis members, and K-injectivity are unnecessary for the mono
assertion. The original signature and public imports are preserved. The unit record has no
realized statement or steps for this item; its higher route is unchanged.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.affineBasisSections_resolution_homology_mono`
(node `lem-sc-affine-basis-sections-resolution-homology-mono`).

Also proved the new declaration
`AlgebraicGeometry.Scheme.Modules.integer_section_acyclic_incoming_kernel_image`
(node `lem-sc-integer-section-acyclic-incoming-kernel-image`). All its helpers are proved.
No `sorry` remains in either delivered module; no holes were added or split off.
Independent `#print axioms` checks for both public theorems report exactly `propext`,
`Classical.choice`, and `Quot.sound`; neither reaches `sorryAx`.

## No longer needed

No original Lean import was removed: the two public imports provide the existing signature.
The following seven original planned dependencies are no longer used by this proof:

- `lem-pc-derived-limit-eventually-iso` / `Sheaf.CategoryTheory.DerivedLimitEventuallyIso`.
- `lem-pc-derived-limit-milnor-sequence` / `Sheaf.CategoryTheory.Triangulated.MilnorSequence`.
- `lem-sc-derived-k-injective-restrict-open` / `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`.
- `lem-weil-pbc-affine-opens-basis` / Mathlib's `Scheme.isBasis_affineOpens`.
- `lem-weil-pbc-injective-module-sheaf-H-acyclic` /
  `Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology`.
- `lem-weil-pbc-kinjective-hom-derived` / Mathlib's K-injective derived Hom comparison.
- `prop-pur-kinjective-resolutions-exist` /
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.

These are removed from this node's `proof_deps`, not assertions that no other target route
uses their modules. The inverse-limit and bounded-below Cech steps are unnecessary here.

## Where the brief, the DAG or earlier work was wrong

The module did not import its original seven proof dependencies, despite the standing brief's
statement that these imports were present. The DAG's bounded-below comparison step had no
stated dependency. The direct finite-degree proof avoids that gap.

The planned injective-module acyclicity node is stated for constant-coefficient small-etale
module sheaves; its current Lean signature is not a Zariski structure-module-sheaf statement.
It is not used in this delivery. No statement or definition was changed.

The dimension-shifting check is explicit: `0 -> H^j -> Q^j -> B^(j+1) -> 0` gives
H^1(B^(j+1)) = 0 from H^1(Q^j) = H^2(H^j) = 0. Then
`0 -> B^j -> Z^j -> H^j -> 0` gives H^1(Z^j) = 0.
For a zero differential the same sequence reduces to the supplied vanishing for the term;
for a zero complex or empty V all its objects and cohomology are zero. Negative degrees cause
no endpoint case, since the index set is the integers.

## New nodes

`lem-sc-integer-section-acyclic-incoming-kernel-image`, in
`dag/nodes/sec-picard-framework/`, supplies first-cohomology vanishing of incoming kernels and
images from the original cokernel and homology hypotheses. This is fully proved using the
existing module/ordinary cohomology comparison, exact restriction and the long exact sequence.
It is a strictly smaller finite-degree algebraic step and introduces no resolution or limit.
Searches were run with LeanSearch (unavailable), Loogle and grep; the existing nonnegative
incoming-acyclicity theorem requires termwise module-cohomology vanishing and induction from
zero, so does not supply this integer-indexed cokernel argument. Blueprint searches for
“cokernel cohomology” and “kernel.*image” found no matching blueprint node.
The sources read were cohomology.tex, lemma-alternating-cech-complex-complex-ss (08C2),
and derived.tex, lemma-higher-derived-functors (015B), together with the existing
short-complex section comparison module and its 01E4 normalization.
No change records or forced adaptations were needed.


## Second reading by A4

1. **Interfaces: pass.** Compared the delivered item with the repository file using
   `diff -u` and compared the full theorem signature as text: byte-identical. The
   affine-open hypothesis, integer degrees, K-injective target, quasi-isomorphism,
   all three basiswise positive-cohomology assumptions, and native module-valued
   homology-map conclusion remain unchanged. Both original public imports remain.
   The only new public declaration is the fully proved incoming-acyclicity lemma;
   no existing definition, statement, or visibility changed. There are no change records.
2. **Proof and axioms: pass.** Compiled both modules in import order with `lcompile.py`:
   no errors or warnings. Scanned both sources: no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, or kernel-check bypass. Scratch copies with
   `#print axioms AlgebraicGeometry.affineBasisSections_resolution_homology_mono`
   and `#print axioms
   AlgebraicGeometry.Scheme.Modules.integer_section_acyclic_incoming_kernel_image`
   each report exactly `propext`, `Classical.choice`, `Quot.sound`. Removed the scratch
   copies afterward. The private comparison is explicitly constructed from the
   sheafification adjunction and its counit; it chooses no arbitrary witness from
   an unproved existence theorem. The comparison equivalence in the new lemma is
   used only to prove a proposition about zero objects, not to define data.
3. **New statement: pass; no split-off holes.** Read Tag 08C2's assumptions (3)(b),(c)
   in `scratchpad/cohomology.tex` and Tag 015B's long exact sequence in
   `scratchpad/derived.tex`, together with `ModuleCohomologySourceComparison` and
   `ShortComplexSectionComparison`. The new lemma matches its node: arbitrary scheme
   and open, integer complex, ordinary positive cohomology of cokernels and homology,
   and first module cohomology of the incoming kernel and image. Checked the shift:
   the opcycle sequence gives vanishing for the image of d^j from degree-r cokernel
   and degree-(r+1) homology vanishing; the boundary sequence gives cycle vanishing.
   Incoming kernel at p is Z^(p-1), incoming image is B^p. Empty opens, zero complexes,
   and zero differentials introduce no missing case; integers have no bottom endpoint.
   Repeated searches with different terms: LeanFinder query about positive derived
   cohomology of opcycles, Loogle for `mapHomologyIso_inv_naturality`, grep for
   `cycles.*IsZero|IsZero.*cycles|homEquiv_naturality_left_square`, and repository
   searches for incoming acyclicity and opcycle cohomology. Results give the Mathlib
   naturality infrastructure already used, not this incoming-acyclicity assertion.
   The existing `SectionAcyclicIncomingKernelImage` is indexed by naturals and uses
   termwise module-cohomology vanishing and bottom-degree induction, so cannot replace
   this integer-indexed cokernel argument. The new lemma is strictly smaller than
   the item: it has no resolution, comparison map, or homology-monicity assertion.
4. **Route and pruning: pass.** Read the actual naturality calculation: counit
   naturality supplies the short-complex square, inverse homology-comparison naturality
   and adjunction naturality transport it. The source comparison and quasi-isomorphism
   induce an invertible composite; cancellation gives a mono without assuming the
   target comparison invertible. Exact presheaf evaluation then transports that mono
   to native section-complex homology. The generic short-complex comparison is a tool,
   not a replacement of a unit step. `sk-thm-picard-duality.json` has no realized
   statement or step naming this item, and no unit record was changed. All seven old
   proof dependencies appear under `No longer needed`; no claim is made that their
   modules are globally unreachable. Proof-only imports are plain imports; the new
   module's public imports supply its signature's cohomology notions. No shorter
   existing theorem was found. The harmless elimination of the supplied termwise
   subsingleton instance does not contribute a mathematical premise to the argument.
5. **DAG: pass.** Existing node changes are exactly `proof`, `proof_deps`, and
   `proof_origin`. Its two proof dependencies are the new incoming-acyclicity result
   and the short-complex comparison actually applied. The new node's proof follows
   the cohomology comparison, exact restriction, enough injectives, and long exact
   sequences in the Lean; its `proof_deps` is the union of step `uses`. Its source,
   searches, creation record, blueprint ancestry, chapter/unit, and verbatim Lean
   statement are present. No hole was closed merely by moving it to another theorem.

Second reading changed the item's theorem docstring: replaced the obsolete truncation,
tower, and Milnor proof with the dimension-shifting and naturality argument actually
formalized. Also corrected the axiom-status sentence above and recorded this independent
review. No proof, signature, import, or node needed repair. One original hole closed;
zero holes added; the additional theorem is fully proved.
