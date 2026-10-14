## What changed

Repair of return X-10c6b: removed the three duplicate module-level helper
statements `homologyBiprodEquiv_apply`, `homologyBiprodEquiv_lift`, and
`homologyBiprodEquiv_desc_neg`, together with their private equivalence definition.
Exactness now constructs its section-specific equivalence locally and uses Mathlib's
biproduct comparison, homology composition, lift projection, and additive-map APIs
inside the actual restriction-pair and restriction-difference calculations.
The SectionComparison helpers are private, so importing that module does not
make them available. Its public theorem compares inverse-image coefficients and
cannot supply the fixed prescribed comparisons used here. No visibility or
signature in that unheld module is changed. No duplicate theorem is redeclared,
and this repair adds no imports or holes. Superseded reader sections are removed.
The repaired exactness file compiles without warnings; the landing
`tools/import_prune_check.py` check passes (exit 0) against an absent old file,
so the duplicate-statement refusal is resolved for this new module.

Repair of return H2 / point 6 (reviewer X-9c4a7): restored the parent node's
`lean.statement` byte-for-byte from the repository's multiline string.
Only this recorded string is restored; the Lean theorem and its proof are unchanged.


Repair of return B2 (reviewer X-d6157): made the canonical-boundary-naturality
node statement self-contained by introducing the schemes, morphism, covering
opens, intersection morphism and its square, coefficient sheaves and morphism,
injective resolutions, and prescribed normalized comparisons locally. The
replacement is exactly the requested text; the remainder of the statement and
all other node fields are unchanged. No Lean declaration was changed by this repair.

Replaced the hole in `AlgebraicGeometry.Etale.tailOpenCompatibleBoundaries`
with fixed resolution boundaries, exactness on both sides, and naturality for
all stage transitions and cone legs. Its signature and three public imports
are unchanged. Proof imports provide the local boundary exactness and
naturality APIs. The two map definitions are expanded directly to identify the actual
transition and leg maps with pullback followed by `openSquareCoefficient`.

Four new modules supply the reduction:

- `EtaleMayerVietorisCanonicalBoundary` constructs the homology boundary,
  conjugated by normalized section comparisons. Its named-intersection
  section complex is constructed directly on the specified open; its
  short exactness is proved. The irreducible fixed-boundary interface
  fixes a resolution and a comparison determined on cocycles. Separate typed
  constants hide the resolution instance construction and normalized comparison
  choice from their uses in the boundary.
- `EtaleMayerVietorisCanonicalBoundaryExact` proves exactness by transporting
  Mathlib's homology exactness through the normalized restriction comparisons
  and the homology biproduct equivalence. Its difference input is an ordinary
  function with the prescribed pointwise restriction formula; no algebraic
  structure on that input is needed for exactness.
- `EtaleMayerVietorisCanonicalBoundaryNaturality` proves boundary naturality
  from a section-complex coefficient comparison and Mathlib's connecting-map
  naturality.
- `EtaleSectionShortComplexCoefficientComparison` states the remaining
  comparison for arbitrary coefficient morphisms. It concerns one morphism
  of section complexes and its two induced homology maps, without a cover,
  boundary, exactness, or simultaneous-family conclusion.

The argument follows [Stacks Tag 0A50](https://stacks.math.columbia.edu/tag/0A50).
The pullback/coefficient extension is the parent node's second proof step,
with the resolution construction of
[Stacks Tag 01F7](https://stacks.math.columbia.edu/tag/01F7), and is marked
agent-written. No data is chosen from the new comparison theorem: its
existence witness is eliminated only in a proof. The existing normalized
comparisons determine their values on all representing cocycles.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.tailOpenCompatibleBoundaries`
(node `lem-weil-pbc-etale-limit-open-compatible-boundaries`). Its proof
assembles actual fixed boundaries, three exactness assertions, and the two
compatibility assertions. There is no sorry left in the item's module.

The new public proof declarations are
`AlgebraicGeometry.Etale.etaleSectionShortComplex_resolution_shortExact`,
`AlgebraicGeometry.Etale.etaleSectionShortComplexOn_shortExact`,
`AlgebraicGeometry.Etale.etaleMayerVietorisFixedBoundary_exact`, and
`AlgebraicGeometry.Etale.etaleMayerVietorisFixedBoundary_naturality`.
Their private helper proofs have no holes, and all definitions are explicit.

Added one hole:
`AlgebraicGeometry.Etale.etaleSectionShortComplex_coefficient_comparison`
(node `lem-weil-pbc-etale-section-short-complex-coefficient-comparison`).
Its proof is exactly `by sorry`; its docstring gives the augmentation-preserving
resolution lift, restriction-square construction, and normalized homology
computations. This is a decomposition, with one upper hole closed and one
strictly lower hole added, net zero among the delivery's declarations.

## No longer needed

Repair X-10c6b also removes the duplicated module-level homology biproduct
coordinate, lift, and signed-desc helper declarations and their equivalence
definition from `EtaleMayerVietorisCanonicalBoundaryExact`. Only the local
section-specific equivalence and coordinate computation remain; the actual
map calculations use Mathlib directly. No import was added for inaccessible
private helpers.

No original public import is removed: all three support the unchanged
statement. The original module did not import its planned proof dependencies.
The revised parent proof no longer needs these direct dependencies:

- `lem-weil-pbc-etale-mayer-vietoris-section-comparison`,
  `Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionComparison`;
- `lem-weil-pbc-etale-resolution-section-homology`,
  `Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology`;
- `lem-weil-pbc-cohomology-pullback-functorial`,
  `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.

The other five original direct proof dependencies are now used through the new
boundary API rather than listed directly on the parent:
`def-sp-injective-resolutions`,
`def-weil-pbc-etale-mayer-vietoris-section-complex`,
`lem-weil-pbc-etale-mayer-vietoris-injective-sections-exact`,
`lem-weil-pbc-complex-ses-homology-long-exact`, and
`lem-weil-pbc-complex-ses-long-exact-naturality`.
They are retained in this route; the three dependencies listed above are the
ones the revised argument no longer uses directly. The paired existential
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionDiagram` and
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback` are not needed
by this proof. These are removals from this route; no claim is made that
other target routes cannot reach them. In particular, pullback functoriality
still occurs through the canonical-arrow statement dependencies.

Removed the uncommitted earlier-attempt module
`Sheaf.AlgebraicGeometry.EtaleLimitOpenCompatibleBoundaryData` and its
proposed node `lem-weil-pbc-etale-limit-open-compatible-boundaries-data`:
its exactness assertions are proved directly in the main proof, so neither
an extra theorem hole nor an extra delivery module is needed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox report claimed completion, contained two second-reader
sections, and counted two added holes as net zero after closing one. Those
claims are corrected here; this report leaves the independent second reading
to its reader. The prior exactness-only hole was unnecessary.

Pairwise existential boundary/comparison theorems do not ensure one family
compatible with every arrow. The normalized comparisons and fixed resolution
boundaries resolve that issue. Existing open transfer statements require the
target coefficient to be the source inverse image; the target here permits
arbitrary maps into arbitrary target coefficients. The new comparison is
strictly this missing step, not a renamed target.

The new comparison was checked on zero coefficients, empty and coincident
opens, and degree zero. It needs no cover. The main proof adds no directedness,
coefficient composition laws, or canonical-arrow assumption on G. Functoriality
of D and the cone equation identify the inverse-image opens. The statement
and all steps of the unit `sk-thm-p1` are retained.

LeanSearch returned Internal Server Error; this is recorded as unavailable,
without a mathematical verdict. Loogle supplies connecting-map naturality;
LeanFinder and source searches supplied no direct simultaneous-family theorem.
The blueprint search for Mayer-Vietoris returned no matching imported node.

## New nodes

`def-weil-pbc-etale-mayer-vietoris-canonical-boundary` records the explicit
transported boundary, its named-intersection construction, and its fixed
resolution interface.

`lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-exact` records the proved
transport of local homology exactness to actual restrictions.

`lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-naturality` records the
proved transport of connecting-map naturality using the section comparison.

`lem-weil-pbc-etale-section-short-complex-coefficient-comparison` records the
remaining resolution-lift and prescribed homology-map comparison. Its source,
complete proof in words, edge cases, searches, and exact Lean signature are
recorded. The parent's proof dependencies follow the actual assembly.

Local definitions pin the stage and limit boundaries to their constructed
values. Inferred types of the local exactness proofs avoid redundant conversions
of cohomology instances during kernel checking. No file or proof is split to bypass the limit.
No existing statement or definition changes; no forced adaptations are needed.

The local elaboration-command change is recorded in
`coord/changes/etale-limit-open-compatible-boundaries-route.md`.


## Second reading by S3

1. Compared all five delivered modules against the repository. Only
   EtaleLimitOpenCompatibleBoundaries already exists there. Its sole existing
   declaration, AlgebraicGeometry.Etale.tailOpenCompatibleBoundaries, has an
   exactly byte-identical statement (checked with the declaration parser as
   well as the full diff). The only other changes are two proof imports,
   the recorded local elaboration commands, and the proof body. All three
   original public imports remain. No target, existing definition, visibility,
   or unheld module is changed. Verdict: pass.

2. Compiled all five files in import order with lcompile.py: no errors or
   warnings, within the per-file limit. Searched every delivered Lean file
   for forbidden declarations and proof escapes; the only sorry is the
   reported named coefficient-comparison theorem. A scratch module ran
   #print axioms on all twelve public declarations. The constructed boundaries,
   fixed resolution and comparison, short exactness, and boundary exactness
   use only propext, Classical.choice and Quot.sound. The coefficient comparison,
   boundary naturality and parent theorem additionally use sorryAx. There is
   no sorry inside a definition. The comparison choice is normalized on all
   cocycles, which represent every homology class, and hence determines its
   additive equivalences; its existence theorem is already proved. The new
   existential chain-map witness is eliminated only inside a proposition.
   Verdict: pass as a decomposition, not as an axiom-free completion.

3. Read the remaining coefficient-comparison signature, its complete docstring
   argument and node. It asserts a section-short-complex morphism and the two
   normalized homology identities, with no cover, connecting map, exactness or
   simultaneous-family conclusion. It is a strictly smaller geometric step,
   not a restatement of the parent. Exact inverse image makes direct image
   preserve injectives; lifting into the pushed-forward target resolution
   gives the chain map and restriction squares. Normalization then fixes the
   whole and intersection cohomology maps. Checked zero coefficients (zero
   induced homology maps), empty intersections (zero intersection cohomology),
   coincident opens and degree zero (the actual map on sections). The square
   determines k by monicity of the intersection inclusion. Independent
   LeanFinder search for coefficient maps lifted to resolutions found generic
   InjectiveResolution lifting APIs; Loogle found the already-used
   HomologicalComplex.HomologySequence.δ_naturality. Independent source searches
   for coefficient transfer, short-complex transfer and open transfer found
   the proved global arbitrary-coefficient transfer, but the existing open
   transfer fixes the target coefficient to the inverse image of the source.
   The existing section comparison also chooses its equivalences rather than
   using the prescribed normalized comparisons. Neither supplies this missing
   step. Its formalization is more than a few-minute repair. Verdict: pass.

4. Read the assembly from the parent downward: fixed boundary construction,
   actual restriction-pair/difference exactness via homology and biproduct
   comparison, then Mathlib connecting-map naturality. All proof-only imports
   are plain imports; public imports support the public statements or definition
   bodies. No shorter existing direct comparison was found. Reviewed all eight
   old proof dependencies: three are no longer directly needed and five remain
   through the boundary API, now explicitly enumerated above. The sk-thm-p1
   statement, steps and realized fields are untouched; this is a reduction
   below its unit route. Checked the cited resolution argument against
   [Stacks Tag 0A50](https://stacks.math.columbia.edu/tag/0A50) and
   [Tag 01F7](https://stacks.math.columbia.edu/tag/01F7); the cross-scheme
   arbitrary-coefficient extension is correctly marked agent-written.
   Verdict: pass.

5. Compared each node with its Lean declaration and the actual proof. The
   parent's only changed node fields are proof, proof_deps and proof_origin;
   its original Lean statement record is unchanged. For each statement node,
   proof_deps equals the union of its proof-step uses. The new nodes supply
   source, self-contained statement, proof origin, searches, split status,
   creation, blueprint origin, chapter, unit and Lean records. The boundary
   definition node also records its bundled direct constructions and short
   exactness declarations. The single remaining hole has its matching node
   and full proof in words. Verdict: pass.

Second reading changed only this report: added the independent checks and
explicitly enumerated the five old dependencies retained indirectly. No Lean
proof or statement repair was needed, and no hole was added or closed by this
reading. The delivery closes one original hole and adds one smaller hole:
net zero, a decomposition.
