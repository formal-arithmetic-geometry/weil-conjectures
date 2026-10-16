## What changed

Kept the signature and visibility of
`CategoryTheory.cartanEilenberg_second_image_eq_truncation` unchanged and replaced its
`stage-3 sorry` by a complete Lean proof from the normalized truncation comparison.
The cases p <= 0 and n < p are proved directly. In the remaining range the proof
uses the equality of decalage and filtration-step cohomology images and a commuting
square with the canonical Grothendieck spectral object.

Constructed decalage as an actual complex of intersection subobjects, with its
restricted differential and monic inclusion. Proved its cohomology-image lemma
without boundedness assumptions. Constructed the full and horizontal-cut injective
totals explicitly, proved their boundedness and injectivity, and checked all three
augmentation/inclusion equations. Proved the derived-unit comparison and its
normalization using the existing canonical resolution-unit comparison.

Continued proving the intermediate comparisons rather than leaving the first split
open. The good-cut derived-truncation comparison is proved: construct the truncated
augmentation, prove its columns are quasi-isomorphisms (including the horizontal
cycle column), totalize, check the augmentation square, and identify good complex
truncation with t-structure truncation by its homology. A separate, fully proved
functor/truncation API supplies the exact degree-zero embedding comparison.

The mapped-cut comparison is also proved: extension by zero preserves finite limits,
the functor/truncation isomorphism commutes with inclusions, the mapped-total
comparison is natural on every diagonal summand, and total-flip signs commute.
The pure good-cut/decalage comparison is also proved: coproducts preserve monics,
the degreewise image identity gives canonical isomorphisms onto the intersection
subobjects, and cancellation of the monic inclusions proves the differential
equation. The image identity is proved when n<q, including every negative total
degree, because the totalized inclusion is then invertible.
The only remaining assertion is the degreewise finite-diagonal boundary-kernel
identity in the range 0<=q<=n. It concerns just one first-quadrant bicomplex:
no functor G, extension by zero, acyclicity assumption, derived category, homology, spectral object or augmentation.
Its docstring gives both subobject containments, including the empty strict sum
when q=0. The assembly into a complex and all other index ranges are proved.

All new modules are imported by the proof, with proof imports private. The second
reading narrowed three imports in new modules, as detailed below. Existing public
imports and declarations of the item are unchanged. No existing module
outside the item was changed. No target statement was changed.

Repaired the maintainer's duplicate-theorem return: removed both new private
`image_comp` lemmas, from `FilteredComplexDecalageImage` and the item module.
Both proofs now use the existing
`CategoryTheory.DecreasingFiltration.exists_image` from
`Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries`, reached with
`import all` because that helper is private. This follows the existing use in
`FilteredCohomologyImageCycleMap`. The existing module and its visibility are
unchanged; the repair adds no statements, nodes or holes.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.cartanEilenberg_second_image_eq_truncation`.

Fully proved new declarations and their supporting APIs:

- `CategoryTheory.DecreasingFiltration.decalage_image`;
- `CochainComplex.mapTruncLEComparison_ι` and
  `CochainComplex.mapTruncLEComparison_isIso`;
- `CategoryTheory.cartanEilenberg_horizontal_cut_terms`;
- `CategoryTheory.cartanEilenberg_total_injective_terms`;
- `CategoryTheory.cartanEilenberg_good_cut_decalage`;
- `HomologicalComplex₂.good_truncation_total_decalage` and
  `HomologicalComplex₂.good_truncation_total_image`;
- `CategoryTheory.cartanEilenberg_good_cut_identification` (including the complete
  derived truncation and augmentation-square part, from the remaining concrete
  subcomplex comparison);
- `CategoryTheory.cartanEilenberg_horizontal_cut_comparison`;
- `CategoryTheory.cartanEilenberg_decalage_injective_model`;
- `CategoryTheory.cartanEilenberg_decalage_truncation_diagram`.

One new hole remains:
`HomologicalComplex₂.good_truncation_total_boundary_image`, node
`lem-sp-good-truncation-total-boundary-image`, in
`Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage`.
It still needs the two containments identifying the image of the finite direct sum
of the cut terms with the second-filtration/differential intersection, for
0<=q<=n. The proof should evaluate truncation below q and at its boundary kernel,
then use the diagonal inclusions and projections. All other degrees, monicity,
complex assembly, total-flip signs and functor comparisons are proved in callers.

This is a decomposition: one original hole closed, one strictly smaller hole added,
so the delivery itself has net zero holes closed. The item proof also uses existing
library theorems through their declared APIs; their proof status is not changed.
There is no sorry in a definition or in any other new declaration.
The item is reduced to a remaining obligation; it is not yet axiom-clean.

All fourteen sandbox modules compile together without errors or warnings using
`lcompile.py --all`. Each file is below the 60-second limit. The delivery dry run
is the final required validation.

## No longer needed

Removed the item's direct imports of `Sheaf.CategoryTheory.Filtration` and
`WeilConjectures.CategoryTheory.Abelian.Filtration`; the necessary public filtration
interfaces remain available through the existing statement imports. Their interfaces
remain used; this is import pruning, not a claim that these modules leave the targets'
transitive closure.

The previous direct dependencies `def-sp-cartan-eilenberg-presentation`,
`def-sp-composite-acyclicity` and `def-sp-filtration` remain the sources of the
statement interfaces and are used through the new comparison chain; they are no
longer separate entries in this node's direct proof route. The direct dependency
`def-sp-double-complex-total` is retained.

The old direct proof dependency `lem-sp-derived-well-defined` is replaced by the
specific existing `lem-pc-grothendieck-resolution-unit-comparison` through the new
comparison diagram. The generic derived-well-defined theorem is not applied by this
proof. No claim is made that it is unreachable elsewhere.

The proof does not use a filtered injective comparison existence theorem, a filtered
homotopy uniqueness theorem, the full filtered spectral-sequence realization
(`lem-sp-ce-filtered-truncation-comparison`), or the boundary/homology portions of the
horizontal CE presentation. Only the column and horizontal-cycle quasi-isomorphisms,
term injectivity and cycle-term injectivity are needed. These stronger presentation
interfaces are unchanged because they are also used elsewhere. No existing module
is withdrawn.

The second reading replaced the new diagram's public import of
`Sheaf.CategoryTheory.FilteredComplexDecalageImage` by
`Sheaf.CategoryTheory.FilteredComplexDecalage`, since only the construction is used
there. It replaced the cut-terms module's public import of
`Sheaf.CategoryTheory.CartanEilenbergPresentation` by
`Mathlib.Algebra.Homology.HomologicalBicomplex`: the lemma uses an arbitrary
bicomplex and does not need a presentation. In `MapGoodUpperTruncation`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` is now a plain proof import.

The repair also removes the redundant direct proof import of
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` from both repaired files;
its API is available through the imported existing module. No whole module is
pruned from the targets' closure. The two duplicate local `image_comp` proofs are
no longer needed. The current second reading additionally removes the local
`transported_imageFiltration_eq` proof, using the existing identically stated
private helper in `GrothendieckCanonicalImageFiltration` through `import all`.
This is a proof import; no existing public import is changed.
Also removed `MapGoodUpperTruncation.iota_iso` and use the existing upstream
`CochainComplex.isIso_ιTruncLE_f` in all three callers. The image module no longer imports the new Map module at all; the
good-cut-identification module imports it with plain `import`. The image
node no longer needs `def-sp-map-good-upper-truncation` in its proof route.
The upstream component lemma is a proof-only import.

## Where the brief, the DAG or earlier work was wrong

The returned version duplicated the existing private `exists_image` helper.
Its privacy is handled by `import all`, so copying its proof was unnecessary.

The original route omitted a Lean construction of decalage and the explicit cut-total
comparison. These cannot be inferred from the generic derived-well-defined theorem
alone. The delivery supplies the construction and proves the injective-model,
truncation, derived-unit and normalization parts, isolating only the finite-diagonal
kernel calculation. This is a missing interface/proof in the plan, not a disputed
statement.

The normalized comparison diagram holds for all q >= 0 and all natural cohomology
degrees n; its proof does not need q < n. The caller uses the smaller range after
handling the top and bottom cases directly.

## New nodes

`def-sp-filtered-complex-decalage`: actual intersection-based shifted-cycle complex,
restricted differential, natural inclusion and monicity; all properties proved.

`lem-sp-filtered-complex-decalage-image`: the image equality in ambient cohomology,
proved by the cycle-kernel intersection and naturality of homology projections.

`def-sp-map-good-upper-truncation`: actual functor/truncation comparison, its inclusion
equation and invertibility for left exact functors; all properties proved.

`lem-sp-ce-horizontal-cut-terms`: good-cut vanishing and injective terms, proved by
truncation coordinates below, at and above the boundary.

`lem-sp-ce-total-injective-terms`: boundedness and injectivity of the actual
finite-diagonal total, proved using a finite CoreHasTotal witness.

`lem-sp-ce-good-cut-decalage`: proved comparison, reducing the mapped cut to the
unmapped good-cut total using finite-limit preservation and both naturality squares.

`lem-sp-good-truncation-total-decalage`: proved monicity of the total inclusion and
assembly of the degreewise image identity into a complex isomorphism.

`lem-sp-good-truncation-total-image`: proved image identity in all degrees from the
boundary identity and the explicit invertible case n<q.

`lem-sp-good-truncation-total-boundary-image`: the sole remaining hole, the concrete
degreewise kernel identity for 0<=q<=n. See the precise remaining work above.

`lem-sp-ce-good-cut-identification`: proved canonical derived-truncation comparison
and inclusion square, combined with the preceding concrete subcomplex comparison.

`lem-sp-ce-horizontal-cut-comparison`: proved full/cut comparison with normalization
on vertical-degree-zero total summands, including total-flip signs.

`lem-sp-ce-decalage-injective-model`: proved construction of compatible injective
models and their augmentation, inclusion and truncation equations.

`lem-sp-ce-decalage-truncation-diagram`: proved homology square and its canonical
resolution normalization. The existing item node's proof route is updated to use
this diagram, the image lemma and the direct edge-case calculation.

All new nodes retain the item's chapter and unit and record the searches and sources.
There is no change record: no existing statement or definition was changed, and
there are no forced adaptations.

## Earlier second reading (a previous round; superseded)

1. **Existing interfaces: pass.** Diffed every delivered Lean file against the shared
   repository. Only `CartanEilenbergSecondImageTruncation` already exists; its full
   theorem header, including haug, is byte-for-byte identical. The thirteen other
   modules are new. No existing definition, target, signature or visibility changed,
   and no forced adaptation or change record is needed.

2. **Proof and construction: pass, with the reported open lemma.** Read all fourteen
   modules. The decalage terms are actual intersection subobjects; its differential
   is a `factorThru`, with separately proved factorization and square-zero lemmas.
   The full/cut totals, augmentation, mapped truncation comparison and localization
   maps are constructed explicitly. Inverses and subobject isomorphisms have their
   required uniqueness properties. No definition selects an arbitrary witness of an
   unproved existence theorem. The derived-unit comparison uses the existing
   canonical resolution-unit theorem and its specified normalization equations.
   All fourteen modules compiled without errors or warnings. The only textual
   `sorry` is `HomologicalComplex₂.good_truncation_total_boundary_image`; there are
   no forbidden declarations or kernel-check bypasses. A separate scratch `#print axioms` check passed for every node declaration and
   the decalage data definitions: only propext, Classical.choice and Quot.sound,
   plus sorryAx exactly on the open boundary lemma and comparisons depending on
   open statements. The decalage construction, its image lemma, mapped-truncation
   comparison, injective cut terms and injective total terms have no sorryAx.
   The delivery tool also probes every declaration.

3. **Remaining split: pass as a strict reduction.** Read
   `lem-sp-good-truncation-total-boundary-image` together with its exact Lean
   statement and docstring. In total degree n, filtration n-q retains p<=q.
   Modulo the next vertical step, only the horizontal differential from p=q
   survives, into (q+1,n-q). Its kernel is exactly the degree-n image of the
   horizontal good cut. Checked q=n=0, q=0<n, q=n>0, a zero bicomplex, and a
   bicomplex supported on the boundary and its outgoing summand: these respectively
   give the single boundary kernel, the same kernel with no strict columns, the
   full strict part plus boundary kernel, zero, and the specified ordinary kernel.
   The identity requires no exactness of G, injectivity, spectral realization or
   augmentation. The finite biproduct projections and kernel universal property
   prove both containments as described in the docstring; the other index ranges
   are already proved in `good_truncation_total_image`. This is true and strictly
   simpler than the original normalized derived image equality, not its renaming.
   Repeated Mathlib searches with a new finite-diagonal/kernel query using
   leanfinder, loogle and grep (recorded in searches.jsonl), and searched the shared
   Sheaf and upstream homological-algebra files. Found the existing truncation
   coordinates and derived exact-functor comparisons, but no total boundary-image
   identity. Closing this kernel calculation still needs a substantial finite
   biproduct argument; it is not a missing one-line API application.

4. **Route and pruning: pass after import repairs.** Read Stacks
   [015X](https://stacks.math.columbia.edu/tag/015X), second spectral sequence and
   its final filtered-resolution paragraph;
   [015N](https://stacks.math.columbia.edu/tag/015N), CE resolution proof;
   [012K](https://stacks.math.columbia.edu/tag/012K), cycle and induced-filtration
   formulas; and [0118](https://stacks.math.columbia.edu/tag/0118), good truncation.
   The new lemmas supply the explicit comparisons left to the reader in 015X.
   The Lean proof first handles p<=0 and p>n directly, then uses the cycle-image
   theorem, normalized homology square, and cancellation of the cut isomorphism.
   No stronger filtered uniqueness or spectral realization result is imported.
   Checked the full and cut augmentation squares, the boundary horizontal cycles,
   and the zero-resolution-degree flip sign. The inherited unit record
   `sk-prop-av-pqf-finite` is a geometric unit with empty realized arrays and is
   already mismatched to this spectral-sequence item in the repository; this
   delivery does not change it or bypass any node in its recorded route. The
   blueprint ancestry remains the second-filtration step of `thm-sp-grothendieck`.
   No whole module is claimed pruned; the complete direct-dependency changes and
   import reductions are listed under No longer needed.

5. **DAG agreement: pass.** Checked all fourteen JSON records against the Lean.
   The sole existing node changes only proof, proof_deps and proof_origin. Every
   new node has its declaration's verbatim header, source, chapter/unit, blueprint
   ancestry, creation record and recorded searches. The new proof routes match
   the actual calls: image -> boundary-image plus the invertible n<q case;
   decalage -> degreewise image plus monicity; mapped good cut -> truncation
   comparison, pure decalage and mapped-total naturality; derived cut -> column
   quasi-isomorphisms and homology detection; model -> injective terms and total
   resolution; diagram -> model and canonical resolution-unit normalization.
   The only new hole has its named theorem, complete proof in words and node.

Changed only three import lines in the new modules, as listed above, and clarified
this report's pruning/accounting and review. The first dry run rejected a fourth candidate narrowing: the image lemma uses
`homologyMap` in its public statement, so its ShortComplex.HomologicalComplex import
was restored to public. No proof or theorem statement needed repair. One original hole is closed and one smaller hole added: a decomposition
with net zero holes, not a completed proof of the import closure.

## Second reading by K1

1. **Existing interfaces: pass.** Diffed every module against the shared library.
   The item's complete theorem header, including haug, is byte-for-byte unchanged.
   Its public imports and visibility are unchanged. Thirteen delivery modules are
   new; no existing module besides the item is changed. During the push a new
   canonical FilteredComplexDecalage module landed from J4. Removed our conflicting
   module from the delivery and now import the landed one. The adapter module
   FilteredComplexDecalageComplex abbreviates its step and inclusion, preserving
   the canonical decalage definition and every J4 declaration. No forced adaptation
   or statement change record is required. The sole existing node changes only
   proof, proof_deps and proof_origin. All new node signatures were checked with
   the project's declaration parser, including let-bound conclusions.

2. **Proof and construction: pass with one reported open lemma.** Read every
   delivered module and compiled the fourteen-module set with lcompile.py --all.
   All compile without errors or warnings, within the per-file limit. The final
   adapter uses the proved unique canonical decalage filtration and does not
   choose arbitrary data from an unproved existence statement. The cut/full
   totals, augmentation and mapped truncation comparison are explicit; inverses
   refer to specified isomorphisms. The sole textual hole is the named public
   theorem HomologicalComplex₂.good_truncation_total_boundary_image. There is no
   hole in a definition, forbidden declaration or kernel bypass. A fresh scratch
   axiom audit and delivery probes show only propext, Classical.choice, Quot.sound
   and sorryAx where open statements are used. The permitted axiom check therefore
   does not yet certify the import closure as completely proved.

3. **Remaining split: pass as a strict reduction.** Read its docstring and node.
   The only obligation is a degreewise kernel calculation for one first-quadrant
   bicomplex and 0<=q<=n, with no functor, derived category, augmentation,
   injectivity or spectral object. The second-filtration step n-q retains the
   horizontal indices p<=q. In degree n+1 the step n-q+1 also retains p<=q.
   Modulo that step, only the outgoing horizontal differential from p=q survives.
   Its kernel is the full strict sum p<q plus the boundary horizontal kernel,
   precisely the good-cut diagonal image. Total signs are units. Checked q=n=0,
   q=0<n, q=n>0, zero bicomplexes and a boundary/outgoing-term supported bicomplex;
   the strict sum is empty at q=0. Its proof in words gives both containments via
   diagonal projections and kernel lifts. Repeated leanfinder, loogle, grep and
   shared-library searches with new totalized-inclusion and diagonal-coproduct
   queries. No existing boundary-image theorem was found. The missing finite
   biproduct argument is substantial and is strictly simpler than the normalized
   derived image equality of the item, not a renamed restatement.

4. **Route and pruning: pass after repairs.** Read Stacks
   [015X](https://stacks.math.columbia.edu/tag/015X),
   [015N](https://stacks.math.columbia.edu/tag/015N),
   [012K](https://stacks.math.columbia.edu/tag/012K), and
   [0118](https://stacks.math.columbia.edu/tag/0118). Checked the direct p<=0 and
   p>n cases, the decalage cycle-image equality, horizontal cycle boundary column,
   cut/full augmentation squares, mapped-total naturality, total-flip signs (one
   on resolution degree zero), and the canonical resolution-unit normalization.
   The item applies the normalized square and cancels the cut isomorphism from
   the image. Removed two further duplicated private proofs: transported_imageFiltration_eq
   now comes from GrothendieckCanonicalImageFiltration through import all, and
   iota_iso is replaced by the upstream CochainComplex.isIso_ιTruncLE_f in its
   three callers. Removed the image module's now-unused MapGoodUpperTruncation
   import and narrowed the identification module's import to plain import.
   Retained the earlier repair using exists_image rather than duplicate image_comp.
   After the concurrent landing, reused canonical decalage rather than maintaining
   a second construction. The existing exact-functor truncation comparison needs
   finite colimits and does not replace the left-exact comparison here.
   No whole module is claimed pruned. All old direct dependencies omitted by
   this route are accounted for above. The inherited geometric unit has empty
   realized arrays and mismatched attribution; this delivery preserves it and
   its blueprint ancestry and bypasses no recorded realized step.

5. **DAG: pass.** Read all fourteen nodes against the final declarations and calls.
   Every new node has source, statement, proof steps, dependency union, origin,
   recorded searches, creation, blueprint, chapter/unit and Lean record. The
   construction node now records abbreviations of the landed canonical decalage
   and depends on lem-sp-filtered-complex-decalage. The image theorem uses the
   canonical intersection formula. The total-image route uses the boundary
   lemma plus the invertible n<q case and no Map dependency. The total-decalage
   proof assembles canonical subobject isomorphisms using monicity. The mapped
   cut, derived cut, model and diagram routes match their concrete comparisons,
   column quasi-isomorphisms, injective terms and normalized derived-unit calls.
   The only remaining hole has a new module, named theorem, full proof in words,
   source and matching node. The main theorem's original signature is unchanged.

Changed duplicate helpers/imports, reused the concurrently landed canonical
filtration via abbreviations in FilteredComplexDecalageComplex, adapted the new
comparison proofs and node signatures, and corrected this report. The earlier
successful dry runs preceded the concurrent landing. The subsequent failures
were the interface collision and then stale node signatures; both are repaired.
The delivery closes the original item hole and adds one strictly smaller boundary
hole: a decomposition with net zero holes closed, not a complete proof of the
import closure. No existing dependency module is overwritten.
