## What changed

Replaced the sole `sorry` of
`CochainComplex.exists_filtered_free_resolution` in
`Sheaf.Algebra.Homology.FilteredFreeResolution` by a complete Lean proof from
an exact free-cover bicomplex, the existing total-resolution quasi-isomorphism,
and a filtration theorem for the total of two-step split columns.
The original declaration, universes, hypotheses, conclusion and docstring are unchanged.

Added `Sheaf.Algebra.Homology.FreeCoverBicomplex` and
`Sheaf.Algebra.Homology.TotalFreeFiltration`, one public theorem per module.
The former constructs the exact augmented bicomplex and its column presentations;
it asserts neither a quasi-isomorphism nor a filtration. The latter works for any
bicomplex with those column presentations, without exactness or an augmentation;
it asserts only the filtration. These are separate parts of the construction,
not renamed versions of the original theorem. The original proof extracts all
witnesses, applies the existing quasi-isomorphism theorem with its nine hypotheses,
and combines its result with the independently supplied filtration.

Updated the original DAG node's proof, proof_deps and proof_origin to match this
composition. No definitions or statements were changed and no change record is needed.
All added imports in the original module are proof-only imports.

## Proved and sorry left

`CochainComplex.exists_filtered_free_resolution`
(lem-pc-derived-filtered-free-resolution) has no local `sorry`; its proof is a
reduction to the two construction lemmas and the existing total-resolution theorem.
It is not yet independent of `sorry` in its dependencies.

New remaining sorries, each the entire proof of a public theorem:

- `CochainComplex.exists_freeCoverBicomplex`,
  node lem-pc-derived-free-cover-bicomplex,
  module `Sheaf.Algebra.Homology.FreeCoverBicomplex`.
- `CochainComplex.exists_totalFreeFiltration`,
  node lem-pc-derived-total-free-filtration,
  module `Sheaf.Algebra.Homology.TotalFreeFiltration`.

The pre-existing dependencies
`CochainComplex.exists_freeComplexCover`
(lem-pc-derived-free-complex-cover) and
`WeilConjectures.DerivedTotalResolution.total_resolution_quasiIso`
(lem-pc-derived-total-resolution-quasi-iso) still have their original sorries;
their modules are not modified by this delivery.

All three delivered modules compile together, in dependency order, with lcompile.py.
The original proof needs no additional homology or totalization assumptions:
the required instances are inferred for ModuleCat in the declared universe.

## No longer needed

Second reading removed redundant direct public imports of
`Mathlib.Algebra.Homology.Single` from both new modules: it is already publicly
provided by `HomologicalComplexAbelian`. The original module retains its existing
public imports, preserving its interface.

Removed the direct proof import
`Sheaf.Algebra.Homology.FreeComplexCover` from the original module and replaced it
with the two construction modules. This is relocation, not pruning of the cover:
`FreeCoverBicomplex` imports it as a proof dependency and its node cites it.
The old parent-to-cover DAG edge is replaced by parent-to-bicomplex-to-cover.
No existing node or module becomes unnecessary. The existing total-resolution
quasi-isomorphism module remains directly imported and used. No public import
was removed or changed, and no blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The two imported statements did not directly provide the iterated exact bicomplex,
its augmentation, or the filtration of its total complex. These were genuine glue
constructions in steps 1--3 of the original DAG, now exposed as two independent
items rather than hidden in an unfinished proof.

The local Stacks TeX files are absent. Read the sources at
https://stacks.math.columbia.edu/tag/09KP,
https://stacks.math.columbia.edu/tag/09KN, and
https://stacks.math.columbia.edu/tag/09IZ.
The stable tags are correct, but the old section numbers in the original docstring
are stale: the current web lemmas are 22.20.4, 22.20.3 and 12.26.2 respectively.
The original docstring was preserved. LeanSearch returned Internal Server Error;
the new nodes record unavailable searches, not negative results. LeanFinder,
Loogle, Mathlib/source grep and blueprint searches provided no matching theorem.
The ModuleCat subcomplex API and Mathlib LeftResolution API were also inspected:
the latter requires functorial covers and does not supply the cycle-surjectivity
or two-step free column data needed here.

Edge cases checked in the new statements and proof descriptions: the zero ring
and zero complex need no nontriviality assumptions; empty index sets are allowed;
the inclusion out of F₀ = 0 has the zero retraction; in column zero the horizontal
target is a zero positive column; unbounded vertical degrees cause no infinite
support problem because totalization uses direct sums. A copy of A in vertical
degree d and column -i contributes in total degree d-i. Exactness on cycles of
the resolution follows from cycle-surjectivity of each cover of the kernel,
not merely degreewise surjectivity. No horizontal exactness is assumed in the
filtration theorem, and no projectivity of the original complex is required.

## New nodes

lem-pc-derived-free-cover-bicomplex:
`dag/nodes/sec-picard-framework/lem-pc-derived-free-cover-bicomplex.json`,
with module `lean/Sheaf/Algebra/Homology/FreeCoverBicomplex.lean` and declaration
`CochainComplex.exists_freeCoverBicomplex`. This is steps 1--2 of Tag 09KP:
iterate covers of successive kernels, prove exactness of term and cycle rows,
and form the signed direct-sum total augmentation. Its proof dependency is the
existing free-complex-cover node. The docstring gives the complete construction.

lem-pc-derived-total-free-filtration:
`dag/nodes/sec-picard-framework/lem-pc-derived-total-free-filtration.json`,
with module `lean/Sheaf/Algebra/Homology/TotalFreeFiltration.lean` and declaration
`CochainComplex.exists_totalFreeFiltration`. This isolates step 3 of Tag 09KP for
arbitrary nonpositive bicomplexes with two-step split free columns. It describes
the odd/even stages, their differential stability, finite-support exhaustion,
degreewise retractions and cokernel identifications explicitly. Both nodes retain
the original chapter/unit and nearest blueprint ancestor. No change records.


## Second reading by V2

1. **Visible declarations — PASS.** Compared every delivered module against the
   repository. The only existing declaration is
   `CochainComplex.exists_filtered_free_resolution`; its complete signature,
   universes, assumptions, conclusion and docstring are byte-for-byte unchanged.
   Its differences are two proof-only imports replacing the direct cover import
   and the proof body. Both additional modules are new. No definitions or target
   statements changed; no change record is needed.

2. **Proof and axioms — PASS as a reduction, not an axiom-free final proof.**
   Independently compiled all three modules using `lcompile.py --all` in dependency
   order. Scratch copies appended `#print axioms` for each delivered theorem;
   each reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   There are exactly two local sorries, the complete proofs of the two reported
   public construction theorems. There are no definitions, hidden proof holes,
   forbidden declarations or kernel-check bypasses. The parent extracts the exact
   bicomplex data, supplies all nine hypotheses of the existing total-resolution
   theorem, and independently supplies the six filtration clauses. Its dependency
   on open statements is explicitly reported above.

3. **Split statements — PASS.** Read both Lean signatures, nodes, and complete
   natural-language proofs against [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP),
   [Tag 09KN](https://stacks.math.columbia.edu/tag/09KN), and
   [Tag 09IZ](https://stacks.math.columbia.edu/tag/09IZ).
   The bicomplex theorem supplies exact rows of terms and cycles and the free
   column presentations; it asserts neither quasi-isomorphism nor filtration.
   Cycle lifting through the successive kernel is justified by injectivity of
   the kernel inclusion and the cover's cocycle-surjectivity, including column
   zero. The filtration theorem assumes these presentations but no exactness or
   augmentation; it is applicable independently of the chosen resolution. Neither
   theorem restates the parent. Tested the zero ring/complex, empty summands,
   a single copy of A in an arbitrary degree, two adjacent columns with nonzero
   horizontal map, and an identity-differential two-term column. The first stage
   is the left term of column zero; a generator in vertical degree d of column
   -i occurs in total degree d-i. Positive columns vanish, so the rightmost
   horizontal map is zero. Earlier full columns absorb all other horizontal
   differentials; the left term and the column quotient have zero vertical
   differential. Retractions are degreewise only, exactly as required. Unbounded
   complexes cause no exhaustion problem because diagonal sums have finite support.
   Both statements require substantial new constructions and cannot be closed in
   a few minutes from the available API.

   Repeated searches with different terms via the prescribed `msearch.py`:
   LeanFinder queried disk/sphere kernel resolutions and column filtrations;
   Loogle queried `HomologicalComplex₂.total`; grep queried
   `semifree|two.step.*free|free.*two.step|filtration.*total|total.*filtration`.
   No exact match was found. Also searched `lean/Sheaf`, `lean/WeilConjectures`,
   and Mathlib homology sources. Read the nearby upstream
   `CochainComplex.exists_quasiIso_of_liftsAlongEpi`: it assumes bounded-above
   input and gives neither the two-step column data nor the desired filtration.
   Mathlib projective/left resolutions likewise do not supply these clauses.

4. **Route and pruning — PASS after import cleanup.** Both old proof dependencies
   remain used: the cover through the bicomplex node, and the total-resolution
   theorem directly. The report distinguishes this relocated edge from pruning;
   no old node is unused and no module is pruned. All new parent imports are
   proof-only. Removed the redundant direct `Single` imports from the new modules;
   the other new public imports provide data, instances or notation in their
   signatures. The unit `sk-thm-picard-f-representable` has empty realization
   lists, and this auxiliary node changes none of its statement or steps. The
   projection-formula route through filtered free resolution and free generation
   is retained. Mathlib's total complex uses the stated horizontal differential
   plus (-1)^p times the vertical differential.

5. **DAG agreement — PASS.** Parsed all three nodes and compared each `lean.statement`
   with its module's normalized declaration signature: exact agreement. Each
   `proof_deps` equals the union of its proof steps' `uses`. The parent node changes
   only `proof`, `proof_deps`, and `proof_origin`. The two new nodes carry the
   required source, searches, creation record, blueprint ancestor, chapter/unit,
   split status and complete Lean record. Their proof steps match the docstrings
   and the parent proof uses exactly the three listed dependencies.

Changed in this reading: removed two redundant imports and expanded this report
with independent review and validation evidence. No proof or statement changed.
