## What changed

Proved `AlgebraicGeometry.exists_perfect_restrict_iso_directSum_shift` in
`Sheaf.AlgebraicGeometry.AffinePerfectPlusShift`, preserving its signature and visibility.
The proof follows Stacks Tag 08EI: obtain the shifted locally free summand extension,
lift its projector, complete the lifted map to a distinguished triangle, and apply
two out of three to its cone. The private, fully proved `cone_projection_iso` computes
the restricted cone by adjoining two trivial summands to an identity triangle and
comparing the first two terms of distinguished triangles.

Added proof-only imports `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh` (the target of
map lifting must have quasi-coherent cohomology) and
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Triangulated` (its proved
`mk_fst_comp_distinguished` and `mk_comp_inl_distinguished` supply the cone calculation).
Updated only the item's node proof, proof dependencies, and proof origin to record
these steps. No public imports, statements, definitions, or other modules changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_perfect_restrict_iso_directSum_shift`
(node `lem-sc-affine-perfect-plus-shift`). The private `cone_projection_iso` is proved.
No holes remain in the delivered module; no holes were added or split off.
This is a proof from existing declarations, not a new decomposition. The existing
extension and map-lifting theorems may still depend on `sorry`; they are intentionally
used as the next stage-3 items. No claim of an axiom-free transitive target proof is made.

Local compilation passed without errors or warnings. The generic cone calculation
requires neither perfectness, affineness, nor quasi-compactness. It covers zero
summands, the empty open, and all integer shifts without case exclusions.

## No longer needed

None. All three original proof imports are used: `AffinePerfectPlusLocallyFree`,
`AffinePerfectMapLift`, and `PerfectTwoOutOfThree`. No planned dependency node or
module is pruned. The proof needs no extra finite-locally-free perfection lemma and
no new cone-calculation hole.

## Where the brief, the DAG or earlier work was wrong

The DAG's quasi-coherence justification can now use the existing
`schemeDerivedQCohProperty_of_isPerfect` in `PerfectImpliesQCoh`, node
`lem-sc-perfect-qcoherent`; its proof is not repeated here. The final cone computation
is made explicit with already proved source-library trivial-summand lemmas (lines
50 and 113 of `WeilConjectures/Mathlib/CategoryTheory/Triangulated/Triangulated.lean`).
The original DAG route is retained. The unit's realized lists are empty and no unit
statement or required step is bypassed.

The locally free extension node's historical Tag 08ED reference differs from the
current Lean docstring and current Stacks Tag 08EG; the theorem actually used has
exactly the required shifted finite locally free summand conclusion. The item itself
is unchanged and agrees with https://stacks.math.columbia.edu/tag/08EI, read during
this session because the local Stacks source is absent. No statement dispute or forced
adaptation was necessary.

## Second reading by C3

1. PASS: compared the only delivered Lean module with the repository using `diff` and
   a byte-for-byte signature comparison. The existing theorem's entire signature,
   visibility, and docstring are unchanged. `X` remains affine, `U` remains a compact
   open, `F` remains perfect on `U`, and the conclusion remains a perfect object on
   `X` restricting to `F ⊞ F[1]`. All derived-category instance binders are retained.
   There are no definition changes, adapted modules, or change records.
2. PASS: compiled the module locally without errors or warnings (12.1 seconds), then
   compiled a scratch copy with `#print axioms` for both declarations (10.2 seconds).
   `cone_projection_iso` uses only `propext`, `Classical.choice`, and `Quot.sound`.
   The main theorem uses those three and `sorryAx` from existing open dependencies.
   There is no `sorry` or forbidden declaration in the delivered module. The witness
   eliminations occur inside an existential theorem proof; no definition chooses
   arbitrary data from an unproved existence statement. The local `PQ` wraps the
   already obtained `P` with a proof of quasi-coherence, without choosing new data.
3. PASS: no statements were split off and no new holes were added. Read the fully
   proved private cone helper: source padding of the identity triangle contributes
   `F[1]`, target padding contributes `F`, and the triangle comparison gives the
   required third-object isomorphism. It applies equally when `M` or `F` is zero;
   the main argument also covers the empty open and every integer `r`. There is
   no rank, nonemptiness, or degree restriction hidden in the proof.
4. PASS: read all four geometric proof dependencies and the two upstream padding
   proofs, and searched the local Sheaf/upstream sources using restriction/lift/shift
   and cone/projection terminology. Searched Mathlib's triangulated sources for
   biproduct distinguished triangles and isomorphism comparison; the proof already
   uses its `isoTriangleOfIso₁₂`. No shorter existing extension or projection-cone
   theorem was found. All three original proof imports are used, and both added
   imports are proof-only and used directly. No old proof dependency is omitted,
   so `## No longer needed` is complete. Read `sk-thm-picard-duality.json`: its
   realized statement and step lists are empty, and this proof keeps the original
   extension/lifting/cone route below the unit level. The blueprint section source
   is absent locally; the unit record contains its statement and step in full.
   Independently checked [Stacks Tag 08EI](https://stacks.math.columbia.edu/tag/08EI):
   its statement and projection-cone proof agree with this unchanged theorem.
5. PASS: compared node records programmatically. Only `proof`, `proof_deps`, and
   `proof_origin` changed, and `proof_deps` equals the union of the steps' `uses`.
   Read each listed dependency's statement and Lean/Mathlib record. The added
   quasi-coherence dependency supplies exactly `PQ`'s proof; the triangulated and
   triangle-isomorphism dependencies justify cone completion and comparison.
   The explicit cone calculation and its proved upstream lemmas are recorded.

Second reading changed only this report, adding the independent checks and their
results. No Lean or node repair was needed. Holes closed: one, namely
`AlgebraicGeometry.exists_perfect_restrict_iso_directSum_shift`; holes added: zero;
statements split off: zero; modules pruned: none.
