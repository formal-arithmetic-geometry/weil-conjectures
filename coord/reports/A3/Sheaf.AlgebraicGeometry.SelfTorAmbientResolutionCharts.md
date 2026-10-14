## What changed

Replaced the sorry in `AlgebraicGeometry.exists_selfTor_ambient_resolution_charts`
with a proof from affine section coordinates, quasi-coherence of the ambient
homology sheaf, and affine reconstruction (Stacks Tag 01IB). The existing signature and all public
imports are unchanged.

The private helper `qc_single` proves quasi-coherence of a degree-zero single
object by computing every cohomology degree. The private helper
`affine_iso_of_section_equiv` reconstructs an isomorphism on the category of opens
below an affine open from a linear equivalence of section modules, assuming both
restricted sheaves are quasi-coherent. It extends the equivalence and its inverse
using the existing affine Hom API, checks their composites by affine Hom
extensionality, and transports through `overEquiv`. Its normalization on top
sections is proved, including the open-image equality transport.

The main proof uses the existing affine pushforward quasi-coherence theorem and
`canonical_derivedTensor_preserve_QCoh`, then composes the normalized section
coordinates of `exists_selfTor_affine_chart_sections` with the ambient section
coordinates. Naturality of the resulting sheaf morphism proves the original
restriction equation for every supplied augmented comparison.

Added one new module, `Sheaf.AlgebraicGeometry.SelfTorAmbientSectionCoordinates`,
and its node. Updated the item's node to describe this route. All new imports
of the item's module are proof-only. No definitions, existing interfaces, target
statements, or other modules are changed. The statement elaborates with a local
heartbeat allowance; the compiler's 60-second wall-time limit is unchanged.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_selfTor_ambient_resolution_charts`
(node `lem-pc-self-tor-ambient-resolution-charts`). The item's module has no sorry.

Added one hole:
`AlgebraicGeometry.exists_selfTor_ambient_section_coordinates`
(node `new-a3-self-tor-ambient-section-coordinates`), in its own module, with
proof exactly `by sorry`. It supplies linear equivalences on affine sections and
their basic-open restriction equation. It supplies no sheaf isomorphism and no
quasi-coherence proof. Quasi-coherence, affine reconstruction, inverse identities,
normalization, and the final sheaf restriction equation are proved separately in
the item's module. This is a decomposition, not a sorry-free proof of self-Tor;
one hole is closed and one is added, so the direct net hole count is zero.

The new lemma's edge cases were checked mathematically: degree zero is ordinary
quotient tensor, the unit ideal gives zero quotient and zero section modules,
and an empty basic open has zero target sections. Localization and projective
comparison require no noetherian, finite-generation, regularity, or nonempty-open
hypothesis. Arbitrary augmented lifts give the same homology map by homotopy.
No object is defined by an arbitrary witness of an unproved existence theorem.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
- `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`

Their four nodes remain needed for the new section-coordinate obligation and
are imported there. They are relocated dependencies, not modules pruned from
the target closure. No node or module is claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or interface error found. The original DAG plan describes
the affine comparison but its existing dependency signatures do not directly
supply its natural section-coordinate equation across different affine rings.
That remaining part is now stated explicitly. The unchanged unit record has no
realized node in this item; the finite-duality ancestor and unit route are retained.

The source Tag 08DX has separate affine-computation and quasi-coherence clauses.
This reduction uses its quasi-coherence clause through the existing
`canonical_derivedTensor_preserve_QCoh`, rather than assuming that section
coordinates already supply an isomorphism of sheaves. The affine Hom API already
exists in `WeilConjectures.AlgebraicGeometry.Modules.AffineHom` and was reused.

## New nodes

`new-a3-self-tor-ambient-section-coordinates` states only the affine section
portion of the comparison, with the explicit chosen-resolution homology map.
Its complete proof sketch follows Tags 08DX(2), 06YG, and 00LS. The node records
four actual Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch); the
LeanSearch service returned Internal Server Error, recorded as unavailable. The
other searches found
supporting APIs but no exact natural ambient section comparison. It inherits
the item's chapter, unit, and finite-duality blueprint ancestor. No change record
is needed because no existing statement or definition is changed.


## Second reading by A3

1. **Interfaces: pass.** Compared both delivered modules with the repository.
   The only existing declaration, `exists_selfTor_ambient_resolution_charts`,
   has a byte-for-byte identical signature; its visibility and all original
   public imports are unchanged. No definition is added or changed. The existing
   node differs only in `proof`, `proof_deps`, and `proof_origin`. No change record
   is required.
2. **Proof and trust: pass.** Compiled both modules through `lcompile.py` in import
   order and inspected the complete proofs. The main module has no `sorry`; the
   new module has exactly the reported named theorem with proof `by sorry`.
   Neither contains forbidden declarations or trust-bypassing attributes.
   Scratch copies with `#print axioms` check both private helpers and both public
   theorems: both private helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`; both public theorems additionally use the permitted `sorryAx`
   from open obligations. No arbitrary witness from an unproved existence theorem is used to
   define library data: all constructions occur within existential theorem proofs.
3. **Remaining statement: pass as decomposition.** Read the new theorem and its
   node against Stacks Tags [08DX](https://stacks.math.columbia.edu/tag/08DX),
   [06YG](https://stacks.math.columbia.edu/tag/06YG), and
   [00LS](https://stacks.math.columbia.edu/tag/00LS). Its obligation is the affine
   section calculation and naturality, whereas quasi-coherence, affine sheaf
   reconstruction, inverse identities and normalization are proved in the main
   module. It is a strictly smaller part of the argument, with a complete
   docstring proof and matching node. Checked n=0 (ordinary quotient tensor),
   I=top (both modules zero), V=U (comparison lifts are homotopic to identity),
   and empty V (both restricted sections zero). For a basic inclusion the source
   resolution localizes to projectives over C; a factors through that localization,
   so projective comparison homotopies apply to every supplied augmented lift.
   The pure-tensor equation determines k, and tensoring the comparison homotopy
   makes its homology map independent of the lift. Fresh LeanFinder search for
   affine global sections of derived tensor homology, Loogle search for single
   functor homology, Mathlib grep, and local searches in `lean/Sheaf` and
   `lean/WeilConjectures` found supporting APIs but no replacement for this hole.
   This obligation cannot be closed in a few minutes from the existing signatures.
4. **Route and pruning: pass.** Checked the main proof from its goal downward:
   affine Hom extension/extensionality is already reused, then quasi-coherence and
   the normalized chart-section theorem provide the reconstruction. Other similar
   reconstruction helpers in `SelfTorConormalWedgeChartFromSections` are private.
   The four old direct dependency nodes
   `lem-sc-affine-quotient-resolution-sheafification`,
   `lem-pc-bounded-above-flat-kflat`,
   `lem-pc-affine-derived-pullback-tensor-tilde`, and
   `lem-pc-kflat-derived-tensor-comparison` are no longer direct dependencies of
   the main theorem; all remain dependencies of the new obligation, so none is
   claimed pruned from the target closure. The unit `sk-thm-picard-duality` has
   `realized` equal to `{"statement": [], "steps": [[]]}`; no realized step is
   bypassed or changed, and the finite-duality blueprint ancestry is preserved.
5. **DAG: pass.** Verified the main node's four dependency edges against the
   theorem applications and its proof steps. Verified the new node's required
   fields, source, search records, chapter/unit ancestry, and verbatim Lean
   signature. Its proof dependencies have the existing declarations referenced
   by the docstring. No node claims the remaining affine comparison is proved.

**Second-reading change:** removed the unnecessary public import
`Mathlib.AlgebraicGeometry.Modules.Tilde` from the new section-coordinate module;
its statement uses no tilde construction. No proof or signature needed repair.
The final delivery remains one original hole closed and one new hole added,
a decomposition with direct net zero and no claimed globally pruned modules.
