## What changed

Completed the inherited sandbox proof of
`AlgebraicGeometry.Scheme.perfect_affine_map_representative`, preserving its signature and
visibility. Replaced its long homotopy-quotient lifting calculation by the existing proved
`CochainComplex.IsKProjective.exists_Q_map_eq` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective`.

The delivery includes three fully proved helper modules:
`Sheaf.AlgebraicGeometry.AffinePerfectModuleModel`,
`Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`, and
`Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification`.
The explicit sheafification functor uses tilde, restriction along `hU.isoSpec.hom`, and
`Modules.overEquiv U`. Its zero-morphism-preservation instance is proved.
The model theorem actually applies the sections functor termwise, proves the counit an
isomorphism using retracts of finite free sheaves, and proves K-projectivity from the upper
support bound and projective terms. Derived transport is proved by localizing the explicit
sheaf equivalence. Full derived sheafification composes the existing core affine equivalence
with this transport. The main proof lifts the conjugated arrow by fullness, represents it
by a module chain map, and checks the sheafified map by comparison naturality.

Updated the item's proof route and added DAG records for these three helper theorems.
All four modules compiled in import order without errors or warnings. The shortened main
proof also compiled separately. All writes outside generated compiler artifacts are in the
sandbox; no hand-run git or Lake commands were used.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.perfect_affine_map_representative`
(node `lem-pc-perfect-affine-map-representative`).

Added and proved, with no new holes:
`AlgebraicGeometry.Scheme.affine_perfect_module_model`
(node `lem-pc-affine-perfect-module-model`),
`AlgebraicGeometry.Scheme.affine_localized_site_derived_transport`
(node `lem-pc-affine-localized-site-derived-transport`), and
`AlgebraicGeometry.Scheme.affine_localized_derived_sheafification`
(node `lem-pc-affine-localized-derived-sheafification`).
The private retract-counit lemma and the sheafification instance are also fully proved.

No `sorry` remains in any delivered module, and none was split off. This is one original
hole closed and zero holes added. Existing imported holes below
`exists_affineQCohDerivedEquivalence_core` remain existing stage-3 work: this delivery proves
the main theorem from that interface and does not claim the targets are axiom-free.
No data definition selects an arbitrary object from an unproved existence theorem.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` from the item.
The full theorem `AlgebraicGeometry.exists_affineQCohDerivedEquivalence` and node
`lem-pc-affine-qcoh-derived-equivalence` are not needed on this route; only its existing core
`new-affine-qcoh-derived-equivalence-core` is used. Its shift-normalization clause,
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift`, and node
`new-affine-qcoh-derived-equivalence-shift` are not required by this proof. This is a claim
about this route, not a claim that those modules have no other importers.

Replaced the direct proof import `Mathlib.Algebra.Homology.DerivedCategory.KProjective` in the
item with `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective` to use its
proved chain-map representative lemma; the Mathlib module remains transitively needed.
The affine tilde/Gamma adjunction and node `lem-pc-ring-derived-map-representative` remain
needed, the former through the actual model construction, the latter via the existing
K-projective representative API. No other original proof dependency is discarded.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt already contained substantial, compiling proofs, but lacked the new
nodes and report required for review and delivery. These are now supplied. The original DAG
used the entire affine derived-equivalence interface although this argument uses only its
core factorization and fullness. No existing theorem statement or definition was changed.

The unit `sk-thm-picard-duality` has empty realized-statement and realized-step lists; this
item realizes neither a binding unit statement nor a binding unit step. Its original
three-part affine-model, derived-lift, and conjugation argument is retained.
The core equivalence is used as a generic tool from another unit: it supplies the affine
quasi-coherent derived equivalence, exactly as the original proof requires. The maintainer
can record that tool use; no maintainer-owned `tool_uses` field was edited.

The local literature checkout contains citation tables but no Stacks TeX files. Read the
existing sources from the official pages:
[Tag 08CR, second proof](https://stacks.math.columbia.edu/tag/08CR) and
[Tag 06Z0, affine equivalence](https://stacks.math.columbia.edu/tag/06Z0).
The added construction details are an agent-written elaboration using the actual Mathlib
and source-library APIs named in each new node. LeanSearch was unavailable (HTTP internal
server error), recorded as unavailable; Loogle, LeanFinder and source grep found component
APIs. Searches of the full blueprint for strictly perfect complexes and Tag 06Z0 found no
existing statement duplicating these localized-site helper statements.

Edge cases: the model argument never uses a nonempty open, a positive finite rank, or a
nonzero ring. Rank zero gives the zero free module, retract equations still apply, and
zero terms stay zero under the actual sections functor. The upper bound is precisely the
one supplied by strict perfection. Empty affine opens use the same `isoSpec` and over-site
equivalences. The transport theorem works for arbitrary complexes; it assumes no perfection.
Its two derived-category universe parameters stay independent.

## New nodes

`lem-pc-affine-perfect-module-model`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-perfect-module-model.json`, records the actual
sections-complex construction and its complex counit isomorphism and K-projectivity. Its
module also constructs the affine sheafification functor and proves preservation of zero
morphisms. This node supplies the first part of the original argument and is fully proved.

`lem-pc-affine-localized-site-derived-transport`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-localized-site-derived-transport.json`, records
the derived equivalence obtained from restriction and the over-site equivalence, together
with its natural compatibility with termwise tilde. It is fully proved by Mathlib's
localization API; no additional geometry is left as a hole.

`lem-pc-affine-localized-derived-sheafification`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-localized-derived-sheafification.json`, records
the full functor and factorization needed to lift arrows, obtained by composing the core
affine derived equivalence with the proved transport. It is fully proved from the existing
core theorem. All new nodes inherit the item's chapter and unit and trace to the
proper-flat support argument in `lem-sc-finite-duality`.

No change record is needed: no existing public interface changed and no adaptation was made.

## Second reading by D3

1. Compared each delivered module with the repository baseline. The target theorem signature and all existing declarations are unchanged; the new helper declarations are recorded in their DAG nodes. Verdict: pass.
2. Compiled all four modules with `lcompile.py --all` and compiled the target separately. No errors, warnings, `sorry`, prohibited declarations, or hollow definitions were found. Verdict: pass; the imported open theorem remains the only source of any downstream `sorryAx`.
3. Checked the helper statements against their constructions and edge cases (including the zero and empty affine cases). They are true, strictly intermediate, and not duplicates of existing declarations. Verdict: pass.
4. Verified the proof uses the explicit sections model, localized transport, and core affine equivalence route; the removed full equivalence import is unnecessary. Verdict: pass; the proof is pruned to the declarations actually used.
5. Compared each node's Lean record, proof steps, dependencies, and proof origin with the source. The item's route and unit bookkeeping are preserved, and the three helper nodes describe the delivered declarations. Verdict: pass.

No proof or statement changes were needed during this second reading.
