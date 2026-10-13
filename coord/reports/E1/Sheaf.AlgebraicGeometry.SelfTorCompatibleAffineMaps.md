## What changed

Replaced the sorry in `AlgebraicGeometry.exists_compatible_affine_selfTor_maps`
with a complete Lean reduction. Its existing signature, universes, visibility,
`IsAffineSelfTorChartMap` definition and existing docstrings are unchanged.
Added proof-only imports of `Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates`
and `WeilConjectures.AlgebraicGeometry.Modules.AffineHom`.

The remaining affine lemma supplies source/target coordinates whose conjugated
comparison maps agree on the sections of each whole smaller inverse-image affine
chart for nested affine pairs. It asserts no equality on arbitrary subopens or
incomparable overlaps. The original theorem proves these omitted steps using two
complete private helpers:

1. `affine_model_hom_ext`: identify tensor pullback with ordinary pullback by
   uniqueness of left adjoints. Pullback composition, the chart square, and the
   open-restriction counit identify the restricted affine model with pullback of
   a quasi-coherent associated module. Transport quasi-coherence across the given
   source coordinate. Apply the proved source-library `hom_ext_of_isAffine`
   through the over-site equivalence. Explicitly transport the top-component
   equality along the isomorphism between the image of the top open and the
   terminal over-object. This needs no quasi-coherence of the target.
2. `affine_chart_maps_compatible_of_nested`: restrict the larger-chart map to the
   smaller affine chart and use the preceding extensionality to extend equality
   on whole-chart sections to all subopens. For incomparable charts and arbitrary
   W, construct the sieve of subopens lying over affine neighborhoods inside the
   two charts' intersection. Prove that it covers W, use naturality to identify
   the two restricted images with the smaller-chart image, and apply target
   separatedness. Neither W nor the intersection is assumed affine or compact.

The theorem defines the conjugated chart maps, supplies their coordinate-square
witnesses, and applies the proved descent helper. This is not a one-line
application of a renamed copy of the original statement: the remaining lemma
contains the affine computation and nested section equation, while the Lean proof
supplies affine generation and arbitrary-overlap descent.

Both final modules compiled in dependency order through lcompile.py (4.2 s and
17.2 s in the latest complete check), with no warnings. No other existing module
was edited, and no interface adaptation was required.

## Proved and sorry left

Original holes closed: 1, by name:
`AlgebraicGeometry.exists_compatible_affine_selfTor_maps`
(node `new-n1-self-tor-compatible-affine-maps`). No sorry remains in the item's module.
Both new private helpers have complete Lean proofs.

New holes added: 1, the whole proof of the public theorem
`AlgebraicGeometry.exists_nested_affine_selfTor_coordinates`
(node `new-e1-self-tor-nested-affine-coordinates`), in its own new module.

This is a decomposition, not completion of the transitive proof obligations:
one upper hole is closed and one strictly smaller affine-construction hole is
added, for net 0 before pruning. The lower theorem retains the affine resolution
comparison and normalized localization work, but not affine-source Hom
extensionality or arbitrary-overlap compatibility. Its statement and docstring
specify the exact remaining section equation and complete proof in words.

## No longer needed

No original import or original downstream module is pruned.
Removed from the upper node's direct `proof_deps`:
`lem-sc-affine-open-kernel-conormal-sections` and
`lem-sc-affine-quotient-resolution-sheafification`. Both are retained in the
new nested-coordinate node's proof plan; neither is claimed as globally pruned.
The original quotient-resolution and kernel-conormal-section dependencies remain
needed by the nested-coordinate construction, although no longer direct
proof dependencies of the item's descent argument. The normalized algebraic
comparison is still used explicitly, so its public import and node remain needed.

A separate quasi-coherence theorem for exterior sheaves is unnecessary: the
source coordinate supplied by the affine construction already identifies the
source with an affine pullback model. No exterior-quasi-coherence statement,
module or node is delivered. No separate source-Hom-extensionality module is
needed; the helper is private and fully proved in the item.

The previous attempt's false `compatible_of_affine_selfTor_chart_family` and
`exists_affine_selfTor_chart_family` are not imported, recreated, or relied on.

## Where the brief, the DAG or earlier work was wrong

The previous report correctly refuted compatibility of arbitrary chart coordinate
choices, but that does not refute the original existence theorem. Negating a
target coordinate on only one chart preserves the chart predicate and can
violate compatibility. The new affine lemma explicitly chooses one family and
requires a nested section equation; the upper proof never infers compatibility
from the bare chart predicate or claims that arbitrary coordinates agree.

Equality of top components alone does not imply equality of arbitrary sheaf
morphisms. The proof supplies the missing property: the source's affine model is
quasi-coherent on an affine inverse-image chart. The target remains arbitrary.
It does not assert that restrictions to arbitrary opens are surjective.

Read the original DAG's three proof dependencies and their actual Lean signatures.
`exists_affine_quotient_sheafified_resolution` gives a quasi-isomorphism of an
augmentation, not the fixed derived-tensor homology identification or its
localization coherence. Those are genuine remaining work in the new affine node.
`affineOpen_kernel_conormal_sections` fixes ideal classes through the unit but
does not itself supply the exterior or derived coordinate isomorphisms.
Their sources and original proof route are preserved in the new node.

The blueprint unit `sk-thm-picard-duality` has empty realized arrays. Its route and
all unit/chapter records are untouched. The reduction follows the original affine
Koszul computation and does not bypass a unit.

Edge cases checked in the statements and proof: n=0, zero ideal, zero quotient,
empty charts and nonregular ideals. Quasi-coherence of the affine model needs no
finite generation or local freeness. The covering sieve works for arbitrary,
possibly non-quasi-compact intersections; the empty W is covered vacuously.
In particular no arbitrary coordinate uniqueness or global map is assumed.

Searches: LeanSearch returned Internal Server Error for the relevant queries,
recorded as unavailable without an absence conclusion. LeanFinder found ideal
sheaf localization and general Hom extensionality APIs, not a normalized affine
self-Tor construction. Local rg found the proved source-library affine Hom
theorem, which is used. The new node records all three search kinds. Read Stacks
09PQ, 01R3 and 06YH; 06YH is a definition, so the affine node cites the preceding
K-flat comparison construction as well. Source coordinate generation is proved
through the existing pullback/restriction API rather than left as another hole.

## New nodes

`new-e1-self-tor-nested-affine-coordinates`, module
`Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates`: the affine resolution,
conormal-coordinate and normalization steps through equality on nested affine
whole-chart sections. It records the original quotient-resolution,
conormal-section, exterior-restriction and normalized-comparison dependencies,
with a complete natural-language proof and the precise Lean statement.

Updated the original node's `proof`, `proof_deps` and `proof_origin` to describe
the compiled reduction. No definition/statement change record is needed: all
existing public interfaces are identical.

## Second reading by E1

1. Interface check: PASS. Diffed the only existing delivered module against the
repository. Checked the existing theorem signature byte for byte and the entire
`IsAffineSelfTorChartMap` body. Both are unchanged, as are their docstrings,
universes and visibility. Only two proof-only imports, two proved private helpers
and the theorem proof were added. The other Lean module and its node are new;
there are no forced adaptations or changed targets.

2. Proof and axioms: PASS as a decomposition. Compiled both files in import order
using lcompile.py (4.0 s and 19.3 s). Compiled a scratch copy with `#print axioms`
for the definition, both helpers, the original theorem and the new theorem.
Both private helpers use only propext, Classical.choice and Quot.sound. The
public definition/theorems additionally use sorryAx from the remaining normalized
comparison or affine-coordinate obligations. There is exactly one delivered
sorry, the whole proof of `exists_nested_affine_selfTor_coordinates`. No axiom,
unsafe, opaque, extern, implemented_by, hidden sorry or new data definition occurs.
The existential coordinates are destructured inside a proof of a proposition;
no arbitrary witness is installed as definition data.

3. Split statement: PASS. Read its full statement, source, proof docstring and
node, and the actual signatures of the original resolution and conormal lemmas.
The remaining claim is affine coordinate construction and equality only on whole
nested-chart sections. It does not assume arbitrary-overlap compatibility.
The upper proof genuinely supplies source quasi-coherence, affine Hom
extensionality, restriction to subopens and arbitrary-overlap descent. Checked
n=0 (quotient unit), zero ideal (positive exterior powers vanish), zero quotient
and empty charts (zero modules), and nonregular ideals (comparison need not be an
isomorphism). No finite generation, local freeness or quasi-compact intersection
hypothesis was introduced. Read Stacks 09PQ, 01R3 and 06YH, confirming the last
is a definition whose preceding K-flat construction is also cited. Independent
LeanFinder searches on affine global-section detection/gluing and on derived
self-tensor/conormal localization found general Hom and cotangent APIs, not this
coordinate construction. Loogle's ModuleCat isomorphism query returned general
linear-equivalence APIs. Local rg confirmed the existing proved affine Hom lemma
is already used and found no existing normalized coordinate theorem. The affine
construction is substantial and cannot be closed by a short available lemma.

4. Route and pruning: PASS after report correction. Read both helpers top down.
The first uses the proved upstream affine Hom theorem, without a new hole for
exterior quasi-coherence. The second restricts maps to smaller affine charts and
uses the covering sieve and target separatedness; it works for arbitrary W.
The two added imports are proof-only and both are used. The unchanged public
imports supply the statement/definition APIs. The unit's realized statement and
step arrays are empty; no unit or chapter record was changed or bypassed.
Corrected `No longer needed` to name every old direct proof dependency removed
from the upper node, while distinguishing retention in the lower proof plan from
global module pruning. No module is claimed as pruned.

5. DAG agreement: PASS. The upper node's steps and proof_deps describe the actual
coordinate composite, affine Hom argument and sieve descent. The lower node has
its matching Lean statement, complete proof plan, source, searches, status,
creation record, blueprint ancestry, chapter/unit and Lean record. Its proof_deps
are exactly the union of its step uses and preserve the original affine route.
No existing node field outside the permitted proof/Lean fields was changed.

Second reading changed only this report: explicit removed-direct-dependency
accounting and this independent review. The Lean proofs and node records needed
no repair. One original hole is closed and one smaller hole is added: net zero,
a decomposition, with the two descent helpers fully proved.
