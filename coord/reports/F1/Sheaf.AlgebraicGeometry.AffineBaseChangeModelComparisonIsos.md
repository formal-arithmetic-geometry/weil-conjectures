## What changed

Replaced the earlier attempt with a reduction following the original node's plan.
The existing declaration `AlgebraicGeometry.exists_affineBaseChangeModelComparisonIsos`
keeps its signature. Its proof constructs stage and limit derived equivalences
using the already proved `Scheme.exists_scheme_iso_derived_equivalence`, obtains
their localization comparisons, and assembles the comparison-data proposition
from the remaining model-isomorphism construction.

Added `Sheaf.AlgebraicGeometry.AffineBaseChangeSchemeComparisons`, fully proved:
it identifies each explicit pushout ring and its colimit with the geometric
pullback, and proves all four projection/transition compatibility clauses.
The proof uses Mathlib's affine pushout/pullback theorem, the equivalence of
the order tail with `Under i`, `IsColimit.underPost`, preservation of connected
colimits by the forgetful functor, and the two pushout projection equations.

Added `Sheaf.AlgebraicGeometry.AffineBaseChangeModelIsosOfSchemeComparisons`:
its sole remaining theorem takes compatible scheme identifications and fixed
localized derived equivalences as inputs. Its conclusion uses the existing `affineModelComparisonData` proposition,
constructed with the supplied transports, four model isomorphisms and two Hom
equations. The predicate is kept folded instead of duplicating its large formula. It applies to any ring
diagram and cocone having those identifications; directedness, colimit
identification, and existence of derived transports are no longer its work.
Explicit E,K inputs and their defining equalities avoid repeatedly unfolding
scalar-extension complexes when assembling the large comparison proposition.

Updated the existing node's proof route and added matching records for the two
new modules. The second reader removed seven unchanged dependency copies from the sandbox
Lean tree after verifying that the published compiled library contains them;
only the three changed/new modules are delivered. No existing definition, theorem signature, or visibility changed.

Sources read: Stacks Project [01JO](https://stacks.math.columbia.edu/tag/01JO),
[09RE](https://stacks.math.columbia.edu/tag/09RE),
[08DW](https://stacks.math.columbia.edu/tag/08DW), and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S),
[064K](https://stacks.math.columbia.edu/tag/064K), and
[06Y1](https://stacks.math.columbia.edu/tag/06Y1), together with the existing
proof-dependency declarations and Mathlib APIs. LeanSearch returned Internal
Server Error; Loogle, LeanFinder and local source search supplied the other searches.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_affineBaseChangeModelComparisonIsos`
(node `lem-pc-affine-base-change-model-comparison-isos`).
Proved the new theorem
`AlgebraicGeometry.exists_affineBaseChangeSchemeComparisons`
(node `lem-pc-affine-base-change-scheme-comparisons`) without sorry.

Added one named hole:
`AlgebraicGeometry.exists_affineBaseChangeModelIsosOfSchemeComparisons`
(node `lem-pc-affine-base-change-model-isos-of-scheme-comparisons`).
Its proof is exactly `:= by sorry`, and its docstring states the source and
complete construction and naturality argument. There are no sorries in the
item's module and none inside definitions. This is a decomposition: one upper
hole closed, one strictly smaller model-comparison hole added, net zero holes.
It is not a complete proof independent of sorry.

## No longer needed

Removed the item's proof-only import of
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`; it belongs to the
remaining model-comparison module and stays imported there. The original
`Sheaf.Algebra.Homology.BoundedFlatKFlat` import is removed: the proof uses the
proved upstream `CochainComplex.kFlat_of_isStrictlyLE_of_flat` directly and the
existing native predicate recorded by `def-pc-module-kflat-complex`. The remaining model theorem uses the
already proved `Sheaf.Algebra.Homology.KFlatModuleBaseChange` for preservation
under further extensions. Consequently no existing
module or original proof dependency is claimed globally pruned.

The old proof dependencies no longer used directly by the item's proof are:
`def-pc-scheme`, `lem-pc-module-bounded-flat-kflat`,
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-perfect-hom-transport`, and
`lem-pc-ringed-spaces-derived-pullback-composition`.
These declarations are supplied by existing upstream results or remain needed
transitively by the geometric or model-comparison theorem,
or by the unchanged statement. This is a redistribution of proof dependencies,
not global pruning. In particular PerfectHomTransport remains a public import
because affineModelComparisonData uses its maps.

Discarded the earlier sandbox's proposed components/completion theorems and
nodes (`lem-pc-affine-base-change-model-comparison-components` and
`lem-pc-affine-base-change-model-comparison-completion`). Neither is used or delivered.
No unit realization is bypassed or removed.

## Where the brief, the DAG or earlier work was wrong

The earlier components theorem quantified over an arbitrary F unrelated to
R and the geometric pullbacks. It is false: choose constant rational R and
Y=Spec Q, but constant zero-ring F. The zero-ring spectrum has a zero module
and derived category, whereas Spec Q has a nonzero module in degree zero;
the asserted derived equivalences cannot exist. Its completion theorem also
retained the whole original conclusion under a stage-equivalence hypothesis,
so it failed to separate the complex construction from the geometry.
Both proposals have been replaced, and the stale second-reading section was removed.

The original node's mathematical route is retained. Bounds are now used in a complete Lean proof only for
K-flatness of the complex models, not to assert an affine equivalence for
arbitrary ring diagrams. All new statements were checked on zero rings,
zero complexes, equality of indices, empty spectra, and the nonempty upper tail.

## New nodes

`lem-pc-affine-base-change-scheme-comparisons`: the geometric part of original
proof step 1, now fully proved, with all ring-to-scheme transition equations.

`lem-pc-affine-base-change-model-isos-of-scheme-comparisons`: original proof
steps 2–3 after the scheme identifications and derived transports are supplied.
It takes native K-flat input models, compatible scheme identifications and fixed
localized transports, and packages the resulting model isomorphisms and equations
in the existing comparison-data proposition. It needs no directedness or colimit
proof and does not construct any geometric identification. This is the single
remaining item.

No change records or forced adaptations are needed.

## Second reading by F1

1. Compared every delivered existing module against the repository. The original
   theorem signature is byte-for-byte identical, including its hypotheses,
   universe parameters, specified models and conclusion. Its existing node differs
   only in `proof`, `proof_deps` and `proof_origin`. No existing definition,
   visibility or target statement changed. Seven byte-identical dependency copies
   were removed from the delivery tree; their published compiled modules are used.
   Verdict: pass.

2. Compiled the three delivered modules through lcompile.py in import order.
   There is exactly one `sorry`, in the named new model-comparison theorem;
   neither the item nor the geometric theorem contains one. No axiom, unsafe,
   opaque, implemented_by, extern or data-valued sorry occurs. The geometric
   theorem's axiom print contains only propext, Classical.choice and Quot.sound.
   The item and remaining model theorem additionally use the expected sorryAx.
   Derived-equivalence witnesses are chosen only inside a proposition proof from
   an already proved theorem; no definition chooses an arbitrary unproved witness.
   Verdict: pass, with the reported model-comparison hole.

3. Read the remaining theorem from its inputs down to the comparison proposition.
   It receives the full scheme identifications, all four projection/transition
   equations, native K-flat complexes, their actual scalar-extension equalities,
   and localized derived transports. Unlike the original theorem, it does not
   establish geometry, directed-tail colimits, boundedness or existence of these
   transports. This is a genuine remaining part of the argument, not the original
   theorem renamed. Its source and complete construction/naturality proof are in
   its docstring. Checked zero complexes, zero rings/empty spectra, equal indices,
   arbitrary non-flat scalar maps and the nonempty initial tail. The supplied
   identifications exclude the earlier false arbitrary-diagram example. Searched
   with alternate terms using Loogle, LeanFinder, msearch grep and local rg;
   no existing complete natural comparison lemma was found. The native K-flat
   definition and upstream bounded-flat theorem already exist and are reused.
   The remaining naturality construction could not be closed in a few minutes.
   Verdict: one true, strictly smaller named hole with its matching node.

4. Read the geometric proof and the item's reduction top down. The former uses
   Mathlib pushout/pullback universal properties, the tail equivalence and
   preservation of connected colimits. The latter reuses the proved scheme-iso
   derived equivalence and upstream bounded-flat criterion directly. Proof-only
   imports are plain imports; public imports supply symbols or instances in the
   new signatures. `No longer needed` now lists all five old dependencies absent
   from the item's direct proof, without claiming transitive/global pruning.
   The unit sk-thm-picard-semicon retains its pre-existing
   `realized.statement = []` and `realized.steps = [[]]` entries; no unit realization or route was removed.
   Verdict: pass; this delivery is a decomposition, net zero holes, not a complete
   proof or a globally pruned library.

5. Checked all three node records against Lean. New `lean.statement` fields are
   verbatim signatures; every `proof_deps` is exactly the union of the proof-step
   `uses`. Sources, origin, creation records, searches, chapter and unit agree
   with the constructions and the single remaining hole. Only permitted proof
   metadata changed on the existing node. Verdict: pass.

Second-reader repairs: restored exact original-signature whitespace; removed
unchanged dependency copies; reused the native K-flat predicate instead of an
expanded acyclic-total-tensor condition and used the proved upstream bounded-flat
criterion; kept affineModelComparisonData folded in the remaining theorem's
conclusion instead of duplicating and matching its large existential formula.
The item still explicitly constructs geometry and selects localized derived
transports. This definition reuse reduced its kernel-checking time from a
60-second timeout to about 11 seconds, without splitting a file, changing a
limit or introducing a definition. Updated both new/old proof records and the
report to describe this final folded conclusion honestly. No split-off theorem
was discharged; the geometric theorem is fully proved, and one upper hole is
replaced by one strictly smaller hole.
