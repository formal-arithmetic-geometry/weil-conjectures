## What changed

Proved `AlgebraicGeometry.exists_flat_module_tensor_model` without changing its signature,
universes, public imports, or visibility. The proof constructs the X-algebra tensor
cancellation equivalence, transports module flatness through the resulting pushout,
uses `Algebra.limitModuleFinitePresentation`, selects a flat stage, proves its three
finite-presentation conditions, and checks both inclusion identities needed for the
final algebra and module comparisons. All chosen data occur inside this existential
proposition proof; there is no new definition or arbitrary data chosen in a definition.

Added proof imports `Mathlib.RingTheory.IsTensorProduct`,
`Mathlib.RingTheory.FiniteStability`, `Sheaf.RingTheory.FiniteTypeApproximationFlatLoci`,
and `Sheaf.RingTheory.FiniteTypeApproximationFlatStage`. The flat-loci theorem isolates
original DAG step 3 and the local part of step 4 for an already supplied diagram.
It asserts local flatness, openness, persistence, and pointwise covering, rather
than model existence. It constructs neither a globally flat stage, the approximation,
the finite presentations, nor the tensor comparisons.

The flat-stage module is proved completely. It only assumes a persistent open
cover at a ring colimit, proves its global directed-cover argument, descends ideal
membership by span induction, descends the unit equality using eventual equality,
and applies the maximal-prime criterion. It handles the distinction between the
two induced scalar actions on localized modules by an explicit equality on fractions.

Updated the item's proof DAG to follow the written proof. Added two new modules and
nodes: one admitted local-flatness/persistence argument and one proved global
open-cover/unit-relation argument. The unit
`sk-thm-picard-semicon` has no realized node at this level; its semicontinuity and
base-change route is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_flat_module_tensor_model`
(node `lem-pc-flat-module-tensor-model`). The item's module now contains no `sorry`.

Added one hole:
`Algebra.exists_flat_finiteType_approximation_loci`
(node `lem-pc-finite-type-approximation-flat-loci`), in
`Sheaf.RingTheory.FiniteTypeApproximationFlatLoci`. Its proof is exactly `by sorry`;
its docstring and node carry the complete source argument and existing dependencies.
This is a decomposition: 1 original hole closed, 1 strictly smaller hole added,
net 0 holes, rather than a complete proof of flat-model existence.

Additionally proved:
`Algebra.exists_flat_finiteType_approximation_stage`
(node `lem-pc-finite-type-approximation-flat-stage`), and its private helpers
`ideal_mem_lift` and `ideal_unit_descends`. These contain no holes.

All three delivered modules compile cleanly with `lcompile.py --all`; the main module's
proof has no admitted glue. The final dry run also checks the declaration axioms.
The two new statements were checked against Stacks Tag 02JO (1), proof paragraphs 1--3,
read at https://stacks.math.columbia.edu/tag/02JO. The explicit colimit, semilinearity,
and canonical tensor hypotheses prevent unrelated diagrams from satisfying it.
Zero modules cause no exception. Zero limit rings have empty spectrum, but the
finite unit relation still descends, so no nontriviality assumption was added.
A one-stage diagram reduces to the given flatness transported through its canonical
comparisons. The nonempty index hypothesis is retained. The proof handles different
ring and module universes and uses the original max-universe bounds.

## No longer needed

Removed five direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`;
- `Sheaf.RingTheory.ColimitEventuallyFlat`;
- `Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule`;
- `Sheaf.RingTheory.FlatModuleAtPrime`;
- `Sheaf.RingTheory.OpenFlatLocus`.

Four are dependencies of the isolated flat-loci argument and remain proof imports
of `FiniteTypeApproximationFlatLoci`: their nodes are still needed and are not
claimed as pruned.
The `FilteredColimitAlgebrasUnderlyingModule` import and direct node
`lem-weil-pbc-filtered-colimit-algebras-underlying-module` are unnecessary for this
route: the approximation already supplies its abelian-group colimit and module
comparisons, and the local criterion accepts ring and abelian-group colimits.
Other consumers may still need this node/module; no whole-library pruning is claimed.

The remaining original proof dependencies now reside either in the item's proved
finiteness/tensor/approximation steps, in the admitted node's local-flatness and
persistence steps, or in the proved global stage-selection argument. No other
original branch is discarded. The approximation's
additional P-module comparison is not used: the requested comparison is Y-linear,
and its Q-module comparison already supplies it once the induced Q-action is checked.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. `RingTheory.exists_flat_stage`
requires local stage rings and local transitions; it cannot be applied directly to
the global approximation returned by `Algebra.limitModuleFinitePresentation`.
The admitted theorem captures the missing localize-and-persist argument; the
globalize argument is proved separately.
The existing ring-only `RingHom.exists_flat_finitePresentation_model` and the
source library's compact flat-localization results concern top rings themselves,
so they do not replace this arbitrary-module step.

Searches used LeanFinder, Loogle, Mathlib grep, and searches of both library roots
and the blueprint/DAG. LeanSearch returned Internal Server Error, recorded as
unavailable. No exact existing flat-stage result for the supplied global module
diagram was found. On this machine the cited literature file is not populated;
the named Stacks tag was read directly online. No source, target, or dependency
signature was changed, and no forced adaptation is required.

## New nodes

`lem-pc-finite-type-approximation-flat-loci`:
`Algebra.exists_flat_finiteType_approximation_loci` in
`lean/Sheaf/RingTheory/FiniteTypeApproximationFlatLoci.lean`. The one remaining hole
is the supplied-diagram local-flatness, openness, persistence and pointwise-covering
argument of Tag 02JO (1), before compactness. Its docstring has the complete source
argument. Its node lists stage finiteness, localized colimits, local eventual
flatness, and open flat-locus persistence as proof steps with their existing nodes.

`lem-pc-finite-type-approximation-flat-stage`:
`Algebra.exists_flat_finiteType_approximation_stage` in
`lean/Sheaf/RingTheory/FiniteTypeApproximationFlatStage.lean`. This is proved without
holes. Given an open persistent flat cover at a ring colimit, it proves compactness,
unit-ideal descent, and global flatness at one stage. Its assumptions contain no
finite-presentation approximation or limit-flatness hypothesis. Its private helper
proofs use Mathlib's colimit representatives and eventual equality, with induction
on ideal-span membership. The node records this proof and its Mathlib dependencies.

Both nodes inherit the item's chapter/unit and name the same blueprint ancestor
through the item. No existing signature or visibility changed, and no change record
is needed. The only new admitted theorem is strictly a part of the original argument;
the original theorem combines actual approximation, tensor and finite-presentation
proofs with the proved global-stage argument, rather than applying a renamed copy
of itself.

## Second reading by P4

1. Compared the delivered main module against the repository with `diff -u` and
   checked the theorem signature as an exact byte string through `:= by`.
   Verdict: unchanged universes, parameters, assumptions, conclusion, public imports,
   and visibility. The two other delivered modules are new. No definitions or
   existing signatures change, so there is no change record. Restored the existing
   theorem docstring verbatim; the updated route remains recorded in the DAG and report.
2. Read all three modules, including ideal-span induction, eventual equality,
   contraction naturality, and the explicit equality of localized scalar actions.
   All three compile through `lcompile.py`. Scratch copies with `#print axioms`
   show only `propext`, `Classical.choice`, and `Quot.sound` for
   `Algebra.exists_flat_finiteType_approximation_stage`; the local-loci and main
   theorems additionally use `sorryAx` from open statements. Exactly one delivered
   theorem has a direct hole: `Algebra.exists_flat_finiteType_approximation_loci`.
   It is public, wholly `by sorry`, documented, and has its matching node.
   No prohibited declarations, hollow definitions, or data definitions were added.
   Verdict: valid checked reduction, not a completed flat-model proof.
3. Read Stacks Tag 02JO (1), proof paragraphs 1--3, directly at
   https://stacks.math.columbia.edu/tag/02JO, and read the imported local-stage,
   flat-localization, and open-flat-locus declarations. The remaining statement
   handles only local eventual flatness, openness, and persistence for a supplied
   canonical diagram. It does not supply the approximation, global flat stage,
   finiteness conversions, or final comparisons. Its natural transformations,
   semilinearity, and pure-tensor formulas give the compatibilities required by
   the source argument. Zero modules, a singleton index, and a zero limit ring
   introduce no exception: the cover can be empty when the limit spectrum is,
   and the unit relation still descends to a zero stage when necessary.
   Repeated searches with different wording using LeanFinder, Loogle, and `rg`
   across Mathlib and both library roots found no direct replacement. Loogle's
   first query reported an unknown identifier; a valid string query returned
   localization criteria, including the criterion already used in the proof.
   Verdict: the admitted statement is true and strictly an intermediate part;
   formalizing its localized diagrams is not a few-minute closure.
4. Checked the route top downward: actual tensor cancellation and flatness
   transport precede approximation; the proved global-stage theorem supplies
   compactness and unit descent; finite presentation and both inclusion formulas
   are proved afterward. Compared every original `proof_deps` against the new
   main and intermediate dependencies: only
   `lem-weil-pbc-filtered-colimit-algebras-underlying-module` is no longer needed.
   All other removed direct imports remain dependencies of the local-loci step.
   Read `dag/units/sk-thm-picard-semicon.json`: its realized statement and step
   lists are empty, and the unit's semicontinuity/base-change route is preserved.
   Checked proof-only imports; removing the concrete-colimit import breaks the
   representative/equality lemmas, so it is required. Verdict: genuine reduction,
   net zero holes, with precisely the reported branch pruned.
5. Read all three node records against their Lean signatures and proof bodies.
   The main node records the pushout, approximation, local-loci/global-stage
   reduction, finite-presentation conversions, and inclusion identities.
   The global-stage node describes the proved span-induction and maximal-prime
   argument; the admitted node describes the localized source argument and its
   dependencies. New nodes have sources, statements, search records, creation
   metadata, blueprint ancestry, chapter/unit, and matching Lean records.
   Verdict: nodes and Lean agree; no existing statement was altered.

Second-reading changes: restored the original theorem docstring. Import-minimality
checks confirmed that FiniteStability supplies the required finite-presentation
base-change instance and ConcreteCategory.Basic supplies the colimit representative
and eventual-equality lemmas; both proof imports are retained. No proof or statement
was rewritten. This delivery closes one original hole and adds one strictly smaller
hole, a decomposition with net zero holes.
