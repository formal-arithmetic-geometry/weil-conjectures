## What changed

Replaced the hole in `ModuleCat.exists_shift_square_data` with an explicit proof from
an ordinary comparison square over `E = A ⊗[R] B` and a coefficient-map homology square.
The original theorem's binders, statement and visibility are unchanged. Added two
proof-only imports, `BaseDerivedTensorOrdinaryShiftModel` and
`TensorCoefficientShiftHomology`. No existing definition or interface changed. The second reader also added the
proof-only import `Sheaf.CategoryTheory.RightKanExtensionCoherentShift` to the
ordinary-model helper, matching its recorded remaining proof dependency.

`ModuleCat.tensorCoefficient_shift_homology` is fully proved for arbitrary ring maps
`f : A →+* E` and `g : E →+* C`. Tensor-generator equations prove the complex square;
restriction/homology naturality and the proved upstream exact-functor shift theorem
prove its homology square. This result does not assume a derived model or any flatness.

The main proof defines `eS` by extending the ordinary E-linear cohomology isomorphism.
It applies the injective extension/restriction adjunction hom equivalence, rewrites both
models' `localized_eq`, composes the ordinary and coefficient squares, and cancels the
isomorphism. There is no deferred adjunction assembly or localized comparison square.

The remaining ordinary-model construction has its own module and node. Its proposed
proof uses the existing, proved `rightKanExtension_coherentShift` for the universal
counit, then reindexes and transports the model's ordinary data. No arbitrary witness
of mere model existence is selected by the main proof, and no new definition uses an
unproved existence theorem.

All three modules compile together without warnings through `lcompile.py`. The
coefficient proof includes the signs through the canonical shift maps, rather than
asserting a new shift convention. New statements were checked on n=0, zero complexes
and zero rings; neither proof uses flatness or invertibility of a comparison.

## Proved and sorry left

Closed the original hole: `ModuleCat.exists_shift_square_data`, node
`lem-pc-localized-tensor-comparison-shift-square-data`.

Also proved the new theorem `ModuleCat.tensorCoefficient_shift_homology`, node
`lem-pc-tensor-coefficient-shift-homology`, with no new holes or assumptions.

Added exactly one deferred theorem:
`ModuleCat.exists_baseDerivedTensor_ordinary_shift_model`, node
`lem-pc-base-derived-tensor-ordinary-shift-model`. Its proof is exactly `by sorry`,
with its source, construction and edge cases in its docstring. It asserts an E-linear
ordinary comparison square, not the C-linear localized square. The coefficient map,
restriction/homology square and adjunction passage have been removed from the
remaining argument.

This is a decomposition: one original hole closed and one strictly smaller hole added,
net zero holes. It is not a claim that derived-model shift transport is proved. There
are no other sorries in the delivered files.

## No longer needed

None. The original module had only its public model import, which its statement still
needs. No original import, node or module has become unused. The ordinary comparison
helper and the proved coefficient helper are both used by the new proof. The existing
coherent Kan shift theorem is a generic proved tool for the remaining model construction;
it does not replace a step of the unit route. No unit or chapter route was changed.

## Where the brief, the DAG or earlier work was wrong

The original node described all model transport and localization assembly in one proof
step and cited only the model definition. The explicit construction and its ordinary
square are now a separate item, while the coefficient and adjunction portions are Lean
proofs. The generic counit-compatible shift theorem already exists as the proved
`CategoryTheory.Functor.rightKanExtension_coherentShift`; its signature was read and
it is named in the remaining node's proof plan.

The local Stacks source files are absent in this clone. I read the existing source places
online: [06Y6](https://stacks.math.columbia.edu/tag/06Y6),
[08IB](https://stacks.math.columbia.edu/tag/08IB), and
[0DJA](https://stacks.math.columbia.edu/tag/0DJA). Tag 06Y6 belongs to More on Algebra,
not `perfect.tex`; the new node identifies the separate source documents. The arguments
making the explicit Lean squares are recorded as agent-written elaborations of these
source places.

`blueprint_refs.py ancestor` returns `None` for the item because `created.item` stores
module names in recent deliveries, while its traversal looks up node ids. The existing
parent shift-square node explicitly records the blueprint ancestor
`lem-pc-rf-perfect-base-change`. The new nodes retain that ancestor and name the precise
shift-reduction substeps, with the intervening nodes recorded; no project tool was
edited or bypassed.

Searches used LeanFinder, Loogle and local rg/grep across Mathlib, WeilConjectures,
Sheaf and the DAG. LeanSearch returned Internal Server Error; this is recorded as
unavailability, not absence of a theorem. No specialized ordinary model transport or
coefficient shift square was found. The upstream generic homology shift compatibility
was found, its type and proof read, and it is used by the coefficient proof.

## New nodes

`lem-pc-base-derived-tensor-ordinary-shift-model`:
`Sheaf.Algebra.Homology.BaseDerivedTensorOrdinaryShiftModel`, declaration
`ModuleCat.exists_baseDerivedTensor_ordinary_shift_model`. The one remaining hole is
transport of derived E-cohomology and its ordinary counit comparison. It omits the
localized square and does not assume a model's comparison is invertible.

`lem-pc-tensor-coefficient-shift-homology`:
`Sheaf.Algebra.Homology.TensorCoefficientShiftHomology`, declaration
`ModuleCat.tensorCoefficient_shift_homology`. Fully proved, for arbitrary composable
coefficient ring maps; no derived transport hypothesis is present.

There are no change records or forced adaptations because no existing signature,
definition or public import changed.

## Second reading by F3

1. Compared the delivered item with the repository using `diff -u`: its only
   changes are two plain imports and the body of `ModuleCat.exists_shift_square_data`.
   The binders, universe, typeclass assumptions, let expressions, conclusion,
   visibility and original docstring are byte-for-byte unchanged. The other two
   modules are new; there are no adaptations, definition changes or change records.
   Verdict: no existing interface or target meaning changed.

2. Read all three modules and compiled the set through `lcompile.py`. The tensor
   generator calculation proves the complex square, then the upstream proved
   exact-functor homology shift lemma and two naturality equations prove the
   coefficient square. The main proof applies the injective adjunction hom
   equivalence, rewrites both `localized_eq` fields, substitutes the two squares
   and cancels `eS`. Scratch `#print axioms` checks gave only `propext`,
   `Classical.choice`, `Quot.sound` for `tensorCoefficient_shift_homology`, and
   those plus `sorryAx` for the ordinary helper and the main theorem. The sole
   delivered hole is the named ordinary helper; there are no new definitions,
   forbidden declarations or arbitrary data definitions chosen from existence.
   Verdict: valid proof conditional on the one reported hole, not a closed target.

3. Read the remaining ordinary helper against every model field, especially
   `cohomologyIso_smul` and `comparison_eq`. Keep the original universal pair;
   Kan shift compatibility identifies its shifted values and counit. Reindex
   the E-modules by j-n and compose the old B-cohomology isomorphism with the
   inverse derived homology shift isomorphism. Naturality for a times identity
   verifies the A-action; B-linearity supplies the other factor. Set the new
   comparison to the old comparison followed by the inverse ordinary homology
   shift. Counit compatibility proves its required equation. Construct the
   coefficient map on generators and transpose to fill localizedComparison.
   This proves an ordinary E-linear square; the C-linear coefficient square and
   adjunction passage are separate, fully checked work. Thus this is a strict
   part of the original argument, not a renamed localized square. For n=0 and
   e=identity take mL=mK and the canonical reindexing; for zero complexes the
   cohomology objects are zero via their model isomorphisms; zero rings and
   nonflat maps require no extra condition. No comparison is cancelled as an
   isomorphism. The coefficient helper assumes precisely its generator formulas
   and arbitrary composable ring maps. Repeated searches with LeanFinder
   (`right Kan extension shift equivariance derived tensor counit compatibility`),
   Loogle (`CategoryTheory.Functor.mapHomologicalComplexHomologyIso`) and grep
   (`counit.*shift|shift.*counit|comparison.*translation|homology.*coefficient`),
   plus local source searches, found generic tools but no existing specialized
   model transport. The remaining multi-field transport is not a few-minute
   hole. Verdict: the one deferred statement is true and strictly simpler.

4. Read the original proof dependency (the model), both new helpers, the proved
   Kan shift theorem and the upstream homology shift proof. No shorter complete
   route was found. Both added imports of the main module are proof-only; the
   helpers' public model import supplies their statement's shift instances
   (notably `ModuleCat.extendScalars_additive`). The coefficient helper's plain
   upstream import is used only in its proof. No old proof dependency or import
   is unused: the old list contained only the model, still used throughout.
   `dag/units/sk-thm-picard-semicon.json` has empty realized lists; no realization
   or unit step is replaced. The closed Kan theorem is a generic tool, not a
   replacement unit argument. Verdict: no pruning or unit-route change.

5. Compared the three node statements and stored Lean signatures with the code.
   The main node records exactly ordinary transport, coefficient homology and
   adjunction assembly. Both new nodes have source, proof, search, creation,
   blueprint ancestry, chapter/unit and Lean records. Corrected the coefficient
   node to record the model node as a proof dependency: its proved additive
   instance is needed for the canonical extension shift maps. Added the missing
   plain Kan-shift import to the deferred ordinary module to match its plan.
   Corrected a generator typo in the new coefficient node. Read Stacks
   [06Y6](https://stacks.math.columbia.edu/tag/06Y6),
   [08IB](https://stacks.math.columbia.edu/tag/08IB),
   [05G3](https://stacks.math.columbia.edu/tag/05G3) and
   [0DJA](https://stacks.math.columbia.edu/tag/0DJA): the sources provide derived
   tensor exactness, the base-change comparison, scalar-extension adjunction and
   tensor inheritance, respectively. They do not literally state these Lean
   shift squares. Clarified that attribution in the new modules and nodes;
   their detailed proofs are agent-written algebraic ingredients. Verdict:
   records agree after these repairs.

Second reading changed dependency bookkeeping, the missing proof-plan import,
a generator typo and source attribution; it did not change any Lean statement
or proof body. One original hole is closed, one new hole is added: net zero,
a decomposition. The new coefficient theorem is fully proved.
