## What changed

Reduced `AlgebraicGeometry.ProEtale.constructibleCocone_homSurj` to the existing
single-constructible-sheaf continuity theorem and the new coefficient complex presentation.
The parent proves the bounded-source argument: finite-stage factorization for shifted single
sheaves, closure under distinguished triangles using monic cocone legs, bounded devissage,
transport between colimit cocones, and the final tensor/restriction adjunction calculation.
It also proves monicity of the coefficient legs directly from the comparison equation and
faithfulness, so monicity is not part of the new unproved statement.
The comparison component lemmas use `map_preimage` to account for the chosen preimages in
`fullyFaithfulCancelRight`. The second reading made the private single-sheaf and bounded
factorization helpers accept a colimit witness, and made the cocone helper reuse its supplied
colimit proof. This avoids repeatedly elaborating the default complex-colimit construction.
It also caches the exact-derived comparison in a private definition shared by the shift and
triangulated proof instances, avoiding repeated elaboration of that same comparison.

Added `Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison` below the parent so the
presentation statement can use the same canonical functors, adjunctions, Hom equivalences
and tensor comparison without a cycle. The original three scalar-extension names retain
their signatures and definitionally equal values as abbreviations. The extraction is recorded
in `coord/changes/B2-finite-derived-tensor-comparison.md`. No other existing module is edited.

Added proof imports for single-sheaf continuity, filtered colimits of abelian groups,
small-category enlargement and final undercategory functors, and the presentation theorem.
The definition module is a public import because the existing public scalar-extension
abbreviations now refer to its constructions. No target signature changes.

Validation: the three delivery modules compiled; after the second-reading elaboration repairs, the item compiled cleanly in 54.5 seconds
in its latest local run. Both unchanged direct users, `Sheaf.Paper.CondensedCoefficientComparisons`
and `Sheaf.Paper.CondensedFlatCoefficientCalculus`, also compiled against the extracted
constructions. The two extension functor definitions are reducible so their existing
raw-functor shift instances remain visible. Their temporary source copies were removed
from the sandbox after this check; no adaptation of either module is delivered.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.constructibleCocone_homSurj`.
There are no remaining sorries in the item module. All the private factorization and
comparison helpers and all nine definitions of the comparison module are fully proved.

One new hole:
`AlgebraicGeometry.ProEtale.exists_condensed_coefficient_complex_presentation`, in
`Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation`, node
`lem-weil-pbc-condensed-coefficient-complex-presentation`.
This is a decomposition: one original hole closed and one strictly smaller coefficient
algebra hole added, for net zero holes in this delivery. The new statement has no
constructibility or bounded-above assumption and does not assert Hom descent.

The remaining theorem needs the explicit diagram of termwise finite tensor extensions
restricted to E, its degreewise colimit and common lower bound, and the canonical
adjunction/tensor comparison equation. Its docstring and node give
the construction and proof. In particular the last equation must follow from the actual
unit and multiplication maps, not an arbitrary Hom-set bijection. I tested the zero complex
and empty-scheme cases, and checked that arbitrary bounded-below targets are sufficient.
The attempts also isolated a generic linear map between restricted regular modules in the
scratchpad; this unused experiment is not delivered as a library dependency.

## No longer needed

No existing direct import was removed: each supports the preserved object-descent,
scalar-preservation or injectivity proofs. The new proof does not need these former direct
proof dependencies of the parent:

- `lem-weil-pbc-profinite-point-pullback`: no direct use in the parent proof; it remains
  a dependency of the condensed coefficient-category definition.
- `lem-weil-pbc-truncation-triangle`: use the already proved `DerivedCategory.prop_of_bounded`.
- `lem-weil-pbc-hom-out-of-triangle-exact`: use Mathlib `Triangle.yoneda_exact₂` directly.
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`: only representative existence is used.
- `lem-weil-pbc-five-lemma`: monic-leg triangle factorization replaces the five-lemma argument.
- `lem-weil-pbc-filtered-colimit-sets-elementwise`: use proved Mathlib
  `Concrete.colimit_exists_rep` for the Hom-group colimit.
- `lem-weil-pbc-condensed-flat-coefficient-calculus`: the parent uses the existing exactness
  instances in Compatibility and the proved generic derived adjunction instead. The new
  coefficient presentation uses those source constructions too.

These are removed parent edges, not claims that other targets no longer use these nodes.
In particular previously retained dependencies may reach some of them independently.
The corresponding Sheaf proof modules are not imported by this delivery. No blueprint
unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The five-lemma comparison is sufficient but unnecessary for this parent: faithful scalar
extension already handles injectivity, and monic coefficient legs let factorization itself
form a triangulated property. The bounded-source proof is written out, rather than split
off under another name.

The lifted constructible tensor comparison has components defined through a fully faithful
functor's chosen preimages. Their underlying arrows require `map_preimage`; they should not
be assumed definitionally equal to the ambient comparison. The new component lemmas supply
this missing API. No mathematical statement was found false or weakened.

The final Lean declaration assembles the three clauses of `CategoryCocone.IsFilteredTwoColimit`.
The old DAG's separate pair-category construction paragraph was more than this source code
actually uses; the source module explains the ordinary-category interpretation.

The first dry run also identified two metadata mistakes, now corrected: the comparison-node
signature must omit the declaration modifier `noncomputable`, and the new nodes must record
all three search kinds. LeanSearch was attempted and returned service unavailable; LeanFinder,
Loogle and local grep were also run. The dry-run wrapper explicitly waives the absent independent
second-reading section for this first-worker pass, so that section remains for the second reader.

## New nodes

`def-weil-pbc-finite-derived-tensor-comparison` records the nine completely defined, canonical
coefficient constructions in `Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison`.
The original comparison body is preserved. Change record:
`coord/changes/B2-finite-derived-tensor-comparison.md`.

`lem-weil-pbc-condensed-coefficient-complex-presentation` records the remaining coefficient
algebra theorem. Its hypotheses, explicit comparison equation, source, edge cases and full
proof in words are in its module and node. The parent's proof and proof-dependency list now
follow the actual monic-leg argument.

## Second reading by B2

1. **Existing interface: pass.** Read the complete parent diff and the local master source
   `~/weil-newtargets-master/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean`,
   especially the bounded-below Hom argument in its module docstring. Every existing theorem
   signature is unchanged. The sole declaration-modifier change is the recorded `def` to `abbrev`
   for `derivedExtendScalarsCompIso`; the two extension abbreviations and comparison retain
   their original types and data. Compared the extracted tensor-comparison body verbatim with
   the original. The change record covers the extraction; rerunning downstream searches for
   all three old names found exactly the three users in its table. No other existing module
   is edited, and no target statement changes.

2. **Proof and trust: pass.** Read the factorization and adjunction proofs, including the
   inverse-rotated triangle, cancellation of monic legs, common-index addition, and both
   `map_preimage` component formulas. The parent has no direct hole; the only delivery hole
   is the named presentation theorem. There is no forbidden declaration, hollow definition,
   or data selected from that theorem in a definition: its witnesses are eliminated inside
   the Hom-surjectivity proof. Scratch reflexivity checks compare the three extracted
   constructions with the original raw functors and tensor-comparison term. The nine
   extracted definitions have only `propext`, `Classical.choice`, and `Quot.sound` as axioms;
   the presentation and parent may also depend on `sorryAx` through the listed open inputs.
   The final local compilation and delivery axiom probe provide the mechanical checks.

3. **New statements: pass, one clarification repaired.** Matched the presentation node to
   every Lean hypothesis and clause: arbitrary scheme, prime, two finite fields, bounded-below
   target, small filtered final diagram, both inclusions, termwise uniform bound, colimit,
   both families of isomorphisms, and the equation for every derived source and every map.
   Arbitrary sources in that equation are needed to prove monicity in the whole derived
   category. The zero target gives a constant zero diagram and the empty scheme gives zero
   module categories; neither needs an omitted nonzero hypothesis. For a complex in one
   degree, the equation is the ordinary tensor-unit and multiplication identity. Exact scalar
   extension preserves a common lower bound, so no upper bound or constructibility is needed.
   The statement is strictly the coefficient-algebra construction, with the bounded-source
   continuity and triangle argument proved in the parent. It cannot be closed in a short
   proof without constructing its coefficient diagram and localization compatibility.
   Independently searched LeanFinder for scalar extension along a filtered union of fields,
   Loogle for complex functor colimit preservation, and Mathlib/local sources for coefficient
   and tensor colimits. Found general colimit infrastructure and the already proved
   `condensedCoefficientTensorColimit`, which only preserves a supplied module cocone and
   does not construct this complex presentation or its adjunction equation. It is downstream
   of the parent, so importing it would also create a cycle. No duplicate presentation was
   found. Rewrote both new node statements in TeX and explicitly defined the finite-subfield-
   valued coefficient sheaf, preventing confusion with the full continuous-function sheaf.

4. **Top-down reduction and pruning: pass, one omission repaired.** The proof uses the existing
   single-sheaf continuity input, Mathlib representative existence and Yoneda exactness, then
   the proved bounded-object devissage. It writes out the triangle reduction rather than
   relocating Hom descent. Each added import supplies the functors, continuity, representatives,
   small enlargement, finality, or presentation used in the code; proof-only imports are plain
   imports. The extracted construction is public because the old public scalar names use it.
   Compared the old and new dependency sets: seven direct parent edges disappear. Added the
   missing `lem-weil-pbc-profinite-point-pullback` entry to `No longer needed`; the other six
   were already listed. These are edge removals, with no claimed whole-module pruning. Read
   `dag/units/sk-thm-properbasechange.json`: none of its realized statement or step nodes is
   removed or bypassed, and its record is unchanged.

5. **DAG and report: pass.** The existing parent node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its steps match the coefficient presentation, faithful cancellation,
   single-sheaf representatives, monic-leg triangle argument, bounded devissage, component
   calculation, and the preserved object-descent/injectivity proofs. The helper definition
   node names all nine implemented declarations; the presentation node's recorded Lean
   statement matches its theorem. Both new nodes carry their source, proof plan, searches,
   creation record, blueprint ancestry, chapter/unit, and Lean record. The report explicitly
   records one hole closed and one added: this is a decomposition with net zero holes.

Second-reading changes: cached the complex-colimit witness in the private reductions and the
exact-derived comparison in the proof instances to repair slow elaboration; clarified the coefficient sheaf and TeX in the two new node statements;
completed the pruning report with the seventh removed dependency; added this independent reading.
No existing mathematical statement, target, or coefficient construction was changed.
