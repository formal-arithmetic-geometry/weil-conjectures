## What changed

Repair of the landing refusal: removed the duplicate private declaration
`CategoryTheory.pullback_kernel` from `FilteredComplexNormalizedHomology`. Added
`import all Sheaf.CategoryTheory.FilteredComplexPageHomology` as a proof-only import
to reuse its existing private theorem directly. No existing module, signature or
visibility changed. Updated the normalized-homology node to record this dependency.


Replaced the hole in `CategoryTheory.filteredQuotient_canonical_functor` by a complete
Lean assembly of the spectral-sequence functor. Its statement, universes, binders and
visibility are unchanged. The page objects are the constructed concrete cokernels;
the page differentials are exactly the supplied `D`.

Added four modules: `FilteredQuotientPageMaps`, `FilteredComplexNormalizedHomology`,
`FilteredQuotientSuccessorCycleMaps`, and `FilteredQuotientHomologyNaturality` in
`Sheaf.CategoryTheory`. The first and third contain the two remaining subarguments.
The second proves the unique normalized homology comparison from the existing
successor-cycle cover and boundary image formulas. The fourth proves homology
naturality by cancelling the epic successor-cycle cover followed by the homology
projection, using the two squares of the successor-cycle restriction.

The proof selects page maps from a uniqueness theorem and homology comparisons
from the proved unique normalization theorem. Both statements determine the data
up to equality. No arbitrary homology-isomorphism witness is used. No definition
contains a hole. The arbitrary restriction `k` in the successor-cycle lemma is
eliminated inside a proof of an equality; it does not define any library object.

All five delivered modules compiled in import order without warnings using
`lcompile.py --all`. The existing theorem needs a declaration-scoped unused-variable
linter option because several names in its unchanged statement are not used in its
types. Explicit binder types in the new naturality statement avoid an elaboration
heartbeat timeout; no limits are raised.

## Proved and sorry left

Closed the original hole `CategoryTheory.filteredQuotient_canonical_functor`
(node `lem-sp-filtered-quotient-canonical-functor`). It is a decomposition from two
strictly smaller remaining theorems, not a sorry-free proof of the entire argument.

The delivery also proves:
- `CategoryTheory.filteredComplex_cycles_successor_le`;
- `CategoryTheory.filteredComplex_normalized_homology`
  (node `lem-sp-filtered-complex-normalized-homology`);
- `CategoryTheory.filteredQuotient_homology_naturality`
  (node `lem-sp-filtered-quotient-homology-naturality`).

The only added holes are:
- `CategoryTheory.filteredQuotient_page_maps`
  (node `lem-sp-filtered-quotient-page-maps`);
- `CategoryTheory.filteredQuotient_successor_cycle_maps`
  (node `lem-sp-filtered-quotient-successor-cycle-maps`).

No hole remains in the item's own module. One original hole closed, two added:
the local net is minus one, honestly a decomposition. Existing successor-cycle and
boundary-image dependencies remain in the import closure.

## No longer needed

The duplicated local `pullback_kernel` proof is removed; the existing theorem in
`FilteredComplexPageHomology` is now used. This adds that module to the proof
closure; no module is claimed pruned by the repair.


Removed the item's direct proof imports of
`Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover` and
`Sheaf.CategoryTheory.FilteredComplexSuccessorBoundariesImage`. They are still used
through the proved normalized comparison; the cycle cover is also used by the
proved naturality argument. They are not pruned from the closure. No node or module
is claimed pruned. The original direct proof dependencies `def-sp-filtration` and
`def-sp-filtered-complex-subquotients` now occur inside the page-map and normalized
comparison subarguments, so their direct DAG edges are removed but both remain
in the closure. The spectral-sequence and page-differential edges remain.
The second reading also removes the unused public import
`Mathlib.Algebra.Homology.SpectralSequence.Basic` from the new page-map module;
this module does not state or construct a spectral sequence.
No dependency of a blueprint unit's realized route is bypassed:
`sk-prop-av-pqf-finite` has no realized nodes in its unit record.

The unrelated positive-page existence theorem and its arbitrary unnormalized
homology-isomorphism choice are not used. Neither the exact-couple realization nor
graded-homology/first-page connecting-map comparisons are needed by this statement.
They were not original proof dependencies and are not counted as pruned.

## Where the brief, the DAG or earlier work was wrong

The previous delivery and reading missed a duplicate private helper. The landing
checker correctly refused it. An ordinary import cannot access that helper; Lean
module-system `import all` provides access without changing the source module.
The repair uses the original theorem directly rather than renaming or restating it.


The stated three-step plan is mathematically usable. The supplied interfaces do not
yet provide canonical page maps or the successor-cycle restriction square; those
are now separate named statements with full proofs in words, rather than hidden
inside the functor hole. The existing `FilteredComplexPageHomology` proof supplies
the cokernel argument; its bare `Nonempty` conclusion omits the normalization, so
this delivery constructs the normalized cokernel comparison with the equation and
uniqueness exposed, reusing that module's private kernel-pullback theorem via
`import all` rather than repeating the helper proof.
No existing definition or statement is changed and no forced adaptation is needed.

Edge cases checked for the new statements: zero complexes and zero pages, zero
filtered maps, identity and composite maps, page 1, unrelated differential
bidegrees, and arbitrary finite filtration endpoints. They use only epimorphic
local lifts and monomorphic cancellation, never projectivity, countable sums or
stabilization. The successor-cycle compatibility theorem quantifies over arbitrary
covers satisfying the representative equation; these are equal after cancellation
of the page cycle inclusion. In the uniqueness assertion for page maps, canonical
restriction squares exist from filtered-map preservation, so the universal property
is not vacuous. Finiteness is carried in the domain but not used in these local
arguments.

Read Stacks Tag 012K, the explicit cycle, boundary and differential formulas, and
Lemmas 12.24.2 and 12.24.4 at https://stacks.math.columbia.edu/tag/012K.
LeanFinder, Loogle and Mathlib grep searches ran and are recorded in `searches.jsonl`;
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable.
Blueprint searches for filtered quotient page maps, filtered homology naturality
and normalized homology returned no matches. The new nodes retain the nearest
blueprint source recorded in the item's existing provenance.

## New nodes

`lem-sp-filtered-quotient-page-maps` records the uniquely determined chain map family
on concrete pages and its universal representative squares and category laws. Its
remaining proof contains no homology comparison or spectral-sequence construction.

`lem-sp-filtered-complex-normalized-homology` records the normalized successor
homology comparison. It is proved in the new module, including uniqueness and the
successor-cycle containment helper; no sorry is introduced by this node.

`lem-sp-filtered-quotient-successor-cycle-maps` records the cycle restriction and
its two projection squares, before taking homology. It is the second remaining
hole, not a reformulation of spectral-sequence functoriality.

`lem-sp-filtered-quotient-homology-naturality` records the homology cancellation
argument and is proved from the previous cycle squares and the existing epic cover.
The original node's proof, proof dependencies and proof origin follow the new Lean
assembly. No change record is needed because no existing interface changes.


## Earlier second reading (a previous round; superseded)

1. **Existing interface unchanged — pass.** Read the full diff of each delivered
   module against the repository: four are new; the canonical-functor module is
   the only existing module. Its theorem signature from `theorem` through the
   conclusion is byte-for-byte identical. Its docstring and visibility are also
   unchanged. Changes are three proof imports, a declaration-scoped unused-binder
   linter option, and the proof body. No target, existing definition, or other
   group's module is changed; no change record is required.

2. **Kernel proof and data choice — pass, conditional on the recorded holes.**
   Compiled all five modules in dependency order with `lcompile.py --all`, before
   and after the import repair, with no warnings. A scratch module printed axioms
   for both property definitions and all six public theorems. The properties and
   successor-cycle containment use only `propext`, `Classical.choice`, `Quot.sound`;
   the other theorems also use `sorryAx`, from the recorded new or imported holes.
   No forbidden declaration or hollow definition occurs. Exactly the two named
   new theorems listed above have `sorry` as their entire proof. The page-map family
   comes from an existence-and-uniqueness statement; the homology comparisons have
   uniqueness proved by cancelling the epic successor-cycle cover followed by the
   homology projection. The locally chosen successor restriction is used only in
   an equality proof. Thus no arbitrary unproved witness defines library data.

3. **New statements and searches — pass.** Read all four new nodes and their Lean
   statements, including the entire quantified four-square property. A filtered
   chain map preserves the intersections, inverse images, and images defining
   cycles and boundaries, so the square property has canonical witnesses and is
   not vacuous. Monic step and cycle inclusions and epic quotient projections
   determine those witnesses and the page map. The successor-cycle assertion
   requires only the two projection squares, with no homology comparison or
   spectral-sequence functor in its conclusion; arbitrary covers with its stated
   equation coincide by monic cancellation. Neither remaining hole restates the
   item. Checked zero objects, zero filtered maps, identity and composite maps,
   r=1, and zero differentials: the normalized comparison is the quotient
   comparison, and all asserted squares reduce to the expected projections.
   The proofs require no projectivity or countable sums. Independently searched
   LeanFinder for induced subquotient morphisms, Loogle for `cyclesMap`, Mathlib
   grep for image-subobject and cokernel maps, and the repository for cycle,
   boundary and normalized-homology declarations. Found `cokernel.map`,
   `imageSubobjectMap`, `cyclesMap_i`, and `homologyπ_naturality`, but no existing
   theorem giving either remaining filtered-complex assertion. The existing
   `FilteredObject.restriction` and `exists_gradedMap` in
   `FiniteFiltrationInduction` provide the first elementary construction, but not
   the cycle/boundary preservation or chain-map assertion. The existing
   `filteredComplex_page_homology` proves only `Nonempty` of an isomorphism;
   it cannot supply the normalization required here. The new proof uses its
   short cokernel argument and proves normalization and uniqueness explicitly.
   Rechecked the explicit formulas and Lemmas 12.24.2 and 12.24.4 in Stacks 012K.

4. **Top-down route and pruning — pass.** The item assembles actual page maps,
   normalized homology isomorphisms, and their naturality. It then proves the
   functor laws by page extensionality and takes identity quotient comparisons.
   Both imported successor formulas are used in the normalized proof; the cycle
   cover is also used for naturality. All original proof dependencies therefore
   remain in the closure, although four direct DAG edges have moved into the
   subarguments as recorded under `No longer needed`. No closure pruning or net
   progress is claimed: one old hole closed and two new holes added is a
   decomposition, with local net minus one. Inspected
   `dag/units/sk-prop-av-pqf-finite.json`: its statement and sole step have empty
   `realized` lists, and no unit route is bypassed.

5. **DAG correspondence — pass.** Matched the parent node's three revised steps
   to the actual page-map choice, normalized comparison/naturality, and identity
   comparison proof. Matched each new node's statement, source, Lean record,
   creation/provenance, and proof-dependency union to its module. The normalized
   and naturality nodes describe completed reductions; the page-map and
   successor-cycle nodes describe the two remaining strict subarguments. Added
   independent search records to the new nodes. Existing node statement and
   statement-dependency fields remain unchanged.

**Repairs:** removed the unused public spectral-sequence import from
`FilteredQuotientPageMaps`, completed the list of displaced direct DAG edges in
`No longer needed`, added the independent search records, and wrote this review.
No mathematical proof or statement needed rewriting. That earlier reading did not find the now-landed
`filteredQuotient_map_restrictions`; the current reading below records its potential use.


## Second reading by Y3

1. **Interface preservation: pass.** Diffed all five modules against the repository.
   Four modules are new; only `FilteredQuotientCanonicalFunctor` has a baseline.
   Compared its signature from the theorem keyword to `:= by` byte for byte:
   identical, including universes, binders, all four-square hypotheses and both
   conclusions. Its docstring and public visibility are unchanged. Only proof
   imports, a scoped unused-variable linter option and the proof body differ.
   The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   No target, existing definition, or other existing module is altered.

2. **Proofs and data: pass relative to the listed holes.** Independently ran
   `lcompile.py --all`: all five modules compiled without warnings. Read each
   proof, and printed axioms for the two property definitions and all six public
   theorems in `scratchpad/lean/ReviewAxioms.lean`. The properties and containment
   theorem use only `propext`, `Classical.choice`, `Quot.sound`; the other
   theorems additionally use `sorryAx`. Exactly the two recorded split theorems
   retain whole-body `sorry`; there is no forbidden axiom, unsafe code, opaque
   declaration, external implementation or hollow definition. The page maps are
   selected from existence-and-uniqueness. The normalized comparison is obtained
   from two cokernel universal properties, and its uniqueness is proved by
   cancelling the epic cover followed by the homology projection. The local
   successor restriction is eliminated only in a proof of an equality. These
   choices satisfy the project's determined-object rule.

3. **Split statements and shortest available route: pass, with a missed search
   result recorded.** Read the new Lean signatures and all four node statements.
   The page-map theorem asserts chain maps, category laws and representative
   squares, with no successor comparison; the successor-cycle theorem asserts
   just two squares before homology. Neither restates the spectral-sequence
   functor. Read Stacks 012K's cycle and boundary formulas and Lemmas 12.24.2
   and 12.24.4. For zero complexes and zero filtered maps the squares reduce to
   zero maps; with zero differential the cycle restrictions are graded maps and
   boundaries vanish. At r=1 the source boundary filtration is p and at r+1
   it is p-1; the successor differential condition is F^(p+r+1). Identity and
   composition follow from monic and epic cancellation. Arbitrary fU and fV
   satisfying their inclusion equations are uniquely determined by monicity,
   so the successor assertion needs no extra epimorphism assumption. Canonical
   step, graded, cycle and quotient maps supply instances of the four squares,
   so the page-map uniqueness property is not vacuous.

   Independently searched LeanFinder for functorial image subobjects, Loogle
   for `Subobject.map`, Mathlib grep for `imageSubobjectMap`, and both library
   roots for filtered cycle maps. Mathlib provides image maps and cancellation,
   rather than either full filtered-complex assertion. The repository now has
   `CategoryTheory.filteredQuotient_map_restrictions` in
   `FilteredQuotientMapRestrictions`, which supplies the cycle and quotient
   restrictions at a specified page. Together with
   `FilteredObject.exists_gradedMap` in `FiniteFiltrationInduction`, it should
   reduce the successor hole to two applications and monic cancellation.
   Tried this reduction in the sandbox, but `lcompile.py` reports that the
   restriction module's object file does not exist in the last green library.
   Did not copy or redeclare it: restored the original compiling split theorem,
   following roles/worker.md section 2.2. This is a useful pending reduction,
   not a proved hole or a reason to discard the valid current delivery.

4. **Top-down construction and pruning: pass.** The parent chooses page maps,
   builds spectral-sequence objects from the normalized successor comparisons,
   uses proved homology naturality for the morphism compatibility, then proves
   functor laws by page extensionality. Identity quotient comparisons prove both
   requested equations. In the normalized proof the successor-cycle cover and
   successor-boundary image theorem are both used. The private pullback-kernel
   theorem is reused through `import all`, not duplicated. In the naturality
   proof precomposition with fU followed by the homology projection is epic;
   each side reduces to k followed by the successor projection. The original
   direct filtration and subquotient edges move into the subarguments, and the
   two successor imports remain in the closure. The report lists these changes
   without claiming closure pruning. Inspected the unit record
   `sk-prop-av-pqf-finite`: its realized lists are empty. No realized route is
   bypassed. One baseline hole closed and two new holes added remains a
   decomposition with local net minus one; no sorry-free result is claimed.

5. **DAG agreement: pass.** Matched the parent's three steps to the Lean assembly
   and each new node to its actual statement and proof or remaining docstring
   argument. Checked each `proof_deps` against the union of its step `uses`;
   all agree. The normalized node records its proof-only dependency on
   `FilteredComplexPageHomology` for the existing private helper. The new Lean
   records reproduce their theorem signatures verbatim and have source,
   creation, chapter, unit, blueprint provenance and search fields. The existing
   statement and statement-dependency fields are unchanged. The new axioms
   checks confirm the advertised remaining proof dependencies.

**Changes in this reading:** added independent search records to the four new
nodes and this current review; corrected the earlier report's assertion that no
short reduction was available, recording the existing restriction theorem and
its missing compiled artifact. Attempted successor-hole closure was restored
because it cannot yet be checked against the last green library. No delivered
Lean proof, signature, definition or import needed changing in this round.
