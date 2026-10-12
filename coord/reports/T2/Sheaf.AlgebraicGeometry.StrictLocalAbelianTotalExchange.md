## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_abelian_total_exchange`
with a complete Lean composition of two comparisons. Its signature, universes,
hypotheses, conclusion, and existing docstring are unchanged. Replaced six old proof-only imports with two new proof-only
imports and added two new statement modules, each with one named public theorem whose
entire proof is sorry. Updated the item's DAG proof to match the Lean composition.
The new modules publicly import the upstream APIs used by their signatures and
privately import the stated dependencies of their proof plans.

The intermediate groups are the homology of bounded below derived global sections.
`StrictLocalDerivedGlobalExchange` handles only the geometric stalk computation,
for arbitrary bounded below K and integer degrees. `AbelianDerivedGlobalExtPullback`
handles only the Ext comparison and its pullback compatibility, for arbitrary scheme
morphisms, with no strict-local base or cartesian-square hypothesis. Neither new
statement alone is the original theorem. The original proof composes c1 with b1 and
c2 with b2, rewrites using the geometric equation, and then applies the Ext equation.

All three modules compile locally in import order without errors or warnings.
The delivery dry run supplies the axiom probe and server checks.

The source pages read were Stacks [03QO](https://stacks.math.columbia.edu/tag/03QO),
[095T](https://stacks.math.columbia.edu/tag/095T),
[01F8](https://stacks.math.columbia.edu/tag/01F8), and
[08J6](https://stacks.math.columbia.edu/tag/08J6). The local literature files named by
older nodes are absent on this machine, so the corresponding public source pages
were read instead. No project source outside the sandbox was edited manually.

## Proved and sorry left

The original declaration
`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_abelian_total_exchange`
(node `lem-weil-pbc-strict-local-abelian-total-exchange`) has a complete proof from
the two new declarations. There is no sorry in the item's module. This is a reduction,
not a claim that the transitive proof is now free of sorry.

Exactly two new sorries remain:

- `AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_derivedGlobal_exchange`,
  node `lem-weil-pbc-strict-local-derived-global-exchange`, in
  `Sheaf.AlgebraicGeometry.StrictLocalDerivedGlobalExchange`.
- `AlgebraicGeometry.Etale.exists_addEquiv_derivedGlobal_ext_pullback`,
  node `lem-weil-pbc-abelian-derived-global-ext-pullback`, in
  `Sheaf.AlgebraicGeometry.AbelianDerivedGlobalExtPullback`.

Both have a source, complete resolution-based proof in their docstrings, and
matching DAG nodes. No definitions, instances, axioms, or private sorries were added.

The edge cases checked mathematically were q=0 (the germ and constant-sheaf
adjunction give the section map), identity g' (the unit/Leray map is the identity
under the comparisons), zero G/K and empty X (the groups are zero), and negative
integer q in the geometric lemma (the comparison is valid on arbitrary complexes;
no nonnegative-degree vanishing is asserted there). No properness, qcqs, or torsion
assumption is used. The original natural-number q is cast to the same integer in
both comparisons, which Lean verifies definitionally.

## No longer needed

Removed the following direct proof-only imports from the item's current repository
version: `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`,
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`,
`Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`,
`Sheaf.Paper.InverseImageStalkGerm`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
These declarations are now available through the two split-off modules: the geometric
module imports the first five as proof prerequisites, and the Ext comparison module
imports `EtaleSheafHExtDerivedComparison`, which publicly imports `LowerShriek`.
They are not globally pruned modules.

Every old immediate proof dependency is no longer an immediate dependency of the
item's composition proof: `def-weil-pbc-cohomology-pullback`,
`def-weil-pbc-etale-cohomology`, `lem-weil-pbc-cohomology-pullback-derived-unit`,
`lem-weil-pbc-derived-exchange-termwise`, `lem-weil-pbc-inverse-image-stalk-germ`,
`lem-weil-pbc-strictly-henselian-sections-stalk`,
`prop-weil-pbc-cohomology-resolution-independent`, and
`prop-weil-pbc-geometric-stalks-exact`. They remain prerequisites of the split-off
nodes or of the unchanged statement; none is claimed globally unnecessary.
No unit statement or realized step is bypassed. Global pruning: none.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the original statement. The current module
imports only statement prerequisites; the original node's proof steps are not
already a directly applicable Lean proof of the derived stalk/Ext comparison.
The existing theorem
`Scheme.nonempty_sheafH_extDerivedIso` is proved and provides natural object
comparisons, but its statement does not assert compatibility with scheme pullback.
Its witnesses cannot be chosen arbitrarily and assumed to commute with pullback:
that is precisely the additional content of the new Ext comparison. Likewise,
`derivedCohomologyPullback_eq_derivedUnit` is proved, but compares two derived
recipes rather than comparing either recipe with the Ext map `cohomologyMap`.
Neither existing result has been restated in its original form.

The existing strict-local germ and inverse-image germ declarations use
algebraically closed geometric points, whereas the item uses separably closed
residue fields. The geometric obligation explicitly includes that passage. One
can perform the same pointed strict-local germ argument for a separably closed
point, or first extend to an algebraic closure (a purely inseparable extension)
and compare the points. The new lemma does not add an algebraic-closedness
hypothesis to the original item.

Searches ran through msearch: LeanFinder on strict-local higher direct image stalks,
Loogle on `CategoryTheory.Sheaf.H`, grep on homology/Ext/cohomology, and LeanSearch
on both new obligations. LeanSearch returned Internal Server Error and is recorded
as unavailable, without a no-match verdict. Local rg searches and signature reading
found the Ext/derived natural isomorphism, the derived-unit comparison, and the
qcqs strict-henselization global-homology statement; none gives the missing map
comparison for this item. Blueprint searches for derived global sections, constant
integers, and strict-local statements found no duplicate of the two obligations.

## New nodes

`lem-weil-pbc-strict-local-derived-global-exchange` isolates the original node's
strict-local germ, exact-stalk, injective-resolution, and termwise-exchange work,
ending at derived global cohomology and its derived-unit pullback. Its module is
`lean/Sheaf/AlgebraicGeometry/StrictLocalDerivedGlobalExchange.lean`.

`lem-weil-pbc-abelian-derived-global-ext-pullback` isolates the constant-integer
sheaf/Ext comparison and compatibility with the exact-inverse-image definition of
`cohomologyMap`. Its module is
`lean/Sheaf/AlgebraicGeometry/AbelianDerivedGlobalExtPullback.lean`.

Both belong to sec-proper-base-change and sk-thm-p1, with the same blueprint
ancestor as the strict-local exchange route. No change record is required: no
existing public interface, definition, or statement changed.

## Second reading by T2

1. Compared the delivered item with the repository using `diff` and the declaration
   parser. Its existing theorem signature and docstring are byte-for-byte unchanged;
   no definitions or instances changed, and no change record is required. The only
   differences are proof-only imports and the proof. The other two modules are new.
   Verdict: pass.
2. Compiled all three modules locally in import order after repair, without errors
   or warnings. Scratch copies with `#print axioms` for each public theorem report
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Exactly the two
   listed new named theorems have `sorry`; there is no hollow definition or forbidden
   declaration. The target module is a reduction, not a transitive sorry-free proof.
   Verdict: pass.
3. Read both split statements, their docstring arguments, and their nodes. Checked
   zero coefficients, empty total space, identity pullback, degree zero, and negative
   degrees for arbitrary bounded-below complexes. The geometric comparison uses
   exact closed-point sections, not a proper-base-change isomorphism; it therefore
   needs no properness or torsion. Passing to algebraic closures of separably closed
   fields uses invariance of etale points under purely inseparable extension. The
   Ext comparison needs resolution choices that respect pullback; arbitrary witnesses
   of the existing natural Ext comparison do not suffice. These are separate parts
   of the argument with an actual composition proof, not a renamed target.
   Read [03QO](https://stacks.math.columbia.edu/tag/03QO),
   [095T](https://stacks.math.columbia.edu/tag/095T),
   [01F8](https://stacks.math.columbia.edu/tag/01F8), and
   [08J6](https://stacks.math.columbia.edu/tag/08J6). Their application to these
   complexes is the resolution argument written in the docstrings. Repeated searches
   with different words: LeanFinder on constant-integer Ext naturality, Loogle on
   `CategoryTheory.Sheaf.H, CategoryTheory.Iso`, grep on `ΓHomEquiv` and
   `upperStarConstantSheafIso`, and local rg of comparison/pullback/exchange modules.
   Found the constant-sheaf adjunction naturality and Ext composition lemmas, but no
   exact match or immediately usable proof of either split statement. No split
   statement could be closed by a short application of the found declarations.
   Verdict: pass, with the two explicitly open obligations.
4. Read the original eight-dependency plan and its stated Lean prerequisites,
   including the proved derived-unit, termwise-exchange, germ, and Ext comparison
   declarations. The composition uses the shortest identified interface through
   derived-global homology. Checked `dag/units/sk-thm-p1.json` and its `realized`
   fields: strict-local calculation and closed-fibre comparison remain on the route.
   Corrected the removed-import inventory above; no node is globally pruned.
   Verdict: pass after repair.
5. Checked each node's `proof_deps` is exactly the union of the step `uses` and
   checked the new nodes' source, search records, created record, blueprint, unit,
   chapter, and Lean signatures. The item's steps describe the Lean composition
   exactly. The two new proof plans describe the remaining named obligations.
   Verdict: pass.

Changed during second reading: replaced the proof-only public import of
`CohomologyPullbackDerivedUnit` in each new module with public upstream signature
APIs and a plain proof import; added plain imports for the proof dependencies with
project declarations, preserving their reachability; corrected `What changed` and
`No longer needed` against the newer repository version. No theorem statement,
proof body, node statement, or unit record was changed.
