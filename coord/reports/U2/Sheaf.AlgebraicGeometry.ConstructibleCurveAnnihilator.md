## What changed

Replaced `AlgebraicGeometry.CurveCoefficientPair.exists_annihilator_of_constructible`'s
sorry with a complete Lean reduction. The curve is Noetherian by finite type over a
field. A new uniform finite stalk-cardinality bound supplies N; N factorial annihilates
every stalk by Mathlib's Lagrange theorem and factorial divisibility. Additivity of the
stalk functor and the source library's stalk extensionality then prove the original
morphism equation. Its signature, universes and hypotheses are unchanged.

Added `Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound`, containing only the
remaining geometric bound. Updated the original node's proof route and dependencies.
No definition, target statement, unit statement or unit proof route changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.CurveCoefficientPair.exists_annihilator_of_constructible`
(node `lem-weil-pbc-curve-constructible-annihilator`). The entire factorial arithmetic,
finite-group annihilation, stalk map computation, and passage back to sheaf morphisms
compile without a sorry in the item module.

Added one hole in
`AlgebraicGeometry.Scheme.exists_stalk_cardinality_bound_of_constructible`
(node `lem-weil-pbc-constructible-stalk-cardinality-bound`), in its separate module.
This is a decomposition: one upper hole closed, one strictly geometric lower hole
added, net holes zero. It is not an axiom-free completion of the original theorem.
The new result applies to any Noetherian scheme, with no torsion or curve hypothesis,
and gives finite cardinality data rather than an annihilation equation. The actual
finite-group and conservative-stalk argument is written and checked in the item.

Edge checks: the empty scheme admits bound zero and the final integer is 0! = 1;
the zero sheaf has singleton stalks; disconnected curves are allowed. An abelian stalk
is nonempty, so finite stalk cardinality is positive even for the zero group. No
positive-bound assumption was introduced. All Lean files compile with lcompile.py.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`:
node `lem-weil-pbc-constant-sheaf-geometric-stalk` proves an abelian constant-section
map, whereas the remaining geometry concerns constant underlying sets. The new bound
uses the general source-library constant-sheaf stalk isomorphism, valid for sets.
This abelian constant-section theorem is no longer a dependency of this argument.

Removed the proof import `Sheaf.Paper.InverseImageStalkGerm` from both delivered
modules. Node `lem-weil-pbc-inverse-image-stalk-germ` is no longer needed by this
argument: it concerns abelian inverse images. The new bound instead imports the
proved set-valued `Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm` and its node
`lem-weil-pbc-sets-etale-inverse-image-stalk-germ`. This is argument-level pruning;
it does not claim the old module is globally unreachable.

Removed `prop-weil-pbc-geometric-stalks-exact` from the original node's direct proof
dependencies. No image is formed; the proved
`Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint` gives equality directly.
Its existing conservative-point module remains imported. This does not assert that
stalk exactness is globally unreachable or absent from the extensionality tool's
transitive imports. No other original planned dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The stated constant-sheaf geometric-stalk theorem is for abelian groups, while
constructibility here is defined via finite locally constant underlying sets. A
set-valued constant stalk comparison and forgetting/stalk comparison are needed
in the remaining geometry. The source library supplies the former generically.
The planned image/exactness/conservativity detour is unnecessary for morphism equality.

Also searched the existing `lem-weil-pbc-constructible-abelian-bounded-exponent`
node. It has no Lean declaration and states the whole annihilation result, so
importing it is impossible and restating it would not be a reduction. The existing
finite constant local model theorem uses separably closed finite stalks, rather
than this definition's algebraically closed finite stalks; it is supporting
material, not a direct proof of the uniform bound.

The local copy of the cited Stacks TeX file is absent. Read Tags 03RW and 095E
at their public Stacks URLs instead. LeanSearch returned an internal server error;
LeanFinder, Loogle, Mathlib grep and project/blueprint searches were completed.
No change record is needed, since no existing statement or definition changed.

## New nodes

`lem-weil-pbc-constructible-stalk-cardinality-bound` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constructible-stalk-cardinality-bound.json`
records the uniform geometric cardinality bound in
`Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound`. Its docstring and DAG
steps give the full finite stratification, finite trivializing subcover,
constant-value and inverse-image stalk argument, including forgetting to sets.
Three kinds of Mathlib search are recorded (LeanSearch unavailable, with no
absence verdict), and the original chapter and unit are preserved.

## Second reading by U2

1. **Unchanged interfaces: PASS.** Diffed every delivered module against this machine's
   read-only repository. The item has exactly its original theorem signature, universes,
   hypotheses and conclusion, byte for byte. The bound module is new. There are no new
   definitions, changed existing statements, changed target statements or change records.
2. **Proof and trust: PASS as a decomposition.** Compiled both modules in import order
   with lcompile.py, without errors or warnings. The only delivered sorry is the named
   `AlgebraicGeometry.Scheme.exists_stalk_cardinality_bound_of_constructible`. Scratch
   `#print axioms` checks show the item uses only propext, Classical.choice, Quot.sound,
   and sorryAx; the new theorem has the same permitted axiom list plus sorryAx. No forbidden declaration, hollow
   definition or arbitrary object chosen by an unproved existence theorem is introduced.
   The existential bound is eliminated inside a proposition-valued proof, not a definition.
3. **Split-off statement: PASS.** Read the definition of finite constructible stratification,
   its immersion domains, the finite-stalk and local-constancy clauses, and the complete
   docstring proof. Noetherian subspaces are compact, etale images are open, finite
   subcovers give finitely many constant finite values, and set inverse-image stalk
   comparison plus forget/stalk comparison transfer the bound. Empty schemes, empty
   strata, zero sheaves, disconnected schemes and varying stalk orders cause no exception.
   Checked the source definition and partition lemma at
   [Stacks 03RW](https://stacks.math.columbia.edu/tag/03RW) and
   [Stacks 095E](https://stacks.math.columbia.edu/tag/095E).
   Independent searches used LeanFinder "locally constant finite sheaf on a compact
   scheme stalk sizes bounded", Loogle "Finite, Nat.card, CategoryTheory.Sheaf", and
   Mathlib grep "IsLocallyConstant.range_finite|constructible.*card|sheafFiber.*card";
   also searched project and upstream declarations by stalk/cardinality/bound concepts.
   The hits include locally constant functions with finite range, not the missing
   geometric-stalk local constancy argument. No matching proved uniform bound was found.
   The hole is strictly the geometric part: the factorial and morphism argument is real
   Lean code. Its node and verbatim Lean signature agree. Closing this geometry would
   require formalizing the stratification and cover argument, beyond a short review repair.
4. **Route and pruning: PASS after repair.** Read the original proof_deps and
   dag/units/sk-thm-p1.json realized fields. This node is below the unit's fixed steps;
   the reduction preserves the constructible curve calculations and bypasses no realized
   unit statement. Direct jointly faithful stalk extensionality is shorter than the old
   image/exactness route. No longer needed now lists all three old dependencies removed
   from this argument: constant-sheaf abelian comparison, abelian inverse-image germs,
   and stalk exactness. Conservativity remains. Public imports of the new module are
   required by its signature; tested removal of EtalePoint, which fails because
   algClosurePoint is required publicly, and restored it. Proof imports are private.
5. **Nodes and accounting: PASS after repair.** Original node changes are restricted to
   its actual reduction's proof, proof_deps and proof_origin. New node has source,
   full proof steps, union of step dependencies, searches, creation attribution,
   blueprint origin, chapter, unit and Lean record. One original hole closed and one
   geometric hole added: decomposition, net zero, not an axiom-free completion.

Changed the item's stale proof docstring to describe N factorial and direct stalk
extensionality. Replaced the lower module's abelian inverse-image import and node
citation with the existing proved set-valued inverse-image comparison, updated its
proof explanation and the pruning report. No mathematical statement or proof term
was changed by this second reading.
