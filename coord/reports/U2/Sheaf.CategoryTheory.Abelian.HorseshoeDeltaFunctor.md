## What changed

Proved `CategoryTheory.exists_horseshoe_rightDerived_deltaFunctor` in
`Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`, preserving its complete signature
and all existing public imports and docstrings. Added proof-only imports of
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`,
`Mathlib.Algebra.Homology.HomologySequenceLemmas`,
`WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`,
`Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`, and
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`.

Private horseshoe data bundle the three resolutions, row maps, augmentation equations,
and degreewise exactness. A choice of this datum defines the transported boundary.
Each row splits by injectivity, and mapping its splitting proves exactness after applying
v. Additivity is supplied by the proved upstream instance for `v.rightDerived n`. Prescribed endpoint lifts extend to a
middle lift using the existing horseshoe-morphism lemma; homology boundary naturality
and the resolution comparison isomorphisms prove naturality for arbitrary horseshoes.
Three explicit short-complex isomorphisms transport the three exactness statements.
The degree-zero homology map is monic because there is no preceding natural-number
degree. These proofs construct all delta-functor fields. Applying naturality to the
identity ladder compares the chosen horseshoe to any supplied one, including exactly
the equation with `eqToHom` in the original theorem.

Updated only `proof`, `proof_deps`, and `proof_origin` in the existing node
`lem-weil-pbc-horseshoe-delta-functor`. Its statement, Lean signature, and unit stay fixed.
Added `coord/changes/HorseshoeDeltaFunctorHelpers.md` because the static interface
checker requires a record for the section variables, namespace opening, and elaboration
options used by the private proof helpers. These commands require no downstream
adaptations and change no public statement or definition.

The unit `sk-thm-p1` does not list this node among its realized statements or steps;
the unit route is preserved.

## Proved and sorry left

The item's one original sorry is replaced by a complete proof:
`CategoryTheory.exists_horseshoe_rightDerived_deltaFunctor`
(node `lem-weil-pbc-horseshoe-delta-functor`). All private helpers are proved, and every
private definition contains concrete data. There are no sorries left in the delivered
Lean file and no new deferred statements.

This is a stage-3 reduction using the existing deferred theorems
`CategoryTheory.InjectiveResolution.exists_horseshoe_resolutions`
(node `lem-weil-pbc-injective-resolution-ses`) and
`CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift`
(node `lem-weil-pbc-horseshoe-morphism-lift`). Their modules are imported and unchanged;
the delivery does not claim that these dependencies are axiom-free yet.

Local compilation succeeded without warnings. Both proof-only Sheaf imports were
checked by `tools/import_direction.py` and do not introduce a cycle.

## No longer needed

Pruned proof dependency `lem-weil-pbc-left-exact-injective-resolution-degree-zero`:
resolution existence is supplied by enough injectives, and the initial
monomorphism follows directly from the degree-zero homology map of the mapped horseshoe.
The isomorphism `R^0 v ≅ v` is not used. This node is a Mathlib leaf, so there is no separate
Sheaf module to remove for it. No existing imports were removed. The other original
proof dependencies remain used, including the horseshoe existence and morphism lift.
No claims are made that this pruned leaf is unnecessary elsewhere in the project.

## Where the brief, the DAG or earlier work was wrong

No false statements or incompatible dependency signatures were found. The second reader
found the proved upstream additivity instance that the first worker missed, and replaced
the duplicate private additivity proof with that instance and a proof-only import. The module
initially did not import its two Sheaf proof dependencies; the proof adds them privately.
The original DAG used the degree-zero left-exact comparison in its additivity route;
this additional comparison is unnecessary. Left exactness is not used in this proof,
but its hypothesis remains exactly as in the original statement.

LeanFinder, Loogle, and grep searches were run through the launcher search tool. They
found the Mathlib resolution comparison and homology sequence APIs, but no direct
horseshoe delta-functor theorem. The searches of the existing source library likewise
did not provide this construction. No new nodes or statement changes were required.

## Second reading by U2

1. Compared the delivered module against the repository with `diff`. The only existing
   declaration is `CategoryTheory.exists_horseshoe_rightDerived_deltaFunctor`; its signature
   and docstring are byte for byte unchanged. All existing public imports remain unchanged.
   The added data and helpers are private. The file-local commands have the existing change
   record `coord/changes/HorseshoeDeltaFunctorHelpers.md`; no public definition changes.
   Verdict: pass.
2. Compiled the complete file locally without errors or warnings. Searched for forbidden
   declarations and `sorry`: none. Read every helper and the final packaging proof.
   A scratch copy prints axioms for all nine retained helper/theorem declarations: only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter occurs in the
   horseshoe-existence and naturality paths through the two existing deferred dependencies
   listed above; exactness, boundary transport, and degree-zero monicity use only the three
   permitted axioms. No definition contains missing data. Verdict: pass as a reduction.
3. There are no split-off statements, new deferred theorems, or new nodes. The private
   statements have appropriate hypotheses: splitting uses the injectivity of the first
   resolution term, exactness is transported by isomorphisms, and the monicity argument
   correctly handles degree zero via the absence of a predecessor in natural numbers.
   Zero objects and identity ladders cause no exceptional case. Verdict: pass.
4. Searched the Sheaf and upstream source libraries and Mathlib using alternate additive,
   boundary, and horseshoe terms. Found a shorter route for additivity in the proved upstream
   module `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`. Removed the duplicate
   private proof and used its instance directly. Tested the two added Mathlib imports
   individually: both are required (`shortExact_of_degreewise_shortExact` and
   `δ_naturality`, respectively). The remaining imports support the statement or proof.
   Compared all old proof dependencies: the only pruned node is
   `lem-weil-pbc-left-exact-injective-resolution-degree-zero`, already listed above.
   Read `dag/units/sk-thm-p1.json`: none of its realized statements or steps is bypassed.
   Verdict: pass after the additivity simplification.
5. Compared the node JSON against its original: changes are confined to `proof`,
   `proof_deps`, and `proof_origin`. Checked that proof-dependency union agrees with the
   steps, and that the steps describe the constructed boundary, naturality, all three
   exactness positions, initial monicity, and identity comparison. Updated Step 1 and
   proof origin for the upstream additivity instance; no further dependencies are pruned,
   since resolution lifts and their comparisons are still used for naturality.
   Verdict: pass after metadata correction.

Second reading changed the private additivity proof to an upstream instance, added its
proof-only import, and synchronized the node and report. The remaining proof is retained.
