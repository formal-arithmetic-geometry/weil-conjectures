## What changed

The target theorem is now proved by composing two named intermediate results. `AffinePrincipalSheafComplexTransport` states the principal-open restriction and localization comparison, and `AffineFiniteFreeSheafComplexLift` constructs the finite-free module complex from the transported sheaf complex. The target module imports these proof modules privately. The affine lift uses tilde full faithfulness to lift differentials and transfer the strict upper bound. Second reading replaced its redundant public import of `Sheaf.AlgebraicGeometry.DerivedCategory` with the direct owner of `moduleRings`, `Sheaf.Paper.DerivedHomMayerVietoris`. The transport module privately imports `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`, as required by its remaining proof plan.

## Proved and sorry left

`AlgebraicGeometry.affine_pseudoCoherent_principal_sheaf_model` has its original hole closed by a checked reduction, conditional on the remaining transport theorem. This is not an axiom-free proof of the original theorem. The intermediate theorem `AlgebraicGeometry.affine_principal_sheaf_complex_transport` remains `sorry` as the incomplete principal-open transport step and is recorded by node `lem-pc-affine-principal-sheaf-complex-transport`. The affine lift theorem is proved and recorded by node `lem-pc-affine-finite-free-sheaf-complex-lift`. Holes closed: `AlgebraicGeometry.affine_pseudoCoherent_principal_sheaf_model` (1). Holes added: `AlgebraicGeometry.affine_principal_sheaf_complex_transport` (1). The new `AlgebraicGeometry.affine_finiteFree_sheaf_complex_lift` has no hole. Net change in holes: zero; this is a decomposition into a remaining restriction/localization step and a fully proved affine-lifting step.

## No longer needed

The target's direct proof import of `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
is replaced by the two new intermediate modules. It remains a private proof-plan import
of `AffinePrincipalSheafComplexTransport`, so it is not pruned from the import closure.
The original direct proof dependencies are replaced in the target node:
`lem-sc-derived-open-restriction-adjunction-exact` and
`lem-weil-pbc-spec-module-tilde-sections` remain dependencies of transport;
`lem-weil-pbc-affine-tilde-gamma-adjunction` remains a dependency of the proved lift.
The last two are Mathlib leaves supplied by `Mathlib.AlgebraicGeometry.Modules.Tilde`.
No original dependency node or module is globally pruned. The lift no longer directly
imports `Sheaf.AlgebraicGeometry.DerivedCategory`, using the narrower direct owner
of `moduleRings`; that module remains necessary in the target and transport statements.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped after observing that the principal-open and affine comparison were unavailable. Stage 3 permits these steps to be stated as named intermediate theorems with `sorry`; the affine tilde full-faithfulness declarations already suffice to make the finite-free lift compile. The transport theorem records the remaining derived comparison without asserting a module-derived isomorphism.

## New nodes

`lem-pc-affine-principal-sheaf-complex-transport` records the exact restriction, principal-open localization, and derived sheaf comparison step. `lem-pc-affine-finite-free-sheaf-complex-lift` records the finite-free module lift through the fully faithful affine tilde functor.

## Earlier second reading (a previous round; superseded)

`AlgebraicGeometry.affine_principal_sheaf_complex_transport` remains open as the transport node; `AlgebraicGeometry.affine_finiteFree_sheaf_complex_lift` and the target proof compile. The target statement is unchanged, and the new statements are strictly smaller steps of the recorded plan. The unit route remains through principal-open restriction and affine tilde/Gamma comparison.

## Second reading by V2

1. Compared the only existing delivered module against the repository with `diff`;
   separately compared the theorem signature byte for byte: identical. The only
   existing-module changes are private proof imports and the proof body. No definition,
   declaration signature, visibility, target, or change record is altered.
2. Compiled all three modules in import order through `lcompile.py`, without errors
   or warnings. A scratch copy with `#print axioms` confirmed the affine lift uses
   only `propext`, `Classical.choice`, and `Quot.sound`; transport uses `sorryAx`,
   and the original theorem uses those three standard axioms plus `sorryAx`.
   The sole written `sorry` is the named transport theorem, with its source,
   complete construction proof in its docstring, and matching node. There is no
   forbidden declaration or holed definition. The existential witness is eliminated
   only inside a proof of an existential proposition; no data definition is chosen
   from that unproved existence assertion.
3. Read both intermediate statements and the full-faithfulness lift proof.
   Restriction/localization is strictly part of the original argument: its conclusion
   is a sheaf complex, without constructing any module complex or lifted differentials.
   The proved lift supplies that missing step. Checked rank zero, the zero ring,
   empty D(f) (including nilpotent f), f a unit, U larger than D(f), and negative
   upper bounds: neither statement requires extra hypotheses. The proof reflects
   zero objects by faithfulness, so even arbitrary ranks chosen above the bound
   give zero modules in those degrees. Independent searches used leanfinder on
   restriction of locally free complexes to principal affine opens, loogle on
   `SheafOfModules.overFunctor`, and grep on `overFunctorMap`, `overFunctorEquiv`,
   `tildeFinsupp`, and `fullyFaithfulFunctor`. They find component comparisons,
   not the transport theorem. Also inspected the upstream Tilde extension,
   `AffineModuleComplexRepresentative`, `AffineFiniteFreeModelBounded`, and
   `AffineFreeComplexUnitCancellation`; none states either new result without
   different hypotheses or conclusions. The remaining transport construction
   needs site/scheme and derived-universe comparisons and was not closed in a
   short proof pass.
4. The proof uses the shortest affine lift via Mathlib's `tildeFinsupp` and full
   faithfulness; no new hole is introduced for lifting differentials or boundedness.
   Imports are retained for signatures or the named remaining proof plan. All three
   old proof-dependency replacements are accounted for above. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and sole step
   arrays are empty; this item is a lower auxiliary node. Principal-open
   restriction and affine tilde/Gamma comparison remain in the route, with no
   bypass of any realized unit node.
5. Read all three delivered nodes and the original node. The target's two proof
   steps and dependencies match the actual composition. The lift's Mathlib-leaf
   dependency matches full faithfulness; the transport node records the remaining
   restriction and principal-open comparison plan. New nodes have their creation,
   origin, searches, blueprint, chapter/unit and Lean records. Checked each Lean
   record against its declaration; no statement change is needed.

Second reading changed only the lift's redundant public import, the transport's
missing private proof-plan import, and this report's dependency and hole accounting.
Verdict: valid decomposition with one remaining hole and no net reduction of holes;
the affine lift itself is fully proved.
