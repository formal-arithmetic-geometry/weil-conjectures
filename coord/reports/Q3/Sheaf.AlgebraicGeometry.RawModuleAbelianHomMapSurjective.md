## What changed

Proved `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_surjective` with its original
signature, visibility, definitions and public import unchanged. Added only proof
imports to the target. The one new module is
`Sheaf.CategoryTheory.Abelian.DerivedHomComparisonSurjective`.

The proof uses the existing `rawModuleFreeSourceHom_bijective` for degree zero and
`rawModuleFreeSource_acyclic` for forgotten injective coefficients. The proved
`nonempty_extFunctor_iso_rightDerivedHom` transfers the latter to positive Ext
vanishing. The new generic theorem lifts Ext classes by dimension shifting and
identifies their images with the precise bounded-below single/shift comparison.
The target proof then cancels the shifted coefficient inverse-image isomorphism.

Source read: https://stacks.math.columbia.edu/tag/03FD, both the universal
delta-functor argument and the injective-coefficient vanishing paragraph. The
formal dimension-shifting implementation is agent-written. No change records or
forced adaptations are needed.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.rawModuleAbelianHomMap_surjective`
(node `lem-sbc-raw-module-abelian-hom-map-surjective`).
Added zero holes. The new supporting theorem
`CategoryTheory.derivedHomComparison_surjective`
(node `lem-sbc-derived-hom-comparison-surjective`) and its private
`extComparison_surjective` helper are proved. No delivered file contains `sorry`.
Existing imported project statements may still contribute `sorryAx`; this is not
an assertion that the entire target import closure is proved.

The second reading removed the first worker's proved but redundant
`rawModuleFreeHom_surjective` and `rawModuleFree_injective_acyclic` modules and
nodes, using existing declarations and a local Ext transport instead. These were
never landed and introduced no holes. This delivery is a proof, not a decomposition.

## No longer needed

The old proof dependency `lem-weil-pbc-injective-module-abelian-acyclic`
(module `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`) is replaced by the
existing correctly-universed free-source acyclicity theorem. This removes that
proof edge; it does not establish that the module is globally unreachable.
No original import was removed (that dependency was not imported originally).

The unlanded candidate modules `RawModuleFreeHomSurjective` and
`RawModuleFreeInjectiveAcyclic` and their candidate nodes are removed entirely.
The generic theorem uses `Ext.Basic`, `Ext.EnoughInjectives`, and `Ext.Map`;
`Ext.MapBijective` is unnecessary because forgetting scalars is not full and need
not preserve abelian injectives. All remaining imports support signatures or proofs.

## Where the brief, the DAG or earlier work was wrong

The old ringed-site acyclicity statement has equal site/coefficient universes,
whereas these small etale sites use coefficients in Type(u+1). The existing
free-source acyclicity theorem fits this interface. The first worker duplicated
both that result's underlying constructions and the already available ordinary
free-source Hom comparison. The second reading removed those duplicates.

LeanSearch was unavailable to the first worker (Internal Server Error); its failed
attempt is recorded honestly. Independent second-reader LeanFinder and Loogle
searches found Ext.mapExactFunctor and injective-resolution APIs, but no complete
fixed-source surjectivity criterion. Mathlib's Ext bijectivity theorem requires
fullness and preservation of injectives, which are unavailable here. Repository
searches found the two concrete results now reused.

## New nodes

`lem-sbc-derived-hom-comparison-surjective` in
`Sheaf.CategoryTheory.Abelian.DerivedHomComparisonSurjective` is a proved generic
criterion for an additive exact functor: degree-zero comparison surjectivity and
positive Ext vanishing on images of injectives imply derived comparison
surjectivity. The induction uses injective presentations, cokernels, connecting
maps, functoriality of extension classes and the fully faithful D+ inclusion.
The node records all three original search types and the unchanged chapter, unit
and blueprint ancestor. It introduces no unproved statement.

## Second reading by Q3

1. Compared every delivered module with the repository. The only existing module
   is the target: its theorem signature and public import are byte-for-byte
   unchanged; only proof imports, a local elaboration option and its proof differ.
   The other remaining module is new. No definition or target interface changes.
2. Read both complete proofs. The Ext induction treats degree zero with homEquiv₀.
   In degree n+1, exactness preserves N→I→coker, vanishing makes the target
   connecting map onto, induction lifts its preimage, and mapExactFunctor_comp /
   mapExactFunctor_extClass plus Yoneda associativity establish the image equality.
   The D+ inclusion is faithful; its shift and single comparisons cancel in the
   displayed calculation. The final raw-map proof uses the actual freeMap and
   inverse-image mate and cancels its coefficient isomorphism. Local compilation
   and explicit axiom checks are recorded below. No forbidden declaration or
   hollow definition occurs; chosen injective presentations and the proved Ext
   comparison have no newly unproved existence witnesses.
3. No statements are split off with sorry. The generic theorem is strictly an
   abstract ingredient rather than a renamed raw-map claim. Checked n=0, the zero
   source/coefficient, and zero categories: degree-zero lifting is exactly hzero;
   only strictly positive Ext groups are assumed zero. Concrete zero rings and
   empty etale objects are covered by the two reused theorems, without additional
   hypotheses. Independent searches used different phrases from the first worker
   and located the redundant concrete proofs, which were removed.
4. The proof now takes the shorter existing-library route for both ordinary Hom
   and acyclicity. Remaining new work is the generic Ext induction. The entire
   old proof_deps list consisted of the acyclicity node named in No longer needed.
   Read dag/units/sk-lem-failure-field.json: its realized.statement and sole
   realized.steps entry are empty; this auxiliary raw-comparison node realizes no
   unit step. No unit or chapter record, statement, or route changes.
5. Checked the nodes against the final Lean. The target's four proof dependencies
   are the existing degree-zero bijectivity, free-source acyclicity, Ext-derived
   Hom comparison, and new generic criterion. Its final isomorphism cancellation
   is elementary. The new generic node's proof is exactly the Ext induction and
   D+ transport; it has source, searches, provenance, creation and Lean records.
   Its public signature matches the node's Lean statement verbatim.

Changes by the second reader: removed two redundant new modules and nodes;
replaced their uses by existing theorems and a local Ext transport; corrected the
target's proof dependencies and this report. No existing signature changed.
