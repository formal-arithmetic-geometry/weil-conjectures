## What changed

The original proof changes are in
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean`.
The delivery proves its two flatness instances and finite-extension pushforward instance.
The H4 repair removes the complete private definitions `extendTensorIso` and
`forgetExtendIsoTensor`, replaces every use with `extendForgetTensorObjIso` or
`extendForgetTensorIso`, and exposes those two existing definitions in
`lean/WeilConjectures/CategoryTheory/ModuleObjects/DerivedExtendScalars.lean`.
Their types and construction bodies are unchanged. The earlier repair also exposes the
existing proved `restrictedRegular_rightAction`, used internally by the shared construction.
The dependency module is unclaimed. Its users and the exact visibility changes are recorded
in `coord/changes/E4-reuse-restricted-regular-right-action.md` and
`coord/changes/E4-visibility-reuse-extend-tensor-isos.md`. The existing public import of
`ChangeOfCoefficients` supplies these declarations; no extra import is needed. Existing
mathematical statements, comparison constructions and public imports retain their meaning.
The proof-only instance changes are recorded in
`coord/changes/E4-coefficient-flatness-proofs.md`.

The H10 repair optimizes the existing definitions in
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean`.
The export profiler identified the premise-index extension traversing the expanded derived
functors in public comparison signatures. Four ordinary definitions name the source and target
composites of `derivedPushHom` and `derivedLowerShriekHom`. These two comparisons use the
names in their types; their construction bodies are unchanged, and the types are definitionally
equal to the originals. The four alias types are inferred from fully specified composites,
avoiding repeated unification against their expanded categorical types. This fixes the expensive
definition in place, without a module/proof
split, an added hole, a target change or an increased limit. The definition record
`coord/changes/E4-compact-derived-comparison-signatures.md` gives the exact old and new
code and every downstream user. The module is unclaimed, and no consumer source is adapted.

For finite extensions, construct the coordinate and basis-vector maps on continuous-function
presheaves. Their module-linearity is checked on pure tensors; the basis identities give a
finite biproduct isomorphism. Transport this through sheafification, its counit ring
isomorphisms, and inverse image from the point. A finite sum of regular modules is flat.
The scalar-extension coequalizer is naturally isomorphic, after forgetting the target action,
to relative tensor with the restricted regular module, which transfers flatness to exactness.
All the new helpers are private and completely proved.

For the algebraic closure, explicitly construct the diagram of restricted finite coefficient
modules indexed by `Under E`. Its underlying cocone is the existing coefficient cocone
whiskered by the final functor `Under.forget E`. Reflect its colimit through the module
forgetful functor. Finite-stage flatness and exactness of filtered colimits imply flatness
at the closure.

For finite pushforward compatibility, express the scalar-extension unit as a finite basis
isomorphism after restriction. Lift the basis endomorphisms through complexes, the homotopy
category and localization to the unbounded derived category. Pullback transports these scalar
endomorphisms, and adjunction gives the corresponding compatibility for derived pushforward.
The finite biproduct decomposition of the units then proves that the canonical mate is an
isomorphism. The basis data are a private, explicitly constructed structure; a general lemma
for inverse commutative squares avoids expensive kernel unfolding of the geometric square.

The proof-only imports are `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
`WeilConjectures.ConstructibleSheaf.FreeLifting` (its proved `ObjectProperty.flat_colimit`), and
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. No `Sheaf`
statement module is needed for these proofs. The original finite-free / filtered-colimit route is retained, so no existing
node proof route changes.

The second reader independently ran the required `lcompile.py --all`: all three delivered
modules exported successfully (`DerivedExtendScalars` 5.1 seconds, `ChangeOfCoefficients`
48.5 seconds, and `Compatibility` 28.3 seconds before the local helper cleanup). Both unchanged comparison-consumer sources are also checked
against the final sandbox outputs. The delivery is checked with `deliver3.py --no-push`.

## Proved and sorry left

Closed three of the four original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`.
- `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`.
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`.

The one original hole left unchanged is:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`:
  needs the corresponding proper unbounded pushforward comparison with the filtered
  coefficient colimit.

The two original flatness obligations occur in the historical `lean_audit` of
`prop-weil-pbc-qbar-condensed-two-colimit`; there is no separate `lean.module` attachment
for this item. The remaining proper-pushforward obligation is the existing input explicitly
cited in the proof of `prop-weil-pbc-qbar-condensed-basechange-compatibility`. No holes were added or split off. Independent `#print axioms` checks of all three completed
instances showed only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The closure-flatness proof uses the existing
`Profinite.isColimitPadicAlgClRingObjCocone` input; it does not reprove that separate obligation.

## No longer needed

No original imports were removed and no whole existing module or DAG node was made
unreachable. The repaired delivery removes duplicate private declarations
`CategoryTheory.Mod.rightAct_regular`, `CategoryTheory.Mod.extendTensorIso` and
`CategoryTheory.Mod.forgetExtendIsoTensor`; their uses are served by the existing shared
right-action lemma and tensor isomorphisms. The earlier second reading removed the redundant added proof imports
`Mathlib.CategoryTheory.Filtered.Final` and `Mathlib.CategoryTheory.Center.Localization`;
their APIs are already available through the remaining imports. Pruned modules/nodes: none. The proof does not import
`Sheaf.Paper.CondensedFlatCoefficientCalculus` or ordinary constant-coefficient module-sheaf
lemmas; their interfaces are unnecessary for the flatness arguments here, and the former
already depends on this item through the coefficient-comparison modules.

## Where the brief, the DAG or earlier work was wrong

The search for this item's module finds its audit entry in
`prop-weil-pbc-qbar-condensed-two-colimit`, rather than a node whose `lean.module` is this
module. The flatness proof follows the argument already stated in this module's docstring.

The existing exceptional inverse image in
`ModuleObject/Derived/UpperShriek.lean` supplies an adjoint only on bounded constructible
categories with additional geometric hypotheses. It does not directly justify the docstring's
claim of an adjoint to proper pushforward on the ambient unbounded categories in this item's
last instance. That comparison remains unchanged and unproved; no statement is weakened.

The prior delivery duplicated the shared right-action theorem and both shared tensor
isomorphism definitions despite their existing implementations in `DerivedExtendScalars`.
The repair exposes and reuses the existing declarations. The maintainer also correctly found
that single-file typechecking missed the timeout seen when emitting both scratch modules.
Profiling showed that premise-index export, rather than the finite-basis proof, repeatedly
inspected expanded derived-functor signatures. The performance repair compacts those signatures
with definitionally equal named functors. Verification includes the exact exporting command
requested in H10, including the optimized dependency module.
No target or mathematical route changes, and no new node or postponed theorem is introduced.
The current second reading is recorded below.


## Second reading by E4

1. **Interfaces — pass.** Compared all three delivered modules with the read-only repository.
   The item's existing declaration signatures are unchanged. In `DerivedExtendScalars`, only
   the three declared visibility changes and the new right-action docstring occur; the types
   and bodies remain identical. In `ChangeOfCoefficients`, the two comparison signatures use
   four explicitly constructed functor aliases, exactly as the change record declares. Unfolding
   them gives the original signatures, and both comparison bodies are verbatim unchanged.
   No target or held downstream module is edited. The two changed dependency modules are
   unclaimed in the current claims snapshot. Rechecked the fourteen downstream consumers of
   `ChangeOfCoefficients`; the two direct external comparison users compiled unchanged against
   the sandbox outputs (10.9 and 45.7 seconds).

2. **Proofs and data — pass.** Read the complete finite-basis, flat-colimit, scalar-endomorphism,
   localization, and mate arguments. Independently exported all three modules with
   `lcompile.py --all`, and compiled the item after the second-reading cleanup. All three
   completed instances have only the standard three axioms. The one remaining proper
   algebraic-closure instance is the original named `sorry`; no hole was added, and no forbidden
   declaration or hollow definition occurs. The basis and scalar-endomorphism data are explicit
   constructions. Classical choice in the completed pushforward proof selects a basis
   isomorphism from the fully proved `padicSubfield_isFree`, not an arbitrary witness from
   an unproved existence claim.

3. **Split statements and searches — pass.** There are no split-off statements or new nodes.
   Searched the module-object, derived-category, center, and sheaf libraries with different
   terms, including conservative exact derived functors and scalar centers. The shared tensor
   isomorphisms are reused rather than copied. Found that the private `reflectsDerived`
   duplicated the upstream generic `Functor.reflectsIsomorphisms_mapDerivedCategory` in
   `SixFunctors/ProEtale/Derived/ScalarExtension`. Importing that module fails because its old
   `UpperLowerStar.Defs` notation collides with the already imported
   `FiniteCoefficient.UpperLowerStar.Defs`. Removed the duplicate standalone theorem and
   performed the short homology test locally at its only use. No incompatible import remains.
   Edge cases include identical fields (degree one), the rank-zero finite-biproduct identities,
   and the nonempty filtered category of overfields of a fixed finite field.

4. **Route and pruning — pass.** The proof retains the prescribed finite-free and filtered
   colimit route. The derived finite-pushforward argument checks the canonical mate using the
   basis decomposition of its units; it does not replace the canonical comparison by an
   unrelated isomorphism. Both original public imports are needed by public interfaces; all
   added imports are proof-only. No original proof dependency or realized unit step is
   bypassed, and no module or DAG node is pruned. In particular, the proper algebraic-closure
   comparison is still open rather than hidden behind a restatement.

5. **DAG and records — pass.** Read the relevant coefficient-comparison, flat-calculus,
   two-colimit, and base-change nodes, and the `sk-thm-properbasechange` realized route.
   This item has no direct `lean.module` node attachment: its flatness obligations are recorded
   in the historical two-colimit audit, and the proper comparison is the existing input of
   the base-change compatibility node. No node's mathematical statement or proof route needs
   changing. The four existing change records describe the three dependency visibility edits,
   unchanged instance signatures, and definitionally equal comparison signatures accurately.

Second-reading changes: removed the redundant private `CategoryTheory.reflectsDerived`
declaration and placed its homology argument directly at the sole use; updated this report
with independent signature, dependency, edge-case, compilation, and axiom checks. Three of
four original holes are closed, zero holes are added, and zero statements are split off.
