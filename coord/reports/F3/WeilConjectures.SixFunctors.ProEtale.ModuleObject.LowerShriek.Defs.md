## What changed

Changed the proof only in `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean`.
Proved `AlgebraicGeometry.ProEtale.CondensedRing.hasProjectionFormula_openImmersion`, preserving
its signature and every definition and other declaration in the module. Updated the module
explanation to describe the completed proof. No imports were added or removed. Added
`coord/changes/proetale-module-open-shriek-projection-proof.md` because the static checker
conservatively counts every instance body edit as an interface change, including this
Prop-valued instance. The record lists every downstream module and explains why proof
irrelevance makes adaptation unnecessary.

The extension by zero is fully faithful: the adjoint triple transports the invertible counit
of restriction/pushforward to the unit of extension/restriction. Write `l` for the localization
functor and `R = Lan(l.op)(M.obj) ⊗ L.obj`. At an object with empty localization comma category,
the Kan extension is initial, hence zero, and tensoring preserves initial objects. Thus `R`
vanishes there. The existing `Functor.isIso_lanAdjunction_counit_app_of_isZero` reconstructs
`R` as extension of its restriction. Uniqueness of left adjoints identifies sheafification
of presheaf extension with extension of sheafification; monoidality of sheafification then
shows that `L ⊗ j_! M` is in the essential image of `j_!`. Its adjunction counit is therefore
invertible by `Adjunction.isIso_counit_app_of_iso`. The actual canonical projection map is,
by its definition and `Adjunction.homEquiv_counit`, the image of the invertible unit and
monoidal tensorator followed by this counit. This proves its invertibility, rather than
merely constructing an unrelated isomorphism between the same objects.

Source read: the support proof in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful` and the
essential-image argument in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Projection`. The proof here
adapts that argument to the current `FiniteCoefficient` interfaces. It uses existing
Mathlib/library declarations already available through this module's original imports.
The empty comma-category case is handled explicitly, so the proof also covers the empty
open and identity immersion, without any finiteness or clopen hypothesis.

Searches run through `msearch.py`: Lean Finder, "projection formula for extension by zero
of sheaves along open immersions" (no directly applicable result); Loogle,
`CategoryTheory.Functor.LaxMonoidal.μ` (including invertibility for strong monoidal functors);
grep, `isIso_counit_app_of_iso` (Mathlib's essential-image criterion). Repository searches
found the two source modules above and no attachment of this item's module or declaration
in `dag/nodes`. The original module has no blueprint tags. No node copies could therefore
be updated, and no new statement requires a new node.

Validation: the complete module compiles with `lcompile.py` without errors or warnings
(about seven seconds). Every line is at most 100 characters. The second reader runs the delivery dry run and delivers after completing the review.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.hasProjectionFormula_openImmersion`.

No `sorry` remains in the item's module. No holes, declarations, helper modules, or nodes
were added. This is a proof, not a decomposition. Existing dependency proofs are unchanged.

## No longer needed

None: the original three public imports are retained and needed by the module's statements
and definitions. No proof-dependency imports or attached DAG nodes existed to prune.
The older `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Projection`
and `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful` modules
are not imported: their arguments are adapted using the already available general lemmas.
No library module is withdrawn or claimed to have left the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original module has no DAG `lean.module` attachment and no blueprint tag, despite the
brief's expectation that such nodes supply a plan. This does not prevent a direct proof.

Importing the existing non-`FiniteCoefficient` projection module fails immediately because
it brings an older duplicate `ProEtale.UpperLowerStar.Defs` into an environment containing
`ProEtale.FiniteCoefficient.UpperLowerStar.Defs` (duplicate scoped notation declaration
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`). The final proof needs neither conflicting
module nor an interface change: it uses the corresponding current adjoint triple and the
existing general Kan-extension support theorem directly.

The dry run's `leanindex.interface` compares whole instance bodies, so a Prop-valued
instance proof change requires a change record even with an identical statement. This
is handled explicitly in
`coord/changes/proetale-module-open-shriek-projection-proof.md`; no tool was modified.


## Second reading by F3

1. **Visible interface: PASS.** Compared the complete delivered module with the repository
   using `diff`, and checked the declaration table with `stage3_delivery.diff_module`.
   The only declaration edit replaces the proof of
   `AlgebraicGeometry.ProEtale.CondensedRing.hasProjectionFormula_openImmersion`.
   Every existing signature, binder, universe, visibility, definition body, and import
   is unchanged. The accompanying change record accurately explains the conservative
   instance-body interface check; the instance is Prop-valued, so proof irrelevance
   preserves every downstream use.
2. **Proof and axioms: PASS.** Independently compiled the complete module through
   `lcompile.py`: exit 0, no errors or warnings, 6.4 seconds. There is no `sorry` or
   forbidden declaration/attribute in the delivered Lean. In a scratch copy appended
   `#print axioms` for all 21 explicitly named declarations. The newly proved instance
   uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The other declarations use only these axioms, with `sorryAx` also present for the
   existing coefficient-dependent constructions: the imported `ModuleObject.Basic`
   still contains open coefficient-site and monoidality proofs. No data definition
   or choice was changed or added. The scratch print commands generated line-length
   warnings; the delivered module itself has no line longer than 100 characters.
   Read the Kan-extension support theorem and localization dichotomy, the current
   adjunction definitions, and the definition of the canonical projection map. The
   proof establishes invertibility of that map via `homEquiv_counit`, not merely an
   isomorphism between its endpoints. The empty-comma case gives zero tensor factors;
   the essential-image case uses full faithfulness. These cover the empty and identity
   open immersions without extra hypotheses.
3. **Split statements: PASS (none).** No statements, split-off holes, or helper modules
   were added. One original hole is closed and zero holes are added. Independent
   `msearch.py` grep for `HasProjectionFormula` found no Mathlib match; repository
   searches locate the existing general projection-map criteria and the older
   pro-etale projection proof, which the author correctly adapts without importing
   the conflicting older coefficient interface.
4. **Shortest route, imports, and unit: PASS.** The existing fully faithful adjunction
   and support arguments are used directly; no unresolved auxiliary lemma is needed.
   The final unfolding is shorter than importing and comparing the differently
   oriented older projection-map API. The three public imports are required by
   existing public statements or definitions: the projection-formula module by the
   class and module lift, finite-coefficient lower shriek by the geometric functors,
   and module upper/lower star by the coefficient objects, maps, and upper star.
   No proof-only public import was introduced. `## No longer needed` is complete:
   there are no old attached `proof_deps`, removed imports, or pruned modules.
   No unit realization or chapter route is changed.
5. **DAG agreement: PASS (no attachment).** Independently searched every node and unit
   for the exact module and instance names; neither has an attachment or blueprint
   tag. There are no node files in this delivery and no new statements requiring
   nodes. Thus there are no attached `proof`, `proof_deps`, or `proof_origin` records
   to update and no `realized` field to change. The report explicitly records this
   mismatch with the generic brief.

Second reading changes: added this independent review and its axiom evidence, and
updated the earlier validation sentence to reflect the second reader's delivery.
The Lean proof and change record needed no repair.
