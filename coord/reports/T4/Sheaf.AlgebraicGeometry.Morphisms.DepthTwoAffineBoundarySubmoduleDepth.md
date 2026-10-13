## What changed

The existing `AlgebraicGeometry.Scheme.depth_one_affine_boundary_submodule` signature and
its docstring are unchanged. Its proof constructs the finite localization instance from
`S.FG` and affine Noetherianity, then applies maximal-associated-prime exclusion and the
positive-depth consequence. The two new intermediate statements are in their own modules:
`Sheaf.AlgebraicGeometry.Morphisms.BoundaryMaximalNotAssociated` and
`Sheaf.RingTheory.DepthOneOfMaximalNotAssociated`. Both target imports are proof-only.
The unused public `Mathlib.Algebra.Category.ModuleCat.Stalk` import was removed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.depth_one_affine_boundary_submodule`
(node `lem-sbc-affine-restriction-boundary-submodule-depth`) by a reduction, not a complete
proof: it still depends on the geometric intermediate below.

Proved `AlgebraicGeometry.Scheme.depth_one_of_finite_localized_module_of_no_maximal_associated`
(node `stage3-depth-one-from-no-maximal-associated`) using the existing proved
`exists_mem_maximalIdeal_smul_injective` and Mathlib regular-sequence lemmas, including the
zero-module case.

Added one hole, exactly the named theorem
`AlgebraicGeometry.Scheme.boundary_maximal_not_associated`
(node `stage3-boundary-maximal-not-associated`). It states only the geometric
associated-prime exclusion, without the target's finiteness/depth conclusion. Thus this is
one upper hole closed and one strictly simpler lower hole added, net zero holes: a
decomposition. The second reading closes the extra algebraic hole left by the first writer.
There are no data definitions or arbitrary choices of witnesses from unproved existence.

## No longer needed

Removed `Mathlib.Algebra.Category.ModuleCat.Stalk`, unused by these statements and proofs.
Removed the first writer's `Mathlib.RingTheory.Ideal.AssociatedPrime.Localization` import.
No Sheaf/WeilConjectures module or old dependency is pruned from the transitive route.

All four old direct `proof_deps` have moved below the intermediate nodes:
`lem-weil-pbc-affine-module-basic-open-localization`,
`lem-weil-pbc-associated-prime-submodule`, and `pqf-lem-pushforward-qcoh` are needed by
`stage3-boundary-maximal-not-associated`; and
`lem-weil-pbc-nonzerodivisor-if-maximal-not-associated` is used in the proved depth helper.
The target's new direct dependencies are the two intermediate nodes.

## Where the brief, the DAG or earlier work was wrong

The first writer left the elementary depth step as a hole even though the existing
regular-element theorem and Mathlib singleton regularity prove it directly. The new
statements were in the item's module rather than their own modules. Their comments were
not declaration docstrings; the target's existing docstring had accidentally attached to
the new depth helper. The new nodes lacked sources, verbatim Lean signatures and recorded
searches, and their dependency lists did not match their proof steps. The target node was
not updated. These faults have been repaired. The loose root-level Lean file is an older
scratch file and is not delivered.

## New nodes

`stage3-depth-one-from-no-maximal-associated`: proved finite local-module tool, using
Tag 00LL and a singleton sequence in the depth supremum. Its three searches found only
ingredients; existing private analogues were inspected and their elementary route used.

`stage3-boundary-maximal-not-associated`: only the geometric step of the original
argument, from Tag 0AVN. Its docstring gives the finite-basic-open injection argument,
localization and the annihilator contradiction, including the empty-cover case. The
source was checked at https://stacks.math.columbia.edu/tag/0AVN . Searches with alternative
phrasing found no already stated exact boundary exclusion. The import-only change record is
`coord/changes/depth_one_affine_boundary_submodule_unused_stalk_import.md`; no existing
declaration signature, definition or docstring changes.

## Second reading by T4

1. Compared the delivered target module with the repository by diff. The existing theorem
signature and docstring are byte-for-byte unchanged. Only the proof and imports change.
The helpers are new declarations in new modules. No target or definition changes.
2. Checked all delivered files for forbidden constructs: none; the sole remaining `sorry`
is the named geometric theorem above, with no inline proof holes and no definitions.
Local compile and axiom checks are recorded after verification below.
3. Read the split statements top down. The geometric statement is true by the finite-cover
argument of Stacks Tag 0AVN and strictly less than the target: it asserts no depth bound
or finite witness. Tested the zero submodule, empty U, empty cover and a generic boundary
prime (where the zero-module case must occur if the localization ring is a field). The
algebraic statement is now proved, with an explicit zero-module branch. Repeated
leanfinder, loogle and grep searches with different terms, and searched the local library;
only ingredients and private depth helpers were found.
4. The shortest algebraic route uses the existing proved regular-element theorem, followed
by the singleton regular sequence. The geometric route still needs the old affine
localization, qcqs pushforward and injective associated-prime tools. The unit record
`dag/units/sk-prop-input-spreading.json` has empty `realized` step arrays; this below-unit
reduction retains the original route and changes no unit realization. Imports are scoped
to statements or proof plans; the unused stalk/associated-localization imports are removed.
5. Checked the target and both new nodes against the delivered Lean: signatures recorded
verbatim, sources and three searches present, proof-dependency sets equal unions of step
uses, and origin places match each argument. The target now depends on the two named
intermediates, and the original four dependencies are retained through those nodes.

Second reading changed: proved the algebraic helper; put helpers in their own modules;
restored the target docstring attachment; supplied the geometric docstring proof and
complete node metadata/searches; synchronized the target DAG and report; removed unused
imports and instance-style warnings.

The required LeanSearch queries were also attempted for both new nodes; the service
returned Internal Server Error. The unavailable searches are recorded without a match
verdict; LeanFinder, Loogle, Mathlib grep and local-library searches supplied the checks.

Verification: all three delivered modules compiled locally through `lcompile.py`, and the
separate scratch copy with `#print axioms` compiled without warnings. The algebraic depth
helper uses exactly `propext`, `Classical.choice`, `Quot.sound`; the target and geometric
helper additionally use `sorryAx`, as expected from the sole documented geometric hole.
No other axiom occurs. The target signature was compared byte-for-byte against the
repository, not merely up to Lean elaboration.

The unused public stalk import has an import-only change record. Its sole direct importer,
`DepthTwoAffineFiniteQuotientDepth`, already publicly imports that same stalk module, so
its API and that of its downstream importers are preserved without adaptations.

Final dry run: `deliver3.py T4 Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineBoundarySubmoduleDepth --no-push` printed OK for commit `ada4482712`: local compilation, every-declaration axiom probes and preflight passed. Delivery is CODEX because it adds intermediate nodes/modules and removes an unused public import, with its change record.
