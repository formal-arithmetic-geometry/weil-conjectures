## What changed

Proved `AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_target_stalkComparison`
in `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso` without changing
its signature or existing docstring. The final composition argument is written directly
in this theorem, with no additional helper declaration.

The proof first obtains qcqs for f′ from sq, then applies the existing
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk` to sqB and g′*G.
Naturality transports this to the derived inverse image of G[0], using
`NatTrans.isIso_app_iff_of_iso`. All remaining factors of the cube target comparison
and its stalk comparison are images of isomorphisms. The node's proof and dependencies
now record this route. The unit sk-thm-p1's statement and realized steps are unchanged;
this reduction occurs below its realized nodes. No data are chosen from existence proofs.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_target_stalkComparison`
(node `lem-weil-pbc-strict-henselization-exchange-cube-target-stalk-iso`).
No sorry remains in this module, and none is added by this delivery. This is a proof from
existing stated dependencies, including the still-unproved
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk`
(node `lem-weil-pbc-strict-local-base-change-closed-stalk`); it is not an axiom-free
closure of the entire argument. No new theorem or helper is declared.

## No longer needed

Removed these six direct proof imports:

- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `Sheaf.Paper.InverseImageStalkGerm`
- `Sheaf.AlgebraicGeometry.GeometricPointFieldExtension`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.BaseChange.Square`

The corresponding direct proof edges to
`lem-weil-pbc-unrestricted-strict-henselization-stalk`,
`lem-weil-pbc-strictly-henselian-sections-stalk`,
`lem-weil-pbc-inverse-image-stalk-germ`, and
`lem-weil-pbc-geometric-point-field-extension` are unnecessary here. The closed-stalk
lemma packages the strict-local geometry; some of these modules remain transitive
imports of that lemma. ExactFunctor and Square remain available through the unchanged
public imports. No claim is made that these modules leave the whole targets' closure.
The sole direct proof import is
`Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk`.

## Where the brief, the DAG or earlier work was wrong

The old plan expanded the strict-local geometry separately in this component even though
an existing chosen-model closed-stalk theorem already supplies precisely the nonformal
base-change factor. No statement error or forced adaptation was needed.

The earlier attempt was blocked because the compiled snapshot lacked
`StrictLocalBaseChangeClosedStalk.olean`. That dependency is now published. The final
proof compiles against the actual existing theorem, with no temporary assumption.
A declaration-scoped `linter.unusedVariables` option suppresses warnings for the
unchanged cube hypotheses and unused signature lets; the shorter proof only needs
the target cartesian square. No option affects other declarations or importers.

Repair of return point 1 (duplicate statement): removed the entire private declaration
`AlgebraicGeometry.isIso_derivedStalkComparison_of_map`. The existing theorem in
`Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource` is private;
an ordinary import cannot expose it, and changing its visibility would be an unrelated
interface change in another item. Instead, the target proof now handles the point
equality locally and simplifies `derivedStalkComparison` directly, then invokes the
existing functor/composition isomorphism instances. There is no renamed or restated
replacement theorem, no additional dependency, and no change to another module.
The DAG's final step records this direct proof. The previous second reading predates
this repair and has been removed so the independent second reader can review it anew.

Validation: the repaired module compiled with `lcompile.py`, exit 0, without warnings.
`deliver3.py T1
Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso --no-push`
printed OK: compiles and passes preflight except for the pending independent second
reading. The exact landing check `tools/import_prune_check.py` also passed, exit 0,
against the current repository module and this repaired sandbox module. Signatures are unchanged,
there are no new sorries, and all Lean lines meet the 100-character limit. Nothing pushed.

## Second reading by T1

Independent second reading of the repaired delivery, 2026-10-13:

1. Compared the sole delivered Lean module with the repository using `diff -u` and
   a byte-for-byte signature comparison. PASS: the existing theorem's complete
   signature, visibility, and docstring are unchanged. Only its proof, a scoped
   unused-variable linter option, and ordinary proof imports differ. No definitions,
   target statements, other modules, or public imports changed; no change record is
   required. The node's recorded Lean statement also matches the signature exactly.
2. Compiled the actual sandbox module with `lcompile.py`: exit 0, no warnings.
   Refreshed the stale scratch copy from the current module and compiled it with
   `#print axioms` for the target theorem. PASS: only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` occur. The existing closed-stalk dependency is still
   open, as reported. The delivered source contains no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or kernel-check bypass. No definition or arbitrary
   witness is introduced.
3. PASS: zero new statements and zero split-off holes. Read the existing closed-stalk
   theorem and the comparison definitions: its specialization uses f′, ντ, eB, sqB,
   ρB, and g′*G with exactly the required hypotheses. The two qcqs instances follow
   from sq. There is no torsion assumption to manufacture. The argument works at
   q = 0 and for the zero sheaf or empty total space; no nonzero object or positive
   degree is assumed. Read Mathlib's `NatTrans.isIso_app_iff_of_iso` to check that
   `.mpr` transports along the single-complex comparison in the correct direction.
4. PASS: searched the library and upstream SixFunctors for closed-stalk and cube
   comparison isomorphisms, and Mathlib for natural-transformation component
   invertibility. The existing closed-stalk theorem is the direct geometric route.
   The related generic helper in StrictHenselizationExchangeCubeStalkIsosSource is
   private; the local equality elimination and final `infer_instance` avoid
   duplicating it. Both public imports provide signature objects; the sole ordinary
   import provides the closed-stalk theorem. The report lists all six removed direct
   imports and all four removed old proof edges. Read sk-thm-p1's `realized`: this
   component is below its realized nodes, none of which is bypassed or modified.
   No whole-closure pruning is asserted.
5. PASS: compared the node JSON with its repository version. Only proof,
   proof_deps, and proof_origin differ. Their three steps match the Lean argument,
   and proof_deps is exactly the union of their uses. The statement, source,
   stmt_deps, blueprint, unit, and existing Lean record are unchanged. There are no
   new nodes requiring additional fields.

Second reading changed no delivered Lean or DAG file: the repaired proof is sound
as written. Refreshed the stale axiom-check scratch file (not delivered) and added
this independent review. One original named hole is closed, zero holes are added;
this remains a reduction to an existing open theorem rather than an axiom-free
closure of the whole argument.
