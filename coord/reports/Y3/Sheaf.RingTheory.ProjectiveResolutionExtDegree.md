## What changed

Repair upstream review #1428 with the generic explicit bounded-projective-resolution
bridge in Sheaf.RingTheory.ProjectiveResolutionExtDegree. The existing declaration
ModuleCat.projective_resolution_ext_degree is retained, with a recorded
statement generalization to abelian categories with enough projectives. Its
ModuleCat specialization is definitionally the old proposition. The resolution
and augmentation are constructed explicitly. No target or definition changes.

Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise receives exactly
one forced proof edit: omit .{u, u} (R := R) at the bridge call. All its existing
signatures and visibility are byte-for-byte unchanged. ExtAllDegrees and
ExtCharacterization compile unchanged and are not delivered.

## Proved and sorry left

ModuleCat.projective_resolution_ext_degree is proved, with no sorry left.
Holes closed relative to the repository snapshot: none (the specialized theorem
was already proved). Holes added: none. This is an interface repair and
generalization, not net sorry progress or a decomposition.
AlgebraicGeometry.affinePolynomial_boundedResolution_of_stalkwise remains proved.
No split-off declarations or new nodes are added.

## No longer needed

Removed imports: Sheaf.RingTheory.GlobalDimension,
Mathlib.Algebra.Category.ModuleCat.Abelian, and
Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic.
Removed old proof dependency: def-weil-pbc-finite-global-dimension; its specialized
predicate is replaced by the explicit existential in the generic signature.
The other old proof dependency def-pc-ext is retained via Mathlib Ext.
No entire downstream module is pruned: GlobalDimension remains used by callers.

## Where the brief, the DAG or earlier work was wrong

The first worker's change record and scratch validation described a retired name
and three forced adaptations, while the delivered theorem retained the old name.
Only the affine caller actually needs adaptation. Its explicit ring argument and
universe instantiation are incompatible with the generic signature. Reproduced
this failure, repaired the call, and corrected the record. The node's status had
also been changed outside the stage-3 owned fields; restored the baseline status.


Current retry (2026-10-13 21:08 UTC): deliver3.py --no-push again refuses the
forced affine adaptation because the original caller already fails against the
published compiled baseline. Its error at line 97 expects
∀ Y, Subsingleton (Abelian.Ext M Y d.succ), but receives
hd : HasProjectiveDimensionLE M d. The baseline therefore still exposes the
older Ext signature instead of the dimension bridge present in repository source.
This is a validation-tool/baseline failure, not a timeout or a failure of the
sandbox proofs. The tool cannot establish its required before/after counterfactual
until a green baseline publishes the current source bridge. No tool or shared
compiled output was changed; nothing was pushed.

Recompiled the saved scratch validation set in import order: the delivered bridge,
the adapted affine caller, both unchanged Ext callers, and their axiom probe all
compile cleanly. All four public theorems use only propext, Classical.choice,
Quot.sound. The prior independent second reading below is retained as historical
work, not authored by this retry worker.

## New nodes

None. Change record: coord/changes/projective-resolution-generic-bridge.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise is the unclaimed adapted module.

The original affine caller against the generic dependency fails at line 96:
Invalid argument name R for ModuleCat.projective_resolution_ext_degree; the
explicit .{u, u} also expects an object in Type u whereas M lies in ModuleCat,
a category in Type (u + 1). Removing just .{u, u} (R := R) resolves both errors.
The adapted caller compiles. All other lines and signatures remain identical.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository using diff. The item's
   only existing declaration changes its signature as explicitly recorded in
   projective-resolution-generic-bridge.md; specialization and unfolding the
   unchanged GlobalDimension predicate recovers the exact old statement.
   No target or definition changes. The affine caller's sole edit is the forced
   argument/universe removal, with its signature and visibility unchanged.
   Enumerated all three declaration users and all three DAG citers. Verdict: pass.
2. Compiled the item and all three callers against the delivered dependency in
   import order through lcompile.py. ExtAllDegrees and ExtCharacterization need
   no edits. The original affine call fails as above; the adapted call compiles.
   Scratch #print axioms for the item and all three public caller theorems shows
   only propext, Classical.choice, Quot.sound. No sorry, axiom, unsafe, opaque,
   implemented_by, extern, or postponed construction data occurs in the delivered
   modules. Verdict: pass.
3. No split-off theorem exists. Checked the generalized signature at n = 0,
   where self gives the bound, and for zero objects and arbitrary category
   universes. EnoughProjectives supplies the actual projective epimorphism.
   Read Mathlib Dimension, Resolution and Ext APIs: unbounded resolution
   existence and the dimension criteria do not themselves provide the support
   bound. Independent LeanFinder search for bounded resolution existence found
   only those unbounded APIs; Loogle query returned unknown identifier, so it
   supplies no positive search evidence. Local searches of Mathlib and both
   library roots found no shorter generic bounded-existence bridge. Verdict: pass.
4. Read [Stacks Tag 065R](https://stacks.math.columbia.edu/tag/065R), including
   its kernel induction and splicing step. The delivered proof reuses Mathlib's
   projectivity and dimension shifting, then explicitly augments Q. Exactness
   at zero comes from the epic Q augmentation, at one from the monic kernel
   inclusion, and above one from Q.exact_succ; projectivity and the bound shift
   term by term. Both private imports serve these proof steps; public imports
   supply signature notions. No unit-realizing node is bypassed: the item is
   absent from sk-thm-p1.realized, which remains untouched. All unused old
   proof dependencies/imports are listed above. Verdict: pass.
5. Compared the node proof steps and dependencies to the Lean construction.
   def-pc-ext remains used; the module-specific finite-global-dimension node
   is removed. The generic lean.statement and statement_change match the new
   signature, include all three citers, and retain the previous change history.
   No new node is needed. Restored status to the baseline split value because
   that field is maintainer-owned. Verdict: pass.

Second reading changed the affine caller's single bridge call, corrected stale
rename/forced-adaptation claims and net-hole accounting, restored node status,
and replaced the stale scratch validation with current compilation/axiom results.
The item's correct proof was retained.

## Second reading by Y3

1. Compared the delivered item and adapted affine module with the repository. The
   theorem statement change is exactly the one recorded in
   `coord/changes/projective-resolution-generic-bridge.md`; all existing caller
   signatures are unchanged. Verdict: pass.
2. Compiled the item and adapted caller with `lcompile.py`, and checked the source
   for forbidden declarations and unlisted `sorry`s. Both compile cleanly and the
   bridge contains no postponed data. Verdict: pass.
3. Checked the generalized statement at zero, successor, and zero-object cases;
   it is the explicit bounded-resolution/dimension equivalence and has no extra
   hypotheses beyond abelian category with enough projectives. No split-off
   statements or new nodes are present. Verdict: pass.
4. Checked the proof route against the unit record and source. The construction
   uses the projective kernel sequence, dimension shifting, and explicit
   augmentation; no unit-realizing route is bypassed. Removed imports and the
   removed finite-global-dimension dependency are recorded. Verdict: pass.
5. Compared the node's Lean statement, proof steps, dependencies, and proof origin
   with the implementation. The node status remains the maintainer-owned baseline,
   and the change record names all citers and the forced affine adaptation.
   Verdict: pass.

This second reading corrected the missing required report section and confirms
that the bridge proof and its one-line forced adaptation are deliverable.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise
Original against changed dependencies failed:
```
/tmp/forced-adaptation-8o8d6e28/lean/Sheaf/AlgebraicGeometry/AffinePolynomialResolutionOfStalkwise.lean:96:71: error: Invalid argument name `R` for function `ModuleCat.projective_resolution_ext_degree`

Hint: Perhaps you meant one of the following parameter names:
  • `C`: R̵C̲
  • `X`: R̵X̲
  • `n`: R̵n̲
/tmp/forced-adaptation-8o8d6e28/lean/Sheaf/AlgebraicGeometry/AffinePolynomialResolutionOfStalkwise.lean:96:80: error: Application type mismatch: The argument
  M
has type
  ModuleCat (MvPolynomial (Fin n) ↑Γ(Y, U))
of sort `Type (u + 1)` but is expected to have type
  ?m.258
of sort `Type u` in the application
  ModuleCat.projective_resolution_ext_degree M

(with the modules compiled into /tmp/forced-adaptation-8o8d6e28/.lbuild) [5.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
