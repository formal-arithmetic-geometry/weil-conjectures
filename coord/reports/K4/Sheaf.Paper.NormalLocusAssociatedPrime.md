## What changed

Proved `AlgebraicGeometry.exists_nonNormal_associatedPrime_le`, preserving its
signature and five original public imports. The proof follows the five planned
steps of Stacks Tag 0332, Cases I and II: Serre's criterion, the low-depth prime
witness, normality under localization, depth drop, and associated-prime descent.

Repair of the return at c8484bfe4: removed the duplicate private declarations
`AlgebraicGeometry.maximal_smul_top_ne_top`,
`AlgebraicGeometry.depth_le_of_ringEquiv`, and
`AlgebraicGeometry.depth_eq_of_ringEquiv`. Added proof-only
`import all Sheaf.RingTheory.FlatFiberLocalDepth`, which Lean's module system
supports for access to private declarations. Both depth transport steps now use
`RingHom.depth_eq_of_ringEquiv` from that module. Its two private supporting
lemmas are reused through that theorem rather than proved again. No other module,
existing signature, or visibility was changed.

Updated the node's first proof step to identify the existing depth transport
helper accurately. The flat fibre depth formula is not applied; no dependency on
its mathematical statement is claimed. The other proof dependencies and the
unit route remain those of the earlier delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_nonNormal_associatedPrime_le`
(node `lem-weil-pbc-normal-locus-associated-prime`).
No sorry remains in the delivered module, no holes were added, and none were split off.
The repaired module compiles cleanly through lcompile.py (about seven seconds).
A fresh scratch axiom probe reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for the main theorem; no `sorryAx` is present.

The proof uses the already closed Serre criterion, associated-prime depth bound,
depth-drop theorem, nonzerodivisor theorem, and normal-implies-regular theorem.
The auxiliary prime witnesses are used only inside proofs; no data definition
chooses a witness. The original checks for unit f, dimension zero, and infinite
height still apply, since the repair changes only depth transport reuse.

## No longer needed

The three duplicate private helpers named above are no longer needed locally.
No original imports, planned dependency nodes, or library modules were pruned.
The existing depth transport theorem is imported and used, so its module remains
needed. No new nodes or modules were added.
The second reading removed the redundant proof imports
`Mathlib.Algebra.Module.LocalizedModule.Submodule` and
`Mathlib.RingTheory.Localization.LocalizationLocalization`; their declarations
are supplied by the required associated-prime localization import.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery and second reading incorrectly treated private visibility
as preventing import reuse. Lean's `import all` grants access to those private
helpers in proof scope. This repairs all three duplicate-statement findings in
the return without modifying FlatFiberLocalDepth.

The original DAG omitted the closed normal-implies-regular tool needed in the
R1 case; the earlier delivery already records `lem-sc-normal-dim1-dvr` for it.
The local literature checkout is absent in this clone; the earlier delivery
read the cited Stacks tag online. No statement, definition, target, or unit route
has changed.

## Second reading by K4

1. **Unchanged interface: PASS.** Diffed the sole delivered module and node
   against the repository. The complete signature of
   `AlgebraicGeometry.exists_nonNormal_associatedPrime_le`, its existing
   docstring, and all five public imports are byte-for-byte unchanged. Only
   proofs, private proved helpers, proof-only imports and the node's proof
   fields differ. No definition, target, change record or adapted module is
   introduced.
2. **Kernel proof: PASS.** Independently compiled the module with lcompile.py.
   A fresh scratch copy prints the axioms of `depth_le_dim`,
   `normal_local_depth_bound`, `exists_nonNormal_lowDepth_prime_le`, and
   `exists_nonNormal_associatedPrime_le`: each uses only `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry, forbidden declaration,
   hollow definition or witness chosen into data occurs. Read the existing
   private `RingHom.depth_eq_of_ringEquiv` proof in FlatFiberLocalDepth:
   it transports regular sequences and maximal ideals in both directions;
   `import all` reuses it without using the flat-fibre theorem.
3. **Split statements: PASS (none).** There are no added holes or split-off
   modules/nodes. Read all three new private helper proofs. The low-depth
   witness requires only nonnormality, not the principal quotient, and is
   fully proved. Checked the unit-element case (normality then excludes hp),
   height zero (a local domain is a field, so R1 cannot fail there), and
   potentially infinite height (S2 failure still forces depth below two).
   The nonzero hypothesis on f supplies injectivity and regularity exactly
   where used; membership in q supplies the proper, nonzero quotient.
4. **Route and pruning: PASS after import cleanup.** Read Stacks Tag 0332,
   https://stacks.math.columbia.edu/tag/0332, Cases I and II, and compared
   the five proof steps with the Lean. Serre's criterion supplies the
   low-depth nonnormal witness; normality after localization forces f into
   q; depth drop and a singleton regular-sequence contradiction make the
   quotient's maximal ideal associated; localization descent contracts it
   back to q. Searched lean/Sheaf, lean/WeilConjectures and Mathlib with
   depth-zero, normality and associated-prime terminology: no replacement
   for the whole witness or duplicate of the new private helpers was found.
   The existing transport helper is correctly reused. Removal probes showed
   that AssociatedPrime.Localization is needed, whereas the two imports
   below are redundant; their combined removal compiles. Read
   dag/units/sk-thm-p1.json, including realized: no unit statement or step
   is bypassed, and no realized record is changed.
5. **DAG agreement: PASS.** Checked every proof dependency's statement and
   attachment against its use; proof_deps is exactly the union of uses.
   The added lem-sc-normal-dim1-dvr dependency records the source theorem
   IsRegularLocalRing.of_isIntegrallyClosed in its lean.declarations and
   closed audit, including the dimension-at-most-one version used here.
   The remaining original dependencies all occur in the argument, either
   through their proved library declarations or their Mathlib matches.
   proof_origin correctly identifies Stacks 0332. The private transport
   helper is described explicitly without claiming use of flat-fibre depth.

Changes by this second reader: removed redundant proof-only imports
`Mathlib.Algebra.Module.LocalizedModule.Submodule` and
`Mathlib.RingTheory.Localization.LocalizationLocalization`; their declarations
remain available through the required associated-prime localization import.
No original proof dependency, original import or library module was pruned.
No proof repair was necessary. Closed holes: the one original theorem named
above; added holes: none. This is a proof, not a decomposition.
