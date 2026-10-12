## What changed
Replaced the first worker's epimorphic-quotient restatement with the actual subobject/cokernel
argument in `constructible_quot_part`. Its signature is unchanged; its proof docstring now describes the integral route.
The proof converts to canonical integral modules, maps the short exact sequence along the
coefficient equivalence, obtains constructibility of the first term by the Noetherian
subobject theorem, applies cokernel constructibility, transports along the cokernel
isomorphism, and converts the torsion quotient back to the set-valued predicate.
All added imports are proof-only. The target node now records this route.

## Proved and sorry left
`AlgebraicGeometry.CurveCoefficientPair.constructible_quot_part`: proof written using
existing library declarations. No new `sorry` or split theorem remains in this delivery.
The integral comparison remains open in its existing module; it is not restated here.

## No longer needed
The old proof dependency `lem-weil-pbc-curve-constructible-sub-quotient` is removed from
this node: it is the parent theorem, whose proof already imports this item.
The proposed new node `lem-weil-pbc-curve-constructible-quot-part-aux` is deleted.
Removed redundant proof imports: `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`,
`Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian`,
`Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree`,
`Sheaf.AlgebraicGeometry.CurveCoefficientPair`, `Sheaf.AlgebraicGeometry.EtaleSheaves`,
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
`Sheaf.Paper.InverseImageStalkGerm`, `WeilConjectures.ConstructibleSheaf.Defs`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
These redundant imports are not a claim that their modules are globally unreachable.
The unit `sk-thm-p1` realized statements and steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong
The first worker's new epimorphic quotient lemma retained the whole item argument;
its proof dependency pointed back to this item and its docstring did not give the
required complete proof. It was not an acceptable split. The existing item node also
pointed to its parent theorem, introducing a dependency cycle.
The integral coefficient comparison and the general Noetherian module subobject theorem
already give a shorter route, with no new statements. The cokernel declaration attached
to `thm-constructible-serre` is general in the coefficient ring; this proof uses that
actual Lean statement over ULift Z. The blueprint unit route is preserved.
Loogle confirmed `ShortExact.gIsCokernel`; Mathlib grep found no direct constructibility
quotient theorem. Searches of the project found the integral comparison and the
subobject theorem, and the upstream library supplies the cokernel and isomorphism steps.

The dependency audit also found pre-existing cycles between
`lem-weil-pbc-sheaf-algebraic-structures-objects` and its abelian/ring component nodes
below the integral comparison. They lie outside this item and are not modified.
The cycle through this item's parent is repaired.

## Second reading by J1
1. Compared the delivered module against the repository with `diff` and a byte comparison
   of the target signature: exactly unchanged. No existing definition changed and no new
   public declaration remains. The proof docstring is corrected to the actual route.
   Verdict: pass.
2. Compiled the full proof locally with `lcompile.py`: no errors or warnings. No `sorry`,
   hollow definition, axiom, unsafe, opaque, implemented_by, or extern occurs in the module.
   `#print axioms AlgebraicGeometry.CurveCoefficientPair.constructible_quot_part` in a
   scratch copy reports exactly propext, Classical.choice, Quot.sound and sorryAx.
   The latter comes from existing open library dependencies, including the integral
   comparison; this does not claim the target's entire axiom closure is finished.
   Verdict: pass.
3. Removed the split epimorphic-quotient restatement and its circular, unsearched node.
   No split statement remains to review or search. The existing integral comparison
   retains torsion, needed to equate finite set stalks with finite integral modules.
   The subobject and cokernel steps apply also to zero terms and the empty curve;
   no nonempty, positive-rank or nonzero hypothesis is introduced. Verdict: pass.
4. Checked the proof from the target downward against the imported declarations.
   The integral comparison avoids a new finite-annihilator lemma. The first term is
   constructible by the general Noetherian subobject theorem; cokernel constructibility
   and the short-exact cokernel isomorphism finish the argument. Imports are minimal
   for this route and all removed imports and the sole removed old proof dependency
   are listed above. The unit's realized route is unchanged. Verdict: pass.
5. The target node now records exactly the Noetherianity, integral comparison,
   subobject, cokernel/isomorphism, and reverse-comparison steps used by Lean.
   Its proof_deps are the union of those steps, and proof_origin records this
   implementation of the source's subobject/cokernel route. No new node remains.
   Existing unrelated downstream DAG cycles are reported above. Verdict: pass.

Changed during second reading: replaced the restatement with the actual proof,
removed its proposed auxiliary node, pruned redundant imports, repaired the item
node's parent dependency cycle, and corrected the proof docstring and report.
