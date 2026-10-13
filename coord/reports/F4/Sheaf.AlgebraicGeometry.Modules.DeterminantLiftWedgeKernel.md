## What changed

Replaced the sole hole in
`Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel` with a proof from
`exteriorSheaf_wedgeMap_exists` and `determinant_wedge_quotient_factor`.
Added their two modules as ordinary proof imports. All existing signatures,
visibility, public imports and docstrings stay unchanged.

The first theorem supplies the wedge map and its required formula. The second
factors that map through the given quotient. Associativity, `kernel.condition`
and `zero_comp` then prove kernel annihilation. Updated the item's node to record
this route. No data definition or arbitrary witness selection was added: the two
existential witnesses are eliminated only inside a theorem proof.

Searches: LeanFinder for exterior-power multiplication and concatenated wedges,
Loogle for `exteriorPower.ιMulti`, and the logged grep search for exterior-power
maps and wedge kernels found ordinary-module infrastructure. Repository `rg`
found the existing sheaf wedge construction and quotient factorization. The
import-direction checker accepted both imports, with no cycle.

## Proved and sorry left

Closed the one local hole:
`AlgebraicGeometry.Scheme.Modules.determinant_liftWedge_kernel_exists`
(node `new-determinant-lift-wedge-kernel`). Added zero holes; no `sorry` remains
in the delivered module. This is a proof from existing statements, not a claim
that the imported theory is already free of holes.

The existing imported theorems
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists`
(`lem-sc-exterior-sheaf-wedge-map`) and
`AlgebraicGeometry.Scheme.Modules.determinant_wedge_quotient_factor`
(`lem-sc-determinant-wedge-quotient-factor`) retain their pre-existing holes in
the repository; this delivery does not modify them.

Both statements apply at all natural-number degrees, including either zero
degree, and to empty schemes and zero rings. The proof introduces no positive
rank or nonempty-open assumption. The unit `sk-thm-picard-rr` has no realized
nodes in its statement or step arrays, and this reuse preserves its determinant
argument.

## No longer needed

No existing imports were removed. No module is claimed to leave the targets'
import closure.

The direct proof no longer needs
`def-sc-sheaf-exterior-power`, `lem-sc-exterior-tensor-lift-hom-ext`
(`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt`), or
`lem-weil-pbc-exterior-power-free-basis` as separate proof dependencies of this
node. The exterior-sheaf definition remains a statement dependency and public
import; the basis theory remains needed inside the quotient-factorization node.
These are changes to this node's direct route, not global pruning claims.

## Where the brief, the DAG or earlier work was wrong

The recorded plan duplicated two already stated parts of the determinant
argument. Their existing modules can be reused without an import cycle, so the
sectionwise construction and rank-bound kernel argument need not be restated
here. No statement error or interface change was found.

The first local compile was blocked by a missing compiled artifact for
`ExteriorSheafWedgeMapExists`, despite the source module being present. The
brief requires waiting for the next green compiled snapshot rather than
redeclaring such a theorem. The next refresh supplied both imported artifacts;
`lcompile.py` then compiled the delivered module cleanly in 3.3 seconds.

## Second reading by F4

1. Compared the delivered Lean module with the repository using `diff -u` and
   checked the theorem signature byte for byte. Verdict: unchanged statement,
   hypotheses, visibility, definitions and existing public imports. The only
   Lean changes are two ordinary proof imports and the replacement proof.
   No change record or forced adaptation is needed.
2. Independently compiled the module with `lcompile.py`: clean, with no warnings.
   A scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.determinant_liftWedge_kernel_exists` reports
   exactly `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. The last is
   inherited from the two existing imported open theorems, not a new local hole.
   No forbidden declarations, proof bypasses or data definitions occur. Both
   existential witnesses are eliminated within the proposition's proof.
3. No statement or hole is split off by this delivery. Read both imported
   theorem signatures, docstrings and nodes: wedge construction is independent
   of exactness; factorization uses exactly the given exactness, rank and
   generator formulas. Their claims cover degree zero, rank zero, zero rings
   and the empty scheme. These are existing components, not a new restatement
   of this item. Neither imported construction can be closed in a few minutes.
4. Read the proof from its conclusion backward: substituting the factorization
   reduces kernel annihilation to associativity, `kernel.condition` and
   `zero_comp`. An independent Loogle search for the kernel inclusion and
   condition confirmed the categorical route; repository searches for lift
   wedges and determinant maps found no shorter proved sheaf-level result.
   Both new imports are ordinary imports and used explicitly. Existing public
   imports support the signature, including the abelian instance for kernels.
   `No longer needed` lists all three removed direct proof dependencies. No
   global module pruning is claimed. Read `sk-thm-picard-rr` and its `realized`
   arrays: the determinant-additivity argument is preserved, without replacing
   a unit step or changing the unit record.
5. Compared the node JSON with the repository: only `proof`, `proof_deps` and
   `proof_origin` changed. Its three proof steps match the two theorem
   applications and the categorical rewrite. The dependency list is exactly
   the union of the steps' uses. There are no new nodes to audit.

Second reading changed only this report, adding the independent review and
explicit axiom result. The Lean proof and node changes were accepted unchanged.
One existing local hole is closed and zero holes are added; full axiom closure
still awaits the existing imported theorems. This is not a claim about the
ledger's global net or globally pruned modules.
