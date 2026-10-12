## What changed

Proved `AlgebraicGeometry.Scheme.nonempty_etaleDualRestrictionIso` in
`Sheaf.ConstructibleSheaf.EtaleDualRestriction` by specializing the existing general
étale internal Hom comparison to the coefficient unit, then composing with `mapIso`
of the inverse monoidal unit comparison. Added proof-only imports of
`Sheaf.ConstructibleSheaf.EtalePullbackInternalHom` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`. Updated the existing
node's proof, proof_deps, and proof_origin to match this route. No signature changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.nonempty_etaleDualRestrictionIso`
(`lem-weil-pbc-etale-dual-restriction`). Its Lean proof is complete; no sorry remains
in the item and no new hole was added. It uses the existing sorry theorem
`AlgebraicGeometry.Scheme.nonempty_etale_upperStar_ihom_iso`
(`lem-weil-pbc-etale-pullback-internal-hom`), which remains the next proof obligation.
This is a proof from an existing stated dependency, not a proof of that dependency.
The unit comparison is already proved upstream. The combined proof compiled locally.

## No longer needed

None: the three original public imports support the statement's categories and
closed monoidal structures, and both new proof imports are used. No named nodes or
modules of the original plan are pruned: that plan had no named proof dependencies.
The slice-site and section calculations are supplied by the existing general
comparison rather than duplicated here. No blueprint unit or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node had three prose steps but no named proof dependencies. The library
already states their internal Hom conclusion as
`lem-weil-pbc-etale-pullback-internal-hom`, so a new split is unnecessary. The local
compiled library initially lacked that dependency's object file. An unchanged sandbox
copy was compiled solely to check the proof and then removed from the delivery; its
compiled object remains in the sandbox overlay. No dependency declaration was changed.

## Second reading by G1

1. **Unchanged interface — pass.** Read the entire module and compared it with
   the repository using `diff -u`. The only Lean differences are the two plain
   proof imports and the replacement of the original `sorry`. The existing
   declaration signature and docstring are byte for byte unchanged. No definition,
   target, public import or other module was changed; no change record is needed.
2. **Proof and axioms — pass with the reported open dependency.** Recompiled the
   delivered module through `lcompile.py`: no errors or warnings. Scanned the file:
   no `sorry`, axiom, unsafe, opaque, extern or implemented_by. Compiled a scratch
   copy with `#print axioms`: `nonempty_etaleDualRestrictionIso` uses only
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the existing general
   internal Hom comparison accounts for the open proof obligation. The monoidal
   upperStar instance uses only the three permitted standard axioms. The witness
   of the existing Nonempty theorem is eliminated inside a proof of Nonempty;
   no data definition chooses an arbitrary unproved witness.
3. **Split statements — pass (none added).** There are no new declarations, new
   nodes or split-off holes. Read the existing general comparison and its node:
   it applies to arbitrary module sheaves and specializes to the unit without
   an extra finiteness or noetherian assumption. Empty schemes, the zero ring,
   zero sheaves and identity etale maps cause no extra hypotheses. Independent
   LeanFinder search for inverse image preserving internal Hom of module sheaves,
   Loogle search for the comparison API, and `rg` over both Lean roots found no
   shorter exact theorem. Ringed-site modules and derived/pro-etale comparisons
   concern different categories; the finite locally constant dual theorem is
   weaker than this item's arbitrary-sheaf statement.
4. **Route and pruning — pass.** The existing general comparison followed by
   `ihom.mapIso` of the inverse unit comparison is a direct specialization and
   composition, rather than a new restatement hole. All three public imports
   supply the statement's sheaf/pullback and closed monoidal structures; both
   added imports are needed only by the proof and are correctly plain imports.
   The old `proof_deps` was empty, so `No longer needed: None` is complete.
   Read `dag/units/sk-thm-p1.json`, including `realized`: this local supporting
   lemma is not a realization of a unit statement or step, and no fixed unit
   route is bypassed.
5. **DAG consistency — pass.** Compared the delivered node with the repository:
   only `proof`, `proof_deps` and `proof_origin` differ. The first step names the
   existing general comparison; the second records the proved monoidal unit
   transport and isomorphism composition. Their dependency union agrees with
   `proof_deps`, and the declaration and unchanged statement agree with Lean.
   New-node field checks do not apply because there are no new nodes.

Second reading changed only this report, adding the independent review and axiom
results. The proof and node were already correct and were kept as written.
