## What changed

Proved `AlgebraicGeometry.exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero`
without changing its signature or its existing docstring. Added proof imports of
`Sheaf.Paper.H1ClosedPointIdealQuotient` and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`.
The new module proves the geometric quotient-section construction in full, using the
actual inclusion `IdealSheafData.toModulesOfLE` and its categorical cokernel.
The item's local kernel argument proves quasi-coherence of the needed ideal module,
and its private helper proves surjectivity of global sections for a short exact
sequence with vanishing H1 of its first term.
The original DAG proof now names the quotient-section lemma and the actual
quasi-coherence ingredients. No definition, existing statement or visibility changed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero`
(node `lem-pqf-h1-closed-point-affine-basic-open`).

Also fully proved `AlgebraicGeometry.exists_closedPoint_ideal_quotient_section`
(node `lem-pqf-h1-closed-point-ideal-quotient`).
The new statement concerns the quotient section before any global lift is known to
exist, and needs neither the H1 hypothesis nor affineness of the chosen open.
The private surjectivity helper and the local quasi-coherence argument are proved.
No sorry remains in either delivered module and no
holes are added or split off. This closes an original hole rather than decomposing it.
The two delivered modules compile together with no warnings using lcompile.py.
`#print axioms` for both public theorems reports only `propext`, `Classical.choice`
and `Quot.sound`; neither proof has a transitive sorry dependency.

## No longer needed

No original imports, proof-dependency nodes or modules were pruned. The reduced-induced
closed-subscheme theorem and the full long exact sequence are both used.
The experimental proof import of
`WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance` was removed from the new
module: the proof uses the existing restriction machinery directly.
The proof does not need a separate identification of global quotient sections with
A/m, or an affine-local quotient comparison: pointwise residue vanishing and left
exactness on every open prove the property of all lifts directly. These were parts
of the old prose plan, not separate original dependency nodes.

## Where the brief, the DAG or earlier work was wrong

No statement error or unit-route departure was found. The recorded reduced-induced
closed-subscheme theorem's Lean conjunction does not itself include quasi-coherence
of the ideal module. This is supplied by the source library's proved
closed-immersion pushforward and quasi-coherent kernel theorems, without extra
geometric hypotheses. The quotient-section construction works for every open
neighbourhood, not just an affine one.
The local copy does not contain the source document coherent.tex; its recorded
Stacks Tag 01XF was read at https://stacks.math.columbia.edu/tag/01XF.

## New nodes

`lem-pqf-h1-closed-point-ideal-quotient`, in the item's chapter and unit, records the
fully proved canonical quotient-section theorem in
`lean/Sheaf/Paper/H1ClosedPointIdealQuotient.lean`. Its proof glues the image of 1 on U
with zero off x and identifies every lift's residue by exactness of evaluation.
No change record is needed: no existing statement or definition changed.

## Second reading by W2

1. Compared the existing Lean module and existing node with the repository by diff.
   The existing theorem signature and docstring are byte-identical; only proof code,
   private proof support, proof imports and the permitted node proof fields change.
   The second delivered module and its node are new. No change record is required.
2. Compiled both delivered modules in import order with lcompile.py: no errors or
   warnings. Scanned both for sorry and forbidden declarations/attributes: none.
   Scratch copies with #print axioms for both public theorems report exactly
   propext, Classical.choice and Quot.sound, with no sorryAx. No definition or
   arbitrary data from an unproved existence statement is introduced.
3. No statements are split off with sorry. Read the new proved quotient-section
   statement and its complete docstring proof against the actual cokernel and
   reduced vanishing ideals. It is strictly the geometric portion of the argument:
   it does not assume H1 vanishing or assert a global lift. Checked U = X,
   nonreduced schemes and the empty-scheme boundary (the point hypothesis excludes
   that boundary). The complement-of-x gluing also works when the overlap is empty.
   Independent leanfinder/loogle/msearch grep searches and rg of both library roots
   found no existing quotient-section theorem. RiemannRoch's
   exists_app_cokernel_π_ne_zero instead requires an invertible module, rational
   point and a dimension hypothesis and does not apply here.
4. Read the proof from the original hole down: quotient gluing, the full long exact
   sequence, residue vanishing and affine basic-open restriction implement the
   recorded route. All original proof dependencies are still used; the No longer
   needed list is complete. Public imports of the new module supply notions in
   its signature; its remaining imports and both added imports of the item are
   proof-only. The unit sk-prop-av-pqf-finite and its realized fields are unchanged;
   this lower-node refinement changes none of its stated steps.
5. Checked the new node's statement, verbatim Lean signature, source, searches,
   creation/blueprint fields and chapter/unit. Both nodes' proof steps and
   proof_deps match the Lean argument, including the existing pushforward and
   quasi-coherent-kernel theorems. Verdict: passes.

Changed: removed the duplicate private theorem isQuasicoherent_idealModule and
placed its argument directly at the needed ideal J. The existing
Scheme.Modules.isQuasicoherent_toModules in HilbertPolynomial has the same general
statement, but importing its module here would add 55 source modules, including
five open Cech-theory holes. The local argument uses the already imported proved
closed-immersion pushforward and quasi-coherent-kernel declarations instead,
introduces no duplicate declaration and preserves the smaller import closure.
Updated the earlier report accordingly; no mathematical statement changed.
