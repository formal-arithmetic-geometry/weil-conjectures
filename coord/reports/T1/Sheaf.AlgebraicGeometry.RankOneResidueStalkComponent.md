## What changed

Proved `AlgebraicGeometry.isIso_localized_stalk_component_of_residue_homology`
without changing its signature. Constructed source and target linear stalk frames,
used the split residue coefficient comparison, and proved that the resulting scalar
is a unit and hence the stalk component is bijective. The unit-stalk construction
is local to the proof: the corresponding existing library helpers are private.
The proof-only import of `FlatComplexDerivedPullback` moved to the new comparison
module; added proof-only imports of `ResidueHomologyRankOneCoefficient` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.

## Proved and sorry left

Closed one hole, by declaration name:
`AlgebraicGeometry.isIso_localized_stalk_component_of_residue_homology`
(node `lem-sc-rank-one-residue-stalk-component`).
Added one hole, by declaration name:
`AlgebraicGeometry.residue_ne_zero_rankOne_stalk_coefficient`
(node `lem-sc-residue-homology-rank-one-coefficient`) in the new module
`Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient`.
This is a decomposition, with net zero holes closed. The item's module has no
remaining `sorry`; the comparison module has exactly the one named theorem above.
No definitions or data are added. The parent's axiom audit is exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` from the unresolved comparison.

## No longer needed

Removed the direct proof-only import
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` from the parent. It remains
imported by the new comparison module. The parent's old proof dependencies
`lem-pc-flat-complex-derived-pullback` and
`lem-pc-ringed-spaces-derived-pullback-composition` are now dependencies of the
comparison node, rather than direct dependencies of the parent. Neither node nor
module is pruned from the import closure. No unit route is removed.
The duplicate top-level unit-stalk helper from the earlier returned attempt is
absent; its checked construction remains local to the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier returned attempt duplicated the private unit-stalk theorem in
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitStalkKernel`. Since that declaration
is private, this proof uses a local construction instead of adding a duplicate
library declaration. The previous report also omitted the decomposition counts,
misdescribed the new node as absent, and did not distinguish moved dependencies
from pruning. These reporting defects are corrected here.

## New nodes

`lem-sc-residue-homology-rank-one-coefficient` isolates the derived comparison
and the injection of connective degree-zero homology into the degree-zero residue
term. Its theorem is in `Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient`.
The source, full informal proof, searches, provenance, and verbatim Lean signature
are in its node and docstring. No change records are needed: no existing statement,
definition, visibility, or public import changes.

## Second reading by T1

1. Compared the parent with the repository file. The existing theorem signature,
   docstring, universe binders, hypotheses and conclusion are byte for byte unchanged.
   Changes are its proof and proof-only imports. The other Lean file is new; no
   existing public interface is altered. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py --all`. Both compile
   successfully. Searched for forbidden declarations and holes: exactly one `sorry`,
   the named comparison theorem; no `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`, and no definition with missing data. Appended an axiom probe
   temporarily to the parent: only the permitted three axioms and `sorryAx`.
   Restored the source after the probe. All frames used in the parent are constructed
   from actual isomorphisms and colimit maps, not arbitrary unproved witnesses.
   Verdict: pass as a decomposition, not an axiom-free proof of the target.
3. Read the new statement and its docstring against its node. Its explicit linear
   frames replace the sheaf rank-one hypothesis at the stalk. Flat bounded terms
   compute the residue pullback; the representing equality gives an invertible
   residue H^0 arrow. With no negative terms, H^0 injects into the degree-zero term,
   so the image of the nonzero source generator is nonzero. Changing frames only
   multiplies its coordinate by units. Tested the field case with P concentrated
   in degree zero, and a two-term connective rank-one complex: an invertible H^0
   arrow forces the generator's nonzero degree-zero image. Zero maps fail ha;
   empty opens and zero stalk rings are excluded by the scheme point. Noncanonical
   c and e do not affect the argument because their residue maps are isomorphisms.
   Ran fresh LeanFinder and Loogle queries and searched both Lean roots. Read the
   flat-complex and composition declarations, KFlatStalkResidueCohomology and
   StalkFreeResidueCohomologyComparison. The latter give objectwise equivalences,
   not the morphism comparison needed here. No direct replacement or quick proof
   was found. The split is the residue part of the argument; construction of frames
   and the unit/bijectivity argument remain real proofs in the parent. Verdict: pass.
4. Checked the top-down reduction, the local unit-stalk construction, and the scalar
   calculation. Loogle confirms `IsLocalRing.residue_ne_zero_iff_isUnit`; linearity
   gives g(r)=r*g(1), and multiplication by a unit is bijective. Proof-only imports
   remain plain imports. The removed direct dependency import is retained where
   its unresolved comparison needs it. No closure module is claimed pruned.
   Read `dag/units/sk-prop-av-cube.json`: its statement and step are untouched;
   its existing `realized` arrays are empty and this below-unit reduction does
   not modify them. Verdict: pass.
5. Compared the parent node with the repository node: only proof, proof_deps and
   proof_origin changed. Its three recorded steps follow the Lean proof. The new
   node's statement matches its theorem; its proof dependencies are imported in
   the comparison module. Its source, searches, created/item, blueprint, chapter,
   unit and Lean record are present. Verdict: pass.

Second reading changed report completeness and pruning/count descriptions, recorded
an additional actual search, and removed a blank line within the tactic proof that triggered the delivery linter. No mathematical proof
or statement changes were required.
