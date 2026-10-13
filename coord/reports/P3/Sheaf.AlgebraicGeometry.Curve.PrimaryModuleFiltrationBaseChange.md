## What changed

Completed the earlier sandbox reduction of
`AlgebraicGeometry.Scheme.primary_fixedField_pullback_iso` in
`Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationBaseChange`. Its existing signature,
visibility, and docstring are unchanged. The proof constructs the additive stalk isomorphism,
extends each subgroup automorphism to the algebraically closed overfield, proves that this
extension fixes the fixed field, obtains equivariance from the germ formulas, builds an
isomorphism of discrete continuous representations, and transports it through the unit of C.
The private helper `discreteRep_iso_of_additive_iso` is completely proved.

The strictly smaller geometric compatibility step is stated separately in the new module
`Sheaf.AlgebraicGeometry.Curve.PullbackStalkGermAction`. It assumes neither a Galois
representation nor a fixed-field equivalence and concludes only that a stalk comparison
commutes with endomorphisms specified on represented germs. Added its missing DAG node and
updated the item's proof, proof_deps, and proof_origin to describe the compiled argument.

Both modules compile with lcompile.py --all. The only remaining sorry is the entire proof of
the public compatibility theorem. No existing interface, definition, target, or other module
was changed. No object is defined by choosing an arbitrary witness of a sorry theorem.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.primary_fixedField_pullback_iso`
(node `lem-sc-primary-fixed-field-pullback-iso`). This is a decomposition, not a complete
sorry-free proof: its proof uses the newly stated compatibility theorem.

Added one hole:
`AlgebraicGeometry.Scheme.exists_etale_pullback_stalk_germ_action`
(node `lem-sc-pullback-stalk-germ-action`), in its own module. Its proof is exactly
`:= by sorry`, with the source and full argument in its docstring and node.

There are no sorries left in the item's module and no other holes added. Closed 1, added 1;
net hole reduction 0. The equivariant-representation helper is proved without sorry.

## No longer needed

Removed the direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` from the item, replacing it with
`Sheaf.AlgebraicGeometry.Curve.PullbackStalkGermAction`. The stalk module remains a plain proof
import of the new theorem's module and is still needed for the construction planned there.
The new module publicly imports only the geometric-point and pullback definitions required
by its statement.
The dependency `lemma-openclosed-stalk-upperstar` moved to that new node, so it is not pruned
from the overall proof closure. The Galois automorphism extension is used and retained.

No nodes or modules are globally pruned. The unit `sk-prop-cd-affine` has empty realized
statement and step lists; this local decomposition bypasses none of its steps.

## Where the brief, the DAG or earlier work was wrong

The original plan invokes a stalk isomorphism naturally in the sheaf, but its equivariance
under changes of geometric lift is an additional compatibility, not supplied by that
isomorphism's signature. This is the missing step isolated by the new node. The earlier
sandbox already contained a compiling reduction and its new statement, but lacked both
node records and the report, so it was not deliverable.

Checked the source: [Stacks Tag 03QW](https://stacks.math.columbia.edu/tag/03QW), equation
the project server, gives the change-of-lift action, and Remark 59.56.6 relates stalks to inverse
images. [Stacks Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1), Lemma 59.36.2(3), gives
the pullback stalk comparison. The general endomorphism formulation follows by the same
projection and colimit calculation; invertibility is not used. Mathlib search results and
the existing Point.Comap construction were inspected; no existing equivariance theorem
with this signature was found.

Edge cases of the new statement: for tau equal to the identity the germ hypotheses force
a and b to be identities, since every stalk element is a represented germ. For the zero
sheaf both stalks are zero and the square is automatic. For f the identity, take the
identity comparison (after transport by hst), and both specified germ actions agree.
In general tau fixes t because t=s followed by f; changing a lift therefore stays over the
same geometric point on both sites. Neither surjectivity of tau nor algebraicity of Omega
is required. These checks reveal no missing field or group hypotheses.

## New nodes

`lem-sc-pullback-stalk-germ-action` in
`dag/nodes/sec-curve-estimates/lem-sc-pullback-stalk-germ-action.json` records the compatibility
of the canonical pullback stalk comparison with changes of lifts. Its module is
`Sheaf.AlgebraicGeometry.Curve.PullbackStalkGermAction`, its source is Stacks Tags 03Q1 and
03QW, and its sole proof dependency is `lemma-openclosed-stalk-upperstar`. Its proof explains
how precomposition acts on represented germs and how the projection comparison and
adjunction mates preserve the square. The Lean statement is strictly part of the original
argument; all Galois extension, representation, and equivalence steps remain proved in the
item's module. No change record is needed because no existing interface was changed.

## Second reading by P3

1. Compared the delivered main module with the repository using diff and the declaration
   parser. The existing public theorem's signature, visibility, and docstring are byte for
   byte unchanged. Only its proof, a plain proof import, and a proved private helper were
   added or changed. No existing definition or target was changed. Verdict: pass.
2. Compiled both modules locally in import order using lcompile.py. No errors or warnings.
   Scanned both files: the sole sorry is the entire proof of
   `AlgebraicGeometry.Scheme.exists_etale_pullback_stalk_germ_action`; no forbidden
   declarations or hollow definitions. A scratch-copy `#print axioms` check found only
   propext, Classical.choice, Quot.sound for the private representation helper, and these
   plus sorryAx for the main theorem and the split compatibility theorem. The temporary
   audit file was removed. Verdict: pass as a decomposition, not a sorry-free proof.
3. Read the compatibility statement, docstring and new node. The equation has the correct
   direction: both paths go from the pullback stalk to the original stalk. The identity
   endomorphism forces both actions to be identity by represented-germ surjectivity; the
   zero sheaf and identity base-map cases also satisfy the square. Precomposition preserves
   lifts since tau fixes s and therefore t; the projection/pairing calculation commutes
   with precomposition without requiring tau to be invertible. This is strictly the
   geometric part of the argument, with no fixed-field equivalence or representation.
   Independently searched with leanfinder (naturality under geometric-point endomorphisms),
   loogle (sheafFiber and naturality), and rg on the library and Mathlib point API. Inspected
   `inverseImage_stalk_germ`, `pointSmallEtaleComapIso`, and the comap germ formulas. The
   existing germ theorem treats pulled-back sections and algebraically closed fields;
   it does not itself state the simultaneous change-of-lift square. No duplicate was found.
   Checked Stacks Tags 03Q1 and 03QW online because the cited TeX is absent on this machine.
   The source supports the comparison and represented-germ action; the endomorphism
   extension is the documented projection and colimit argument. Verdict: pass.
4. Read the proof from its conclusion upward: the unit of C reduces to an isomorphism of
   representations; the private helper reduces this to additive equivariance; extension
   of g and the supplied two germ formulas reduce it to the geometric square. No simpler
   ready-made theorem was found. The split square requires substantial point/adjunction
   bookkeeping, rather than a few-minute closure. The old direct stalk dependency is
   explicitly accounted for under No longer needed and retained below the new node;
   the other old dependency is used. No global pruning is claimed. The unit's realized
   statement and step lists are empty, and its route is not bypassed. Verdict: pass.
5. Compared both node files with the Lean declarations and the old node. Existing-node
   changes are restricted to proof, proof_deps and proof_origin; the new node has its
   source, word proof, searches, provenance, blueprint, unit, chapter and verbatim Lean
   signature. Its proof_deps match the planned stalk construction, and the main node
   records the geometric compatibility and automorphism extension actually invoked.
   Verdict: pass.

Changed only import visibility in the new module: replaced the public Stalk import with
public Mathlib geometric-point and upper/lower-star definition imports, retaining Stalk
as a plain proof import. Updated No longer needed accordingly and added this reading.
No proof or existing statement needed repair. Closed 1 original hole and added 1 strictly
smaller hole, net 0; no globally pruned modules.
