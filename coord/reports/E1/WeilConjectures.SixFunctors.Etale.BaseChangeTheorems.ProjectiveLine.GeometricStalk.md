## What changed

Replaced the target's sole direct sorry with an application of
`AlgebraicGeometry.Etale.geometricStalk_projectiveLine_of_strictLocal`, supplying its
strict-local hypothesis by the existing
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`.
Added the proof-only import `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction`.
The target signature, all other declarations, and all existing public imports are unchanged.
Updated the geometric-stalk node to match this route.

This is a partial delivery: the strict-local comparison remains its existing independent
item, while the arbitrary-base reduction becomes one new independent item. It does not
claim to close a target's axiom closure. The reduction is conditional on the strict-local
comparison, rather than restating the target as an unconditional new theorem.

## Proved and sorry left

The original declaration
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`
(lemma-weil-pbc-p1-exchange-geometric-stalk) now has a proof with no direct sorry. The two
later theorems and the auxiliary lemma keep their existing proofs.

The delivery's only direct sorry is
`AlgebraicGeometry.Etale.geometricStalk_projectiveLine_of_strictLocal`
(lem-weil-pbc-p1-geometric-stalk-strict-local-reduction), in its own new module. Its whole
proof is `:= by sorry`; its docstring and node give the strict-henselization reduction,
exchange compatibility on neighbourhood representatives, and purely inseparable closed-fibre
transport. The existing strict-local theorem is still unproved in the library and is used
as a premise-provider, not proved or modified here.

Local compilation checks the two modules together in import order, with no warnings.
The dry run also checks the new module on the server and runs the axiom preflight. New-statement edge
cases were checked mathematically: q=0, the zero sheaf, an identity base map, a nontrivial
purely inseparable algebraic residue extension, and an arbitrary representative of the
cartesian upper-left object. None requires a hypothesis missing from the signature.

## No longer needed

None globally. No existing imports were removed. The target's former direct proof
dependencies are now used inside the reduction, or through the existing strict-local
comparison; they are not claimed pruned. In particular the strictly henselian comparison,
strict-local exchange, stalk formula, and curve-invariance unit steps are retained.
No unused proof-only import was added.

## Where the brief, the DAG or earlier work was wrong

The original docstring correctly warns that the formal target only asks for some additive
equivalences, while the blueprint specifies canonical maps. This delivery preserves that
signature and does not replace the canonical argument by bijectivity or by proper base
change. The reduction's docstring explicitly requires the canonical stalk restrictions.
The existing strict-local exchange statement supplies the closed-fibre comparison and must
also eventually be filled through its canonical construction, as its existing docstring says.

The available strict-henselization stalk formula is stated for abelian coefficients and
algebraically closed point fields, not directly for this module-coefficient target. The
new obligation includes this coefficient and geometric-point transport; it is not asserted
that the current stalk formula alone closes it. Integral and separably closed does not
mean separable algebraic: purely inseparable extensions must be handled by topological
invariance. For the coefficient transport, the new node uses
`lem-sc-injective-module-abelian-acyclic-zariski` as a generic ringed-site tool: its Lean
signature accommodates the site hom/coefficient universe u+1. The scheme-specific
`lem-weil-pbc-injective-module-abelian-acyclic` records only a ring R:Type u and so cannot
be applied directly to arbitrary Lambda:Type (u+1). The generic tool belongs to another
unit but does not replace any unit route: it only implements the change of coefficient
category needed for the stalk formula. The maintainer should record this generic tool use
if the route checker requests it. Stacks sites-cohomology.tex, Tag 03FD, was read for this
comparison. No statement was marked false or changed.

The Stacks proof was read in the available local copy of etale-cohomology.tex, at
`theorem-proper-base-change`, paragraphs 3--4. LeanSearch returned an internal-server error;
LeanFinder, Loogle and repository searches were available and found no reduction lemma.

## New nodes

`lem-weil-pbc-p1-geometric-stalk-strict-local-reduction` states the conditional passage from
strict-local exchange to arbitrary-base geometric exchange. It is in the same chapter and
unit as the target, preserves the unit's strictly henselian route, and carries the sole new
sorry in `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction`. Its statement
quantifies the full existing strict-local premise; the target discharges that premise by
its recorded declaration. No change record is needed: no existing definition or statement
changed, and the new import in the target is proof-only.

## Second reading by E1

1. Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and one proof-only import changed. The new reduction module and node are additional declarations, with no definition or target change.

2. Compiled both modules together with `lcompile.py --all`; compilation succeeds without warnings. The target's former direct `sorry` is closed. The only remaining direct `sorry` is the named strict-local reduction theorem, which has its own docstring and split node. No forbidden declarations or hollow definitions occur.

3. Checked the split statement against the strict-local premise and arbitrary-base conclusion, including degree zero, zero sheaves, identity maps, and purely inseparable residue extensions. It is a conditional reduction with the full target conclusion and no weakened hypotheses; its node, source, proof steps, and Lean declaration agree. Repository and Mathlib searches found no existing equivalent theorem.

4. The proof follows the unit route through the strict-local exchange and invokes the reduction only below the unit level. The target proof uses precisely the reduction and strict-local premise provider. No unused proof-only import or removable dependency was found; `No longer needed` remains none.

5. The DAG target node records the exact proof and dependencies, and the new split node records its theorem, source, proof origin, Lean module and declaration. The unit route and realized declarations are retained.

I changed only this report section; no Lean or DAG repairs were needed in the second reading.
