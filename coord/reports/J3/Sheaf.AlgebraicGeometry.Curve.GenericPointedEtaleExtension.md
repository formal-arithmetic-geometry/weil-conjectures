## What changed

Replaced the single hole in `Sheaf.AlgebraicGeometry.Curve.GenericPointedEtaleExtension`
with a complete Lean proof of `AlgebraicGeometry.Scheme.exists_hom_generic_baseChangeNbhd`.
The signature and public imports are unchanged. Added proof imports of
`WeilConjectures.AlgebraicGeometry.FunctionFieldLimit` and
`WeilConjectures.AlgebraicGeometry.Sites.PointFunctions`; retained
`Sheaf.Paper.EtaleFiniteDataDescent`. The original namespace opening and options
are preserved; proof-only names are qualified locally.

The proof restricts the marked neighbourhood to an affine open, reindexes the already
proved function-field limit, applies the existing object-descent clause, and constructs
the marking and pointed morphism by explicit pullback equations. The index has universe u;
the unused finite-diagram universe of the descent theorem is explicitly instantiated at u.
Updated the item's node proof, proof_deps, and proof_origin to describe this route.
No definitions, public interfaces, or target statements changed; no adaptations are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_hom_generic_baseChangeNbhd`
(node `lem-sc-generic-pointed-etale-extension`), 1 of 1 original holes.
Added holes: none. Sorries left in the delivered module: none.

This is a proof from an existing stated dependency, not an axiom-free completion of its
entire dependency closure: `AlgebraicGeometry.etale_finite_data_descent`
(node `lem-weil-pbc-etale-finite-data-descent`) still has its pre-existing sorry.
Only its object-descent clause is used. Neither an arbitrary witness nor any data is
installed in a definition; all existential witnesses are eliminated within this theorem.

The module compiles cleanly with lcompile.py. The geometric marking rules out an empty
neighbourhood; restricting to the affine open uses the single point of Spec Omega.
The argument requires neither quasi-compactness nor separatedness of D or the original W.
The unit `sk-prop-cd-affine` has empty realized statement/step lists; this implements the
same generic-counit step below the unit and does not bypass any realized unit step.

## No longer needed

`lem-sc-integral-function-field-affine-fraction` is removed from this item's proof_deps:
there is no fraction-field or principal-localization calculation. The existing proved
function-field cone directly supplies the affine-neighbourhood limit. The node is a
Mathlib leaf with no Sheaf module, so this removes a planned dependency rather than an
entire library module from the target closure.

No original imports were removed. Both added imports are used; removing PointFunctions
was tested and fails at exists_pointSmallEtale_fiber_ofOpens. The data-descent and
function-field-limit imports supply the two main declarations used in the proof.
No other originally planned dependency is pruned. The morphism, equality, finite-diagram,
and covering clauses of etale_finite_data_descent are unused, but its module remains needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The original principal-localization route
was unnecessary: the source library already proves the needed generic-point limit over
all nonempty affine opens. The DAG now cites the existing general local-ring affine-limit
node for this mathematical fact, while the Lean proof uses the source library's proved
specialization `Scheme.isLimitFunctionFieldCone` rather than importing and reconstructing
a cone from `Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`.
This is an existing proved implementation, not a new hole or a duplicate node.

LeanFinder returned etale-locus and rational-map lemmas, with no direct pointed extension.
Loogle returned no matching declaration. The required msearch grep and local rg search
found FunctionFieldLimit and the closed-immersion pointed analogue. The closed-immersion
analogue does not apply to the generic inclusion; its pullback bookkeeping confirmed the
construction used here. The report does not claim all source declarations are axiom-free:
the delivery's dry-run probe is the check for the permitted trust boundary.

## Second reading by J3

1. The delivered module was diffed against the repository version. The theorem signature and all existing declarations are unchanged; only proof imports and the proof body differ. Verdict: pass.
2. The module compiles with `lcompile.py`, contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. The proof uses the existing descent theorem only as an imported dependency. Verdict: pass.
3. No statement was split off. The target theorem is the original statement, and the proof constructs all witnesses rather than choosing data from an undetermined existence result. Verdict: pass.
4. The route uses the source-library function-field limit, affine restriction, and the object clause of finite-data descent. The principal-localization dependency is pruned; imports used by the proof are retained. Verdict: pass.
5. The node proof and `proof_deps` describe the implemented route, and the affine unit remains identified in the node. Verdict: pass.

Changed during second reading: added this review record only; no Lean code or node statements required repair.
