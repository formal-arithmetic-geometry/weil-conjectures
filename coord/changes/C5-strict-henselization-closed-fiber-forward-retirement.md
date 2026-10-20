# AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq

## Reason

The live stage-3 queue assigns retirement of the zero-hole duplicate
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward. The explicit row in
coord/retire-items.tsv is authorized by the human's hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The upstream theorem uses the full
strictLocalization model; the retained consumer uses strictHenselizationScheme,
the chosen small representative colimit. These are canonically isomorphic but
are not definitionally the same scheme.

A direct import replacement in the consumer was tested and fails at its imports:

```
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
failed, environment already contains
'AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq'
from Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
```

The consumer's backward proof imports Sheaf.Paper.StrictHenselizationFunctoriality,
which also exports the small-model wrapper. The new comparison module publicly
imports only the existing small-model construction and canonical comparison API,
and privately imports the upstream forward theorem. Its proved compatibility
corollary transports that theorem without exporting the competing compatibility
API to the consumer. The copied affine-chart/ideal-containment proof is removed.
No source-library file, target statement or mathematical hypothesis is changed.

## Old

The withdrawn Sheaf module exported the following signature:

```lean
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictHenselizationStructuralMap s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A
```

Its imports were:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
```

It contained a private proof of the small-to-full structural-map comparison and
then repeated the affine-chart argument of the official forward theorem.

## New

The existing official declaration is unchanged:

```lean
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictLocalizationToBase s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A
```

The original forward node now points to that official module and exact signature.
The new Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison proves:

```lean
theorem smallStrictHenselizationColimitIso_toBase
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (smallStrictHenselizationColimitIso s).inv ≫ strictLocalizationToBase s =
      strictHenselizationStructuralMap s
```

and the small-model compatibility corollary:

```lean
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_compat
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictHenselizationStructuralMap s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A
```

The first proof applies the inverse coprojection formula of the canonical final
colimit isomorphism and the defining equations of the two structural maps. The
second composes e with Spec of the inverse comparison and applies the official
forward theorem. Both proofs are complete. The sole direct consumer replaces its
private import of the withdrawn module by the comparison module and changes its
one forward application to the compatibility corollary. Both consumer declaration
signatures, attributes, visibility and the backward proof stay identical.

The item file is withdrawn using deleted.txt; its landing representation is an
empty module. No mathematical node is deleted. The singleton-fibre node now cites
the new comparison node, which cites the original node attached upstream; all
original chart and unit-route dependencies remain represented.

## Users

The table includes all three modules listed by tools/downstream.py with --uses,
the assigned module, and the new compatibility module. Claim files were checked;
the sole adapted existing consumer was unclaimed. No forced edit of a held
module is included.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward | C5 | Withdrawn; original node attaches to the proved official twin. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison | new, C5 | Proves the canonical structure-map comparison and transports the official theorem. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber | unclaimed | One private import and one forward application change; all signatures preserved; compiled. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Transitive consumer; unchanged source compiled against the delivered overlay. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Transitive consumer; unchanged source compiled against the delivered overlay. |

The official forward theorem and every other WeilConjectures file remain verbatim.
The old Sheaf forward name has no other named call site, including in quarantine.
The node's upstream attachment preserves every DAG parent and the blueprint unit
route. The targets retain their exact statements and definitions; no statement
re-review is reopened.

## Status

landed 20261020T221106-L-4142787 2026-10-20 (merge of deliver/C5/Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward)
