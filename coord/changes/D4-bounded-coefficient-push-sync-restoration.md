# AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE

## Reason

Restore the assigned quarantined module after the 2026-10-20 upstream sync.
Its archive contains two top-level `by` blocks (lines 1195 and 1252) whose instance
headers were removed by extraction. These are old proofs of declarations which
now belong to the adopted upstream module. They are not declarations of this
Sheaf module. Remove the orphaned bodies and their unused private finite-free,
scalar-transport, and filtered-flatness machinery. Preserve the bounded-below
comparison theorem, its exact signature and its four DAG dependencies. The
upstream file and every upstream declaration remain unchanged.

Keep only the two imports required by the public signature public; the four
proof dependencies are private imports. The redundant upstream imports are
already supplied by the retained upstream Compatibility import, or were used
only by the discarded private machinery. No data definition remains in the
restored module.

The restored proof explicitly unfolds the named scalar-basis proposition before
eliminating its existential, avoiding expensive weak-head reduction by `obtain`.
It also supplies the canonical commutative-ring-object instance on every scheme
explicitly. The resulting file compiles in 20.9 seconds under the unchanged
60-second compile limit.

## Old

The public theorem signature, unchanged in the new version:

```lean
theorem isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE [IsProper f]
    (E : FiniteIntermediateField ℓ)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (N : ℤ) [M.IsGE N] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M)
```

The archived imports:

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Sheaf.CategoryTheory.CoefficientPushCopowerCriterion
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
public import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis
public import Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
```

## New

The theorem has exactly the signature above and retains the scalar-basis/mate/copower
proof. The restored imports are:

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.CoefficientPushCopowerCriterion
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis
import Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
```

## Users

The live downstream query with `--allow-missing` lists zero consumers because the
item and its consumers were quarantined together. The archive has four direct
importers, all listed below. No existing public declaration is removed or
renamed. Only the first consumer calls the bounded comparison; the other three
use upstream coefficient interfaces, still re-exported by the retained upstream
Compatibility import. None mentions the four proof-dependency APIs. The two
coefficient-heart consumers import additive-functor and biproduct APIs themselves;
the flat-calculus consumer imports its own finite-model proof API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | D4 (assigned rework) | Restore the bounded theorem unchanged; remove orphaned commands and obsolete private helpers. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | quarantined; not adapted | Its bounded theorem application retains precisely the same type. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | quarantined; not adapted | Upstream coefficient interfaces remain public; no bounded-theorem use. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | quarantined; not adapted | Upstream coefficient interfaces remain public; no bounded-theorem use. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | quarantined; not adapted | Upstream coefficient interfaces remain public; no bounded-theorem use. |

No forced adaptation is included. The quarantine originals remain untouched.
A scratch consumer imports only the restored module and applies the theorem
with its original exact bounded-below signature.

## Status

landed 20261020T152952-L-2856769 2026-10-20 (merge of deliver/D4/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
