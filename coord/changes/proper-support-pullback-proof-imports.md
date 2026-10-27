# Proper-support pullback proof imports

## Reason

The proof works directly with ModuleCat inverse images and their stalk isomorphism.
Remove unused proof imports and add the closed-support and isomorphism-transport APIs.
All added declarations are proved private lemmas. Existing public declaration signatures,
definitions, attributes, docstrings and the public import remain unchanged. The added
`open Scheme` only shortens names within this file. The local elaboration option
`backward.isDefEq.respectTransparency false` helps match existing semireducible etale
base-change expressions; it changes no declaration or kernel type. After proving the projection equations, both
Cartesian constructions are marked locally irreducible, so unification uses those
equations instead of unfolding the full nested pullback construction. This attribute is
local to the file and has no effect on importers.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import Sheaf.AlgebraicGeometry.ClosedProperSupportLocality
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleSectionProperSupport
import Sheaf.AlgebraicGeometry.ClosedProperSupportLocality
import Sheaf.AlgebraicGeometry.ProperSupportSectionLocality
import Sheaf.AlgebraicGeometry.EtaleModuleSectionClosedSupport
```

After the existing definitions, the proof helpers additionally use:

```lean
open Scheme
set_option backward.isDefEq.respectTransparency false

-- After the private projection equations:
attribute [local irreducible] properSupportBaseChangeProjection properSupportBaseChangeEtaleMap
```

## Users

The public interface is unchanged. No consumer is adapted; all existing public definitions
retain their bodies and signatures. The direct importers in the shared snapshot are below.
The full transitive import closure receives the same public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | Y7 | unchanged; no adaptation |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | unclaimed | unchanged |

## Status

landed 20261025T095118-L-3295445 2026-10-25 (merge of deliver/E5/Sheaf.SecSmoothPurity.ProperSupportPullbackSectionMap)
