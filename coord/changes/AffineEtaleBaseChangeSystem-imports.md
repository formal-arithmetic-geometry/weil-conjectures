# Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem imports
## Reason
The item only needs the affine étale site declarations in its public signature. The broader topological
import is retained only through proof dependencies; the unused Cat import is removed.
The public Sites.Pullback import is reduced to Sites.Continuous, which supplies the
continuous pushforward appearing in the signature. This makes the
module's public interface minimal while retaining all proof dependencies.
## Old
```lean
public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Pullback
```
## New
```lean
public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeGeometry
import Sheaf.AlgebraicGeometry.AffineEtaleCartesianSheafAdjunction
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
```
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit | E1 | Its own public import of FullAffineEtaleTopos continues to provide all prior declarations. |
## Status
landed 20261012T095901-L-316164 2026-10-12 (merge of deliver/G1/Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem)
