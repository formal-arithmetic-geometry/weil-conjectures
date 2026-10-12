# Sheaf.ConstructibleSheaf.EtalePullbackInternalHom private proof context

## Reason

The static interface checker treats additional `variable`, `open`, and local `attribute` commands in the private helper namespace as changes to what importers see. This record documents the additional proof context. All new declarations are private, all new imports are proof-only, and the original public theorem signature, public imports, and definitions are unchanged. No target meaning changes, and no target statement review needs reopening.

## Old

```lean
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
```

The public theorem has the following signature (unchanged):

```lean
theorem nonempty_etale_upperStar_ihom_iso (f : Y ⟶ X) [Etale f]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj ((ihom F).obj G) ≅
      (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G))
```

## New

The old context and theorem signature are retained. Before them is a private helper namespace:

```lean
namespace AlgebraicGeometry.EtaleInternalHomProof
universe u'
open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Opposite
open Scheme Etale
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [BraidedCategory A]
  {V X : Scheme.{u}} (g : V ⟶ X) (h : Etale g)
  [(X.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := A)).IsMonoidal]
attribute [local instance] Sheaf.monoidalCategory
```

Its private, fully proved lemmas and instances establish invertibility of the canonical internal-Hom comparison. The local declarations end before the original public theorem's namespace. There are no definition or statement replacements.

## Users

`tools/downstream.py Sheaf.ConstructibleSheaf.EtalePullbackInternalHom --uses nonempty_etale_upperStar_ihom_iso` found exactly these two textual users. All other downstream modules are unaffected for the same reason: the elaborated public theorem type remains unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.EtalePullbackInternalHom | J1 | Its only hole is closed; the public signature is unchanged. |
| Sheaf.ConstructibleSheaf.DualLocallyConstant | unchanged; no adaptation | Its existing application has exactly the same type. |

## Status

landed 20261012T112842-L-768832 2026-10-12 (merge of deliver/J1/Sheaf.ConstructibleSheaf.EtalePullbackInternalHom)
