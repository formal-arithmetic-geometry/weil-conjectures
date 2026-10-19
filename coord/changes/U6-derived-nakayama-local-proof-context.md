# AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama

## Reason

The stage-3 preflight classifies changed top-level `open` and `attribute` commands
conservatively as interface changes. This record documents the local proof context
needed to prove the existing theorem in `Sheaf.Paper.DerivedNakayama`. Keeping the
large derived-functor constructions irreducible prevents unnecessary unfolding;
the proof instead uses their existing comparison API. The HomologicalComplex
namespace supplies the two-term complex construction.

## Old

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
```

There were no local transparency attributes. The public theorem
`reduction_and_derived_nakayama` had proof `by sorry`.

## New

The module additionally opens HomologicalComplex and uses:

```lean
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite HomologicalComplex
```

Both attributes are explicitly local to the current section. The namespace opening
changes name resolution in this file. Neither command changes imported consumers.
The theorem now has a complete proof, with two proved private helpers. Its binders,
universe, conclusion, name and visibility are identical, as are the public imports.
No definition body or mathematical statement changes.

## Users

The query `python3 tools/downstream.py Sheaf.Paper.DerivedNakayama --uses
AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
reports these two transitive consumers and no external textual use of the theorem
name. Both sources were inspected, including their imports and declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Imports this module for its planned proof; all public signatures and definitions are identical. No adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Imports this module for reconstruction; the existing Nakayama interface is identical. No adaptation. |

No consumer's statement becomes weaker, stronger or different. No target statement
or definition used by a target changes, and no additional statement review is needed.
No consumer module is edited by this delivery.

## Status

landed 20261019T112547-L-3955560 2026-10-19 (merge of deliver/U6/Sheaf.Paper.DerivedNakayama)
2026-10-19. Awaiting delivery and the maintainer's global build.
