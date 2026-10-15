# CategoryTheory.BigradedExactCouple.exactFunctor_couple — private helper context

## Reason

The complete proof adds private construction helpers. Their `variable` commands
share the category, functor and preservation assumptions; `omit ... in` keeps
irrelevant assumptions out of helper signatures. The static interface checker
classifies all such commands as interface changes, even though these elaboration
commands add no exported declaration, instance, notation, attribute or rule.
This record documents that classification. The existing public theorem statement
is byte-for-byte unchanged, and its only public import is unchanged. No existing
definition or public visibility changes. The new public helper theorem has its own
new node and module and is fully proved.

## Old

There were no `variable` or `omit` commands in the item namespace. It contained only
the explicitly quantified theorem. The namespace header was:

```lean
namespace CategoryTheory.BigradedExactCouple
```

## New

The namespace header and public theorem signature are unchanged. The following
elaboration contexts are added verbatim around private helpers:

```lean
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {s : ℕ}

variable {Φ}

omit [Abelian C] [Abelian B] [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in

omit [Φ.Additive] in

omit [PreservesFiniteColimits Φ] in

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in

omit [PreservesFiniteColimits Φ] in

omit [Φ.Additive] in

omit [Φ.Additive] in

omit [PreservesFiniteColimits Φ] in

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (X : BigradedExactCouple C 0) (Y : BigradedExactCouple B 0)
  (hD : ∀ p q : ℤ, Φ.obj (X.D p q) = Y.D p q)
  (ha : ∀ p q : ℤ, Φ.map (X.alpha p q) ≫ eqToHom (hD (p - 1) (q + 1)) =
    eqToHom (hD p q) ≫ Y.alpha p q)
  (AX : ∀ n : ℤ, AlphaColimit X n) (AY : ∀ n : ℤ, AlphaColimit Y n)
  (hAX : ∀ n : ℤ, (AX n).obj = X.D 0 n)
  (hAY : ∀ n : ℤ, (AY n).obj = Y.D 0 n)
  (hAX0 : ∀ n : ℤ, (AX n).ι 0 ≫ eqToHom (hAX n) =
    eqToHom (by congr 1; omega))
  (hAY0 : ∀ n : ℤ, (AY n).ι 0 ≫ eqToHom (hAY n) =
    eqToHom (by congr 1; omega))
```

The private helpers do not occur in any existing public signature. Private data
constructions occur only in the public theorem's proof, never in a public definition.
All helpers and both public theorems compile; their axiom audit uses only propext,
Classical.choice and Quot.sound. No adaptation of any importing module is necessary.

## Users

The following are all modules returned by `tools/downstream.py` (repository claim
snapshot). Their signatures, imported public declarations and elaboration behavior
are unaffected; no file is changed or adapted. The item module itself uses the new
private helpers in its proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactFunctorCouple | C4 | Proof completed; signature unchanged. |
| Sheaf.CategoryTheory.ExactFunctorHalfPlane | new in C4 delivery | New proved theorem and private helpers. |
| Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | B2 | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | A4 | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion | A4 | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | C3 | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercohomologyConvergence | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercohomologyFiltrations | C2 | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Not affected; no adaptation. |
| Sheaf.AlgebraicGeometry.TruncationExchangeAbutment | D2 | Not affected; no adaptation. |
| Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit | unclaimed | Not affected; no adaptation. |
| Sheaf.CategoryTheory.TruncationsAndHomotopyColimits | unclaimed | Not affected; no adaptation. |
| Sheaf.Paper.ExactCoupleDifferential | unclaimed | Not affected; no adaptation. |
| Sheaf.Targets.EtaleSmooth | C1 | Not affected; no adaptation. |
| Sheaf.Targets.EtaleSmoothRing | A2 | Not affected; no adaptation. |
| TargetsCheck | unclaimed | Not affected; no adaptation. |

## Status

landed 20261015T161928-L-300725 2026-10-15 (merge of deliver/C4/Sheaf.CategoryTheory.ExactFunctorCouple)
