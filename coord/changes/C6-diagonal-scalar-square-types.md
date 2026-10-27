# ScalarSquareIsomorphisms and uniformizer scalar-square statements

## Reason

The original mate statement alone, even with a temporary unfinished proof, exceeded the
120-second diagnostic limit during olean serialization. The fully proved version likewise
failed artifact generation despite kernel synchronization completing in 26.5 seconds.
Transparent aliases for the full derived model, canonical normalized square, and universal
mate-isomorphism predicate reduce the specialization test's serialization to 3.47 seconds.
All aliases unfold to the old expressions. The arithmetic parameters, uniformizer hypothesis,
scheme morphism, arbitrary full derived model, universal quantification over complexes,
and actual mate are identical. No Challenge statement or source-library declaration changes.
The new types are in Sheaf.Paper.DiagonalScalarSquareTypes, which the item publicly imports
because its statements use these aliases.

## Old

```lean
structure ScalarSquareIsomorphisms
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f)) where
  square : RestrictionSquare a f R
    (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))
  isIso : ∀ K : DerivedCategory (Modules Λ X), IsIso ((square.mate a).app K)

-- The uniformizer hypothesis stays in the public interface; square existence is general.
set_option linter.unusedVariables false in

theorem diagonal_uniformizer_restriction_square
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f)) :
    Nonempty (RestrictionSquare (quotientMap l E π n) f R
      (canonicalDiagonalRightDerived
        (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f)))

theorem diagonal_uniformizer_restriction_mate_isIso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f))
    (square : RestrictionSquare (quotientMap l E π n) f R
      (canonicalDiagonalRightDerived
        (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f))) :
    ∀ K : DerivedCategory
      (Modules (Profinite.padicIntegersRingObj.{u} l E.1) X),
      IsIso ((square.mate (quotientMap l E π n)).app K)

theorem diagonal_uniformizer_scalar_squares
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f)) :
    Nonempty (ScalarSquareIsomorphisms (quotientMap l E π n) f R)
```

## New

```lean
structure ScalarSquareIsomorphisms
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived Λ f) where
  square : CanonicalScalarSquare a f R
  isIso : ScalarMateIsIso a square

theorem diagonal_uniformizer_restriction_square
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived (Profinite.padicIntegersRingObj.{u} l E.1) f) :
    Nonempty (CanonicalScalarSquare (quotientMap l E π n) f R)

theorem diagonal_uniformizer_restriction_mate_isIso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived (Profinite.padicIntegersRingObj.{u} l E.1) f)
    (square : CanonicalScalarSquare (quotientMap l E π n) f R) :
    ScalarMateIsIso (quotientMap l E π n) square

theorem diagonal_uniformizer_scalar_squares
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived (Profinite.padicIntegersRingObj.{u} l E.1) f) :
    Nonempty (ScalarSquareIsomorphisms (quotientMap l E π n) f R)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalUniformizerScalarSquares | C6 | Uses definitionally identical type aliases. |
| Sheaf.Paper.DiagonalUniformizerScalarFrame | unchanged, no adaptation | Direct importer; unchanged source compiled successfully against this delivery. |

The DAG citers are lem-diagonal-uniformizer-scalar-squares (for both component lemmas)
and lem-diagonal-uniformizer-scalar-frame (for the assembled result). Every use holds
by unfolding the aliases; no mathematical statement or dependency hypothesis changes.

Validation: `lcompile.py --all` completed with exit code 0 for all four delivery modules
and the unchanged direct importer. The temporary importer copy was then removed.

## Status

landed 20261027T210115-L-1656928 2026-10-27 (merge of deliver/K1/Sheaf.Paper.DiagonalUniformizerScalarSquares)
