# AlgebraicGeometry.ProEtale.IntegralQuotient.SectionExchangeRealized

## Reason

A minimal application of normalized_scalar_section_family checks in 0.043 seconds
in the kernel. Eliminating the same theorem directly into the concrete existential
section-realization conclusion exhausted the kernel heartbeat and file-time limits.
The conclusion repeatedly expands the completed coefficient module categories.
Name that exact existential as an irreducible predicate over general coefficient
rings, prove its API before specializing, and use the predicate in the main theorem.
This is a definition-size repair: all scalar data and all three realization equations
remain present, with their original quantifiers and specified maps. No axiom, new
hypothesis, weaker conclusion or data choice is introduced.

## Old

```lean
theorem integral_quotient_exchange_comparison
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      PullNormalized (reduction l E n) u (b u))
    (sq : ChosenCartesianSquare h f' f g) :
    (Functor.whiskerRight (rho (reduction l E n) f (b f)) (L (finite l E n) g) ≫
        Functor.whiskerLeft (D (reduction l E n) X) (ambient (finite l E n) sq) ≫
        Functor.whiskerRight (b h).hom (F (finite l E n) f') =
      Functor.whiskerLeft (F (integral l E) f) (b g).hom ≫
        Functor.whiskerRight (ambient (integral l E) sq) (D (reduction l E n) Y') ≫
        Functor.whiskerLeft (L (integral l E) h) (rho (reduction l E n) f' (b f'))) ∧
    IsIso (rho (reduction l E n) f (b f)) ∧
    IsIso (rho (reduction l E n) f' (b f')) ∧
    ExchangeRealized (integral l E) sq ∧ ExchangeRealized (finite l E n) sq ∧
    ∃ q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n),
    ∃ e₀ : ∀ T : Scheme.{u},
        extension (reduction l E n) T ⋙
            (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
          (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ (q T).extension,
    ∃ e : ∀ T : Scheme.{u},
        D (reduction l E n) T ⋙ ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
          ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ (q T).derived,
      (∀ T : Scheme.{u}, ScalarRealized l E n T (q T) (e₀ T) (e T)) ∧
    ∃ χ : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
        (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) u ≅
          ModuleRingedComparison.derivedPullback (integral l E) u ⋙ (q U).derived,
      (∀ {U V : Scheme.{u}} (u : U ⟶ V) (M : DerivedCategory (Modules (integral l E) V)),
        (pullSection (finite l E n) u).hom.app
            ((D (reduction l E n) V).obj M) ≫
            (ModuleRingedComparison.derivedPullback (finite l E n) u).map
              ((e V).hom.app M) ≫
            (χ u).hom.app ((ModuleRingedComparison.derivedFunctor (integral l E) V).obj M) =
          (ModuleRingedComparison.derivedFunctor (finite l E n) U).map ((b u).hom.app M) ≫
            (e U).hom.app ((L (integral l E) u).obj M) ≫
            (q U).derived.map
              ((pullSection (integral l E) u).hom.app M)) ∧
      (∀ {U V : Scheme.{u}} (u : U ⟶ V) (K : DerivedCategory (Modules (integral l E) U)),
        (ModuleRingedComparison.derivedFunctor (finite l E n) V).map
            ((rho (reduction l E n) u (b u)).app K) ≫
            (pushSection (finite l E n) u).hom.app
              ((D (reduction l E n) U).obj K) ≫
            (ModuleRingedComparison.derivedPushforward (finite l E n) u).map
              ((e U).hom.app K) =
          (e V).hom.app ((F (integral l E) u).obj K) ≫
            (q V).derived.map
              ((pushSection (integral l E) u).hom.app K) ≫
            (sectionProjection l E n q u (χ u)).app
              ((ModuleRingedComparison.derivedFunctor (integral l E) U).obj K)) ∧
      (Functor.whiskerRight (sectionProjection l E n q f (χ f))
          (ModuleRingedComparison.derivedPullback (finite l E n) g) ≫
        Functor.whiskerLeft (q X).derived (sectionExchange (finite l E n) sq) =
      Functor.whiskerLeft (ModuleRingedComparison.derivedPushforward (integral l E) f)
          (χ g).hom ≫
        Functor.whiskerRight (sectionExchange (integral l E) sq) (q Y').derived ≫
        Functor.whiskerLeft (ModuleRingedComparison.derivedPullback (integral l E) h)
          (sectionProjection l E n q f' (χ f')) ≫
        Functor.whiskerRight (χ h).inv
          (ModuleRingedComparison.derivedPushforward (finite l E n) f'))
```

## New

```lean
theorem integral_quotient_exchange_comparison
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      PullNormalized (reduction l E n) u (b u))
    (sq : ChosenCartesianSquare h f' f g) :
    (Functor.whiskerRight (rho (reduction l E n) f (b f)) (L (finite l E n) g) ≫
        Functor.whiskerLeft (D (reduction l E n) X) (ambient (finite l E n) sq) ≫
        Functor.whiskerRight (b h).hom (F (finite l E n) f') =
      Functor.whiskerLeft (F (integral l E) f) (b g).hom ≫
        Functor.whiskerRight (ambient (integral l E) sq) (D (reduction l E n) Y') ≫
        Functor.whiskerLeft (L (integral l E) h) (rho (reduction l E n) f' (b f'))) ∧
    IsIso (rho (reduction l E n) f (b f)) ∧
    IsIso (rho (reduction l E n) f' (b f')) ∧
    ExchangeRealized (integral l E) sq ∧ ExchangeRealized (finite l E n) sq ∧
    SectionExchangeRealized (reduction l E n) b sq
```

SectionExchangeRealized a b sq expands to the old final existential q, e₀, e, χ
and the same three conjunctions, replacing integral/finite/reduction by arbitrary
R/S/a. ScalarComparisonRealized expands to the former ScalarRealized equations.
The generic sectionScalarProjection is the same mateEquiv of χ.hom under the
actual derived adjunctions. The former sectionProjection now specializes that
definition, with its signature unchanged. Unfolding the three predicates and
sectionReduction gives the old conclusion verbatim, up to these transparent aliases.
The proof is internal to this file; no new holed lemma or split-off module is used.
The named predicate is irreducible for elaboration, with its ordinary definitional
equation available through unfold SectionExchangeRealized.

## Users

The read-only tools/downstream.py scan found zero downstream modules. --uses for
ScalarRealized, ExchangeRealized, ambient, sectionExchange, pullSection and
pushSection found only this module. A fresh scan for the theorem and sectionProjection
is recorded in the report. Existing DAG parents retain the same item attachment;
they can unfold the named predicate to obtain its exact previous existential.
No source-library file changes. The target semantic review must check this equivalent
presentation of a predicate below the target.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralQuotientExchangeComparison | D7 | Name the exact section existential before coefficient specialization. |

## Status

landed 20261025T162207-L-354963 2026-10-25 (merge of deliver/D7/Sheaf.Paper.IntegralQuotientExchangeComparison)
