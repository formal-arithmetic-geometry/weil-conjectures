# AlgebraicGeometry.derivedPullbackComposition_localized_counit

## Reason

The assigned hole is closed by the left-derived universal property and the ordinary
mate counit law. Three proved private helpers keep those categorical calculations
independent of the expensive scheme-module instances. Local transparency settings
identify Scheme.Modules with the shared SheafOfModules category while preserving
the interfaces of derivedPullback, tensorPullback and the selected comparison.
The delivery checker conservatively treats these local attributes and elaboration
options as interface changes. No public signature or definition body is changed.

## Old

The public statement, verbatim, was:

```lean
theorem derivedPullbackComposition_localized_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let b {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
        (ComplexShape.up ℤ)
    (canonicalDerivedPullbackComposition f g).hom.app
        (DerivedCategory.Qh.obj
          (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
      (ε (f ≫ g)).app
        (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((b (f ≫ g)).counit.app K) =
      derivedCompositionCounitApex f g K
```

The original local irreducibility list also contained DerivedCategory.Qh. There
were no implicit_reducible or instance_reducible attributes, and the lazy backward
unification options used their defaults.

## New

The public statement above is unchanged and now has a complete proof. The new
private helpers composite_counit, localized_counit and pushforward_comparison_inv
are all proved without sorry. Local instance_reducible and implicit_reducible
attributes expose only category and quotient wrappers for elaboration; local
irreducibility keeps derived functor choices behind their existing interfaces.
The backward unifier uses lazyProjDelta = false, lazyWhnfCore = false and the
existing backward-defeq interface. The helpers and proof locally permit
semireducible type comparison. The existing instance proofs are explicitly inlined with letI to avoid expensive
let-bound instance comparison; only linter.style.haveILetI is locally disabled
for this theorem for that reason. No attribute or instance is exported, and both
original public imports are retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit | G4 | Complete proof and private helpers; signature unchanged. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | unclaimed | Sole direct importer and theorem user; statement unchanged and no adaptation needed. |

All 476 transitive importers continue to see the identical theorem signature and
public imports. No target statement or definition changes, so statement review is
not reopened. No forced adaptations are delivered.

## Status

landed 20261014T101746-L-1176926 2026-10-14 (merge of deliver/G4/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit)
