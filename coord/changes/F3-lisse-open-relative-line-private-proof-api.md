# AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek

## Reason

The original proof was one `sorry`. Its complete replacement uses private categorical
helpers for constructible object properties, finite filtrations, short exact sequences,
compact-support composition, and prime-annihilator induction. The private functors
`shriekFunctor` and `sourceFunctor` are irreducible names for the actual compact-support
functor and its degree-zero composite. Proved private instances supply their additive,
shift, and triangulated structures and the closure properties used in the proof.
No definition takes arbitrary data from a mere-existence theorem with an unproved body.

The complete initial implementation exceeded 60 seconds because the kernel repeatedly
compared independently inferred abelian and derived-category structures. The private
instance-reducible definitions `stableAbelian` and `stableDerived` name the canonical
structures. Their priority-2000 instance attributes are local to `section StableInstances`,
which ends before the public theorem. The theorem's statement therefore uses the original
instances; its proof introduces the same canonical structures locally. Generic helpers
also accept an arbitrary `HasZeroMorphisms` instance, avoiding another expensive
comparison of definitionally equal structures. The final complete file compiles cleanly
in 35.5 seconds, without changing the existing signature.

Preflight conservatively flags the new `attribute`, `set_option`, and private `instance`
commands. The backward transparency option affects proof elaboration. All added instance
conclusions involve the private proof functors or private object-property expressions.
The public imports remain byte-for-byte unchanged. No existing public definition,
attribute, signature, target statement, or target meaning changes. No source-library file
is edited. The independent reader can inspect these instance scopes and definitions.

## Old

There were no private helper definitions, private instances, local instance-priority
attributes, or backward transparency option. The sole theorem had this signature:

```lean
theorem isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((L.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (U.toScheme.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M))
    (c : Compactification
      (U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L)))
```

Its body was `by sorry`.

## New

The existing theorem retains exactly the signature above; its body is a complete proof.
The added proof infrastructure is private. The two explicit local priority commands are:

```lean
attribute [local instance 2000] stableAbelian
attribute [local instance 2000] stableDerived
```

They occur inside `section StableInstances`. The option is:

```lean
set_option backward.isDefEq.respectTransparency true
```

The complete helper definitions and proved instances are in the delivered item module.
They expose no new public declaration. No theorem has been split off and no hole added.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility
--uses isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek` reports zero
current Lean importers and only the item itself as a textual declaration user. This is
not a withdrawal: unfinished parents still need its DAG statement, which is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | F3 | Proof completed; private proof helpers added; public signature and imports identical. |

No other module is adapted. No consumer statement or mathematical meaning changes.

## Status

landed 20261022T113944-L-435617 2026-10-22 (merge of deliver/F3/Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility)
