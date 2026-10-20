# CategoryTheory.TruncationCouple.raw_naturality

## Reason

Retirement row `retire:Sheaf.CategoryTheory.TruncationCoupleNaturality` in
`coord/retire-items.tsv`, under the human's hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The row has no prerequisite retirements.
The adopted `WeilConjectures` module already supplies all four public declarations
of the copy. Their three definitions and the displayed naturality conclusion agree
verbatim. Upstream's theorem omits the unused Grothendieck hypothesis on B;
its proof applies directly to the consumer, which retains its existing assumptions.

## Old

Module `Sheaf.CategoryTheory.TruncationCoupleNaturality`, with context:

```lean
variable {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
```

The definitions (including their original intervening docstrings) are:

```lean
noncomputable def abutmentMap (K : CochainComplex.Plus A) (n : ℤ) :
    D F K 0 n ⟶ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
      (DerivedCategory.Q.obj K.obj) :=
  eqToHom (by unfold D; rw [zero_add]) ≫
    (bridgeIso F (truncation K n) n).inv ≫
    (DerivedCategory.homologyFunctor B n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))

/-- The first shift comparison, without comparison to ordinary right derived functors.
Source: Stacks Tags 015J, 05TC (blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def singleIso (K : CochainComplex.Plus A) (p q : ℤ) :
    E F K p q ≅
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B p).obj (K.obj.homology q) :=
  (bridgeIso F (cohomologyComplex K q) (p + q)).symm ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
          (by omega)).app (K.obj.homology q)).symm) ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-q)).app
        ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q))) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p
      (by omega)).app
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q)))

/-- Transport derived cohomology of a map to cohomology of its representing complexes.
Source: derived localization, Stacks Tag 05S7
(blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def homologyMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    K.obj.homology q ⟶ N.obj.homology q :=
  ((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv ≫
    (DerivedCategory.homologyFunctor A q).map c ≫
    ((DerivedCategory.homologyFunctorFactors A q).app N.obj).hom
```

The theorem signature is:

```lean
theorem raw_naturality (K N : CochainComplex.Plus A)
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) :
    ∃ (tD : ∀ p q : ℤ, D F K p q ⟶ D F N p q)
      (tE : ∀ p q : ℤ, E F K p q ⟶ E F N p q),
      (∀ p q : ℤ, tD p q ≫ alpha F N p q =
        alpha F K p q ≫ tD (p - 1) (q + 1)) ∧
      (∀ p q : ℤ, tE p q ≫ f F N p q = f F K p q ≫ tD (p + 2) (q - 1)) ∧
      (∀ p q : ℤ, tD p q ≫ g F N p q = g F K p q ≫ tE p q) ∧
      (∀ n : ℤ, tD 0 n ≫ abutmentMap F N n = abutmentMap F K n ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c) ∧
      (∀ p q : ℤ, tE p q ≫ (singleIso F N p q).hom = (singleIso F K p q).hom ≫
        (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B p).map (homologyMap c q))
```

## New

Withdraw the Sheaf module through `deleted.txt`. Its four public names are supplied
by `WeilConjectures.CategoryTheory.TruncationCoupleNaturality`; the definitions and
textual theorem signature shown above are byte-identical there. Upstream scopes
`omit [IsGrothendieckAbelian.{v} B] in` over `raw_naturality`, so that theorem has
one fewer implicit instance argument. No call-site term change is required.
All source-library declarations, proofs, attributes and public imports are untouched.

The consumer's only changed line is:

```lean
import WeilConjectures.CategoryTheory.TruncationCoupleNaturality
```

It replaces:

```lean
import Sheaf.CategoryTheory.TruncationCoupleNaturality
```

Reattach node `lem-pc-raw-truncation-couple-naturality` to the adopted module,
keeping the declaration name, mathematical statement, proof and dependencies.
The parent node continues to cite it and keeps the same argument and unit route.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.TruncationCoupleNaturality | J6 retirement item | Withdraw the duplicate; all four names remain available from the adopted module. |
| Sheaf.CategoryTheory.NaturalTruncationCouple | unclaimed in the shared snapshot | Replace its single proof import; all signatures and proof bodies stay verbatim. |
| WeilConjectures.CategoryTheory.NaturalTruncationCouple | unmodified | Already imports the adopted module; unaffected. |

`tools/downstream.py` reports the Sheaf consumer as the sole direct importer.
Searches of both library roots and quarantine find no other import of the withdrawn
module. The raw-naturality node has just one parent, the individual natural-couple
node. That parent remains valid through the new Lean attachment. The unit's
realized lists are empty, and its route is preserved.

The migrated consumer compiles with `lcompile.py` (2.6 seconds, no warnings).
An independent scratch import of the adopted module checks all four names;
each uses only `propext`, `Classical.choice`, and `Quot.sound`. There are zero
holes in the withdrawn module and zero in its adapted consumer.

The import change is forced even if a concurrent group holds the consumer:
compiling the original against the empty retirement stub fails in 3.0 seconds with
`Unknown identifier TruncationCouple.abutmentMap` at line 78,
`Unknown identifier TruncationCouple.singleIso` at line 167, and
`Unknown identifier TruncationCouple.raw_naturality` at line 178. The adapted module
compiles with only line 17 changed. Its project import closure replaces just the
retired copy with its adopted twin and introduces no new pair of duplicate modules.
The delivery dry run passes preflight with CODEX review required.

## Status

landed 20261020T221224-L-4160384 2026-10-20 (merge of deliver/J6/Sheaf.CategoryTheory.TruncationCoupleNaturality)
