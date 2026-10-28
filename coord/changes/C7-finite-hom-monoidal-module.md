# WeilConjectures.FiniteHomDomainMonoidal

## Reason

Relocate the predicate verbatim to `Sheaf.Paper.FiniteHomMonoidalData`, and publicly
re-export it from `Sheaf.Paper.FiniteHomDomainCalculus`, so the generic-ring monoidal
proof can compile independently. Profiling the original combined file showed 33.5 s
kernel checking the generic bridge and 15.5 s checking the finite specialization,
on top of the earlier proofs. The public name, complete signature, body, visibility
and mathematical meaning are unchanged. No new axioms or instance changes.

## Old

In `Sheaf.Paper.FiniteHomDomainCalculus`:

```lean
def FiniteHomDomainMonoidal {C : Type a₁} {C' : Type a₂}
    [Category.{b₁} C] [Category.{b₂} C'] [MonoidalCategory C] [MonoidalCategory C']
    (F : C ⥤ C') {V : C → C → Type b₂} (δ : ∀ U V', V U V')
    {W : Type b₂} (e : W)
    {B : C → C → Type b₁} (σ : ∀ U V, B U V)
    {B' : C' → C' → Type b₂} (σ' : ∀ U V, B' U V) : Prop :=
  ∃ S : F.CoreMonoidal,
    HEq S.εIso.symm e ∧
    (∀ U V, HEq (S.μIso U V).symm (δ U V)) ∧
    (∃ β : ∀ U V : C, U ⊗ V ≅ V ⊗ U,
      ∃ β' : ∀ U V : C', U ⊗ V ≅ V ⊗ U,
      (∀ U V, HEq (β U V) (σ U V)) ∧
      (∀ U V, HEq (β' U V) (σ' U V)) ∧
      ∀ U V, (β' (F.obj U) (F.obj V)).hom ≫ (S.μIso V U).hom =
        (S.μIso U V).hom ≫ F.map (β U V).hom)
```

## New

In `Sheaf.Paper.FiniteHomMonoidalData`, publicly re-exported by the original module:

```lean
def FiniteHomDomainMonoidal {C : Type a₁} {C' : Type a₂}
    [Category.{b₁} C] [Category.{b₂} C'] [MonoidalCategory C] [MonoidalCategory C']
    (F : C ⥤ C') {V : C → C → Type b₂} (δ : ∀ U V', V U V')
    {W : Type b₂} (e : W)
    {B : C → C → Type b₁} (σ : ∀ U V, B U V)
    {B' : C' → C' → Type b₂} (σ' : ∀ U V, B' U V) : Prop :=
  ∃ S : F.CoreMonoidal,
    HEq S.εIso.symm e ∧
    (∀ U V, HEq (S.μIso U V).symm (δ U V)) ∧
    (∃ β : ∀ U V : C, U ⊗ V ≅ V ⊗ U,
      ∃ β' : ∀ U V : C', U ⊗ V ≅ V ⊗ U,
      (∀ U V, HEq (β U V) (σ U V)) ∧
      (∀ U V, HEq (β' U V) (σ' U V)) ∧
      ∀ U V, (β' (F.obj U) (F.obj V)).hom ≫ (S.μIso V U).hom =
        (S.μIso U V).hom ≫ F.map (β U V).hom)
```

## Users

`tools/downstream.py Sheaf.Paper.FiniteHomDomainCalculus --uses
WeilConjectures.FiniteHomDomainMonoidal` finds only the assigned module mentioning
the name. The other rows are its direct importers; current server claim records
show all three as unclaimed. No consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteHomDomainCalculus | C7 | public re-export preserves the predicate; proof uses the generic-ring theorem |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | unchanged, same public name and definition |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | unchanged, same public name and definition |
| Sheaf.Paper.EtaleLisseHomReduction | unclaimed | unchanged, same public name and definition |

## Status

landed 20261028T020240-L-2485019 2026-10-28 (merge of deliver/C7/Sheaf.Paper.FiniteHomDomainCalculus)
