# LinearMap.extension_descends_of_summands

## Reason

Retire the duplicate `Sheaf.RingTheory.DirectSumExtensionAssembly` listed in
`coord/retire-items.tsv`, using the already proved upstream theorem. The upstream
signature differs only in hypothesis binder names (`hflat`, `hC`, `ha`, `hab`, `hb`
in place of the underscored names); all universes, hypotheses and conclusions agree.
The sole consumer uses positional arguments and needs no proof change.

## Old

```lean
import Sheaf.RingTheory.DirectSumExtensionAssembly
```

The old theorem signature is:

```lean
theorem extension_descends_of_summands
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat)
    {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} (C : J → Type y) [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    (_hC : ∀ (j : J) (T : Type z) [AddCommGroup T] [Module S T]
      (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] C j),
      Function.Injective a → Function.Exact a b → Function.Surjective b →
      ∃ (E : Type (max w y)) (_ : AddCommGroup E) (_ : Module R E)
        (i : N →ₗ[R] E) (q : E →ₗ[R] C j),
        Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
        ∃ θ : S ⊗[R] E ≃ₗ[S] T,
          θ.toLinearMap.comp (i.baseChange S) = a ∧
          b.comp θ.toLinearMap = q.baseChange S)
    {T : Type z} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (⨁ j, C j))
    (_ha : Function.Injective a) (_hab : Function.Exact a b)
    (_hb : Function.Surjective b) :
    ∃ (E : Type (max w x y)) (_ : AddCommGroup E) (_ : Module R E)
      (i : N →ₗ[R] E) (q : E →ₗ[R] (⨁ j, C j)),
      Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (i.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S
```

The duplicate module declares `LinearMap.extension_descends_of_summands` and two
proved private helpers, `glue_extension_maps` and `extension_map_ext`.

## New

```lean
import WeilConjectures.RingTheory.DirectSumExtensionAssembly
```

The upstream theorem signature is:

```lean
theorem extension_descends_of_summands
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat)
    {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} (C : J → Type y) [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    (hC : ∀ (j : J) (T : Type z) [AddCommGroup T] [Module S T]
      (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] C j),
      Function.Injective a → Function.Exact a b → Function.Surjective b →
      ∃ (E : Type (max w y)) (_ : AddCommGroup E) (_ : Module R E)
        (i : N →ₗ[R] E) (q : E →ₗ[R] C j),
        Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
        ∃ θ : S ⊗[R] E ≃ₗ[S] T,
          θ.toLinearMap.comp (i.baseChange S) = a ∧
          b.comp θ.toLinearMap = q.baseChange S)
    {T : Type z} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (⨁ j, C j))
    (ha : Function.Injective a) (hab : Function.Exact a b)
    (hb : Function.Surjective b) :
    ∃ (E : Type (max w x y)) (_ : AddCommGroup E) (_ : Module R E)
      (i : N →ₗ[R] E) (q : E →ₗ[R] (⨁ j, C j)),
      Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (i.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S
```

The consumer uses the upstream declaration of the same name. The duplicate is
withdrawn through `deleted.txt`; the delivery tool leaves an empty module for the
maintainer's pruning. The DAG attachment points at the upstream module, with its
verbatim statement modulo whitespace. No upstream file changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.DirectSumExtensionAssembly | K1 | Withdraw duplicate declarations. |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | unclaimed | Replace one private proof import; identical theorem call and signature. |

## Status

landed 20261020T150650-L-2561755 2026-10-20 (merge of deliver/K1/Sheaf.RingTheory.DirectSumExtensionAssembly)
