# CochainComplex.filtered_free_telescope_assembly

## Reason

The assigned queue entry is a `retire` item (zero existing holes), following the human's
2026-10-20 retirement instruction in `coord/changes/retire-sheaf-twins-20261020.md`.
The adopted upstream twin already proves the same telescope result. It concludes
`P.IsKProjective` directly, whereas the redundant Sheaf copy concludes existence of an
isomorphic K-projective `Q`. These conclusions are equivalent: the direct conclusion
supplies `Q = P` and `Iso.refl P`; the existential conclusion transports K-projectivity
along `Q ≅ P` using `CochainComplex.isKProjective_of_iso`.

Retire only the Sheaf copy. No adopted source file or target statement changes.

## Old

The declaration below is withdrawn from
`Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly`:

```lean
theorem filtered_free_telescope_assembly
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hstage : ∀ n, (F n).IsKProjective) :
    ∃ Q : CochainComplex (ModuleCat.{max u v} A) ℤ,
      Q.IsKProjective ∧ Nonempty (Q ≅ P)
```

Its sole consumer `isKProjective_of_filtered_free_telescope` extracted `Q`, installed its
K-projectivity instance, and transported along the isomorphism to prove `P.IsKProjective`.

## New

The already proved declaration below in
`WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveAssembly` is reused verbatim:

```lean
theorem filtered_free_telescope_assembly
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hstage : ∀ n, (F n).IsKProjective) :
    P.IsKProjective
```

The consumer's private import changes to the upstream module and its proof becomes:

```lean
  filtered_free_telescope_assembly P F ι step hzero hmono hcompat hexhaustive hsplit hstage
```

All consumer signatures, definitions and public imports remain identical. The assembly
node's Lean attachment now names the upstream theorem, with its exact signature and a
note explaining equivalence to the unchanged mathematical node statement. Its proof
origin records reuse of the same telescope argument; both proof dependencies remain.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly
--uses CochainComplex.filtered_free_telescope_assembly` reports one downstream module.
The uses scan also reports the declaration's own module; both are listed below.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly | Y7 | Withdraw redundant copy. |
| Sheaf.Algebra.Homology.FilteredFreeKProjective | unclaimed | Replace private import and telescope proof only; signatures unchanged. |

The upstream twin and its upstream consumer are not modified. Since the consumer's
public signatures are unchanged, its downstream modules require no adaptation and no
target meaning is changed or reopened.

## Status

landed 20261020T132057-L-1411020 2026-10-20 (merge of deliver/Y7/Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly)
