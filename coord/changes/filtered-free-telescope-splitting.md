# CochainComplex.isKProjective_of_filtered_free_telescope

## Reason

The existing node states an exhaustive **split** filtered union, but its Lean declaration
omits the degreewise retraction hypothesis. Stacks Tag 09KL explicitly uses those
retractions to make the telescope sequence admissible; without them the theorem is false.
For example, over Z take all complexes concentrated in degree zero, F(0) = 0,
F(n) = 2^{-(n-1)} Z for n >= 1, P = Z[1/2], and the inclusion maps. Every finite
stage is free and hence K-projective, and the union is exhaustive, but Z[1/2] is not a
projective Z-module. A degree-zero complex is K-projective only if its module is projective:
apply the null-homotopy condition to the acyclic complex of any short exact sequence to
obtain the usual lifting property. Concretely Hom_Z(Z[1/2], Z) = 0, so Z[1/2] cannot be a
summand of a free abelian group. Thus it is not K-projective. The inclusions in this example
are not split, precisely the missing hypothesis.

Add the same `hsplit` already assumed by `isKProjective_of_filtered_free` to the intermediate
telescope theorem, and pass it in the top theorem's existing proof. The top theorem,
finite-stage theorem, every definition, and every Challenge target keep their signatures.
The telescope node already says "split", so only its Lean record and proof are corrected;
its natural-language statement is unchanged.

## Old

```lean
theorem isKProjective_of_filtered_free_telescope
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hstage : ∀ n, (F n).IsKProjective) :
    P.IsKProjective
```

## New

```lean
theorem isKProjective_of_filtered_free_telescope
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

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FilteredFreeKProjective --uses
CochainComplex.isKProjective_of_filtered_free_telescope` reports 768 import descendants (second-reader snapshot),
but only one module using this declaration. A source search for its unqualified name also
finds only that module. No descendant statement uses the telescope theorem as data, and
the exported final filtered-free theorem retains its type. No other module needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FilteredFreeKProjective | F1 | The final theorem passes its existing hsplit argument to telescope assembly. No other signature changes. |

The targets use unchanged definitions, so their meaning is unchanged and no target
statement review is reopened by a definition change. This intermediate statement repair
requires independent CODEX review.

## Status

landed 20261012T205629-L-931775 2026-10-12 (merge of deliver/F1/Sheaf.Algebra.Homology.FilteredFreeKProjective)
