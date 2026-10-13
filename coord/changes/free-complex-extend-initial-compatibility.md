# free_complex_extend_family

## Reason

The old intermediate statement is false: its degree-zero map is arbitrary, while
Stacks [Tag 00LS](https://stacks.math.columbia.edu/tag/00LS), proof of (1), starts
with a map lifting the augmentation. The missing condition is
`δ 0 ≫ a₀ ≫ η = 0`.

Counterexample over ℤ: take N=N' 0=ℤ, η=id, higher N' terms zero and all d zero.
Take F 0=F 1=ℤ, higher F terms zero, δ 0=id, higher δ zero, and a₀=id.
Both complexes satisfy the original hypotheses, including target exactness and
freeness, but the degree-one compatibility would assert 0=id on ℤ.

The added condition is necessary, not merely sufficient: any proposed family
has δ 0 ≫ a₀ ≫ η = α 1 ≫ d 0 ≫ η = 0, using α 0=a₀ and hd0.
It is already implied by the sole caller's hypotheses. The corrected lemma is
fully proved by Mathlib projective lifting and dependent recursion. No data is
chosen from an unproved existence theorem.

## Old

```lean
theorem free_complex_extend_family
    (R : Type u) [CommRing R]
    (N : ModuleCat R) (N' : ℕ → ModuleCat R)
    (d : ∀ i : ℕ, N' (i + 1) ⟶ N' i)
    (η : N' 0 ⟶ N)
    (hd0 : d 0 ≫ η = 0)
    (hd : ∀ i : ℕ, d (i + 1) ≫ d i = 0)
    (hex0 : (ShortComplex.mk (d 0) η hd0).Exact)
    (hex : ∀ i : ℕ, (ShortComplex.mk (d (i + 1)) (d i) (hd i)).Exact)
    (F : ℕ → ModuleCat R)
    (δ : ∀ i : ℕ, F (i + 1) ⟶ F i)
    (hδ : ∀ i : ℕ, δ (i + 1) ≫ δ i = 0)
    (hfree : ∀ i : ℕ, Module.Free R (F i))
    (a₀ : F 0 ⟶ N' 0) :
    ∃ α : ∀ i : ℕ, F i ⟶ N' i,
      α 0 = a₀ ∧ (∀ i : ℕ, α (i + 1) ≫ d i = δ i ≫ α i)
```

## New

```lean
theorem free_complex_extend_family
    (R : Type u) [CommRing R]
    (N : ModuleCat R) (N' : ℕ → ModuleCat R)
    (d : ∀ i : ℕ, N' (i + 1) ⟶ N' i)
    (η : N' 0 ⟶ N)
    (hd0 : d 0 ≫ η = 0)
    (hd : ∀ i : ℕ, d (i + 1) ≫ d i = 0)
    (hex0 : (ShortComplex.mk (d 0) η hd0).Exact)
    (hex : ∀ i : ℕ, (ShortComplex.mk (d (i + 1)) (d i) (hd i)).Exact)
    (F : ℕ → ModuleCat R)
    (δ : ∀ i : ℕ, F (i + 1) ⟶ F i)
    (hδ : ∀ i : ℕ, δ (i + 1) ≫ δ i = 0)
    (hfree : ∀ i : ℕ, Module.Free R (F i))
    (a₀ : F 0 ⟶ N' 0) (ha₀ : δ 0 ≫ a₀ ≫ η = 0) :
    ∃ α : ∀ i : ℕ, F i ⟶ N' i,
      α 0 = a₀ ∧ (∀ i : ℕ, α (i + 1) ≫ d i = δ i ≫ α i)
```

## Users

`tools/downstream.py Sheaf.Paper.FreeComplexExtendFamily --uses
free_complex_extend_family` found 398 transitive downstream modules and just
one external declaration user. The only direct importer is that user. All other
transitive users see its unchanged signature; no target definition or statement
changes meaning. No definitions are changed. The theorem corrected here is an
intermediate theorem, absent from Challenge.lean.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FreeComplexExtendFamily | V2 | Add necessary initial compatibility hypothesis; prove the corrected theorem. |
| Sheaf.Paper.FreeComplexMapsToResolution | unclaimed | Forced proof adaptation only; all signatures and visibility preserved. Derive the new hypothesis from ha₀ and hδ0 and pass it to the existing call. |

Original caller against the changed dependency fails at line 58: `Tactic rcases
failed`, because the application now has type `δ 0 ≫ a₀ ≫ η = 0 → ∃ α, ...`.
The original compiles against the original dependency (checked by deliver3.py).
Adapted caller compiles against the changed dependency.

The forced lines replace the old call by a proof of `hstart` and a call with that
extra argument, and remove `have _ := hδ0`, now redundant because hδ0 is used
in that proof. No imports, statements, definitions or visibility change in the
caller. Its DAG proof step now records the same initial compatibility check.
The node's statement_change lists its sole DAG citer and explains why it still
holds.

## Status

landed 20261013T100201-L-2497170 2026-10-13 (merge of deliver/V2/Sheaf.Paper.FreeComplexExtendFamily)
