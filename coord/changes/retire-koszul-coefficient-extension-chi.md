# ExteriorAlgebra.exists_koszul_coefficient_extension_chi

## Reason

The assigned Sheaf module already has zero holes. Its sole public theorem
is a duplicate of the stronger, proved theorem in
`WeilConjectures.RingTheory.KoszulCoefficientExtensionChi`.
The upstream theorem has the identical cochain-map conclusion and evaluation
formula, with no ideal, regularity or localization assumptions. The original
Sheaf statement follows by applying it to `A r f S`; this was checked with the
server compiler using the original statement verbatim.

There are no imports of the Sheaf module anywhere in the current Lean library.
`tools/downstream.py` reports zero downstream modules. The only consumer of the
public name outside this duplicate is the upstream
`WeilConjectures.RingTheory.KoszulCoefficientExtension`, which already privately
imports the upstream Chi module and calls the stronger theorem with `A r f S`.
Withdraw the redundant Sheaf module under brief step 8d and reattach its existing
DAG node to the upstream theorem. No source-library file is changed.

## Old

In `lean/Sheaf/RingTheory/KoszulCoefficientExtensionChi.lean`:

```lean
theorem exists_koszul_coefficient_extension_chi
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S)) :
  ∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f))),
  ∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v))
```

The file also contains private basis-extension constructions and their proofs.
All existing proofs are complete; this is duplicate removal, not a hole closure.

## New

`lean/Sheaf/RingTheory/KoszulCoefficientExtensionChi.lean` is withdrawn through
`deleted.txt`; the delivery tool leaves an empty module with no declarations.
The public name is supplied by the unchanged source-library module
`WeilConjectures.RingTheory.KoszulCoefficientExtensionChi`:

```lean
theorem exists_koszul_coefficient_extension_chi
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (S : Type u) [CommRing S] [Algebra A S] :
  ∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f))),
  ∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v))
```

The unchanged natural-language DAG statement follows from this stronger theorem.
The DAG's `lean` record now names the upstream module, file and statement.
Its proof dependencies remain: the upstream proof uses the same exterior basis,
Koszul differential and dual-complex construction. No definition, source-library
signature, attribute, public import, or target statement is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KoszulCoefficientExtensionChi | P3 | Withdraw unused duplicate. |
| WeilConjectures.RingTheory.KoszulCoefficientExtension | unclaimed | Already uses upstream Chi; unchanged. |

There are zero downstream importers to adapt. A sandbox example with the old
signature compiled by direct application of the upstream theorem. The upstream
axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.
No target review is reopened because all definitions and target types stay fixed.

## Status

landed 20261020T141313-L-2034961 2026-10-20 (merge of deliver/P3/Sheaf.RingTheory.KoszulCoefficientExtensionChi)
