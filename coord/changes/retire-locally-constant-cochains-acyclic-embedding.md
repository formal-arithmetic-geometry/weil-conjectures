# Rep.locallyConstantCochains_acyclic_embedding and its duplicate module

## Reason

The human-approved retirement queue lists this Sheaf module as a copy of the existing,
proved upstream module. Retire the copy and redirect its DAG attachment to the upstream
theorem. The only remaining direct importer is the unclaimed
`Sheaf.RepresentationTheory.CoinducedHomotopyIdentity`, which uses the two public insertion
helpers. Those helpers are private upstream. Merely switching its import to the twin fails
with `Unknown identifier contract_insert_zero` and `Unknown identifier contract_insert_succ`
at the original line 184. Derive the specialized equalities inside its existing proof instead.
No upstream source, definition, public consumer signature, public import, or target changes.

## Old

The withdrawn module publicly declares the following signatures in namespace `Rep`:

```lean
theorem contract_insert_zero (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) :
    Fin.contractNth 0 (· * ·) (Fin.cons x g) =
      Fin.cons (x * g 0) (fun i ↦ g i.succ)

theorem contract_insert_succ (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) (k : Fin (n + 1)) :
    Fin.contractNth k.succ (· * ·) (Fin.cons x g) =
      Fin.cons x (Fin.contractNth k (· * ·) g)

theorem locallyConstantCochains_acyclic_embedding
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hm : ∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
      e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g))
    (hd : ∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
      e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
        (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g))
    (M : A) : ∃ (N : A) (f : M ⟶ N), Mono f ∧
      ∀ n : ℕ, 0 < n → (C.obj N).ExactAt n
```

Its consumer imports `Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`
only for its proof and rewrites with the two public tuple lemmas.

## New

The canonical existing declaration in
`WeilConjectures.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`, also in
namespace `Rep`, is unchanged:

```lean
theorem locallyConstantCochains_acyclic_embedding
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hm : ∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
      e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g))
    (hd : ∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
      e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
        (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g))
    (M : A) : ∃ (N : A) (f : M ⟶ N), Mono f ∧
      ∀ n : ℕ, 0 < n → (C.obj N).ExactAt n
```

Withdraw the Sheaf copy using `deleted.txt`. Its two public helper declarations have no
remaining caller. The consumer proves their two instances as local facts `hzero` and `hsucc`
by `funext`, `Fin.cases`, and `simp [Fin.contractNth]`, then uses them in the same cancellation.
The upstream private helpers are untouched. No replacement public declarations are added.
The acyclic-embedding node points at the upstream module. The homotopy-identity node drops
its former proof dependency on the acyclic-embedding node and records the local calculation.

## Users

`tools/downstream.py` lists nine transitive import consumers. Searching separately for each
helper finds only the withdrawn module and `CoinducedHomotopyIdentity`. The queue's second
listed consumer `Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable` is already
absent from the current checkout; its upstream twin imports the upstream acyclic embedding.
Claim holders below were checked before writing the adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding | J1 | Withdraw the duplicate; attach its node to the unchanged upstream theorem. |
| Sheaf.RepresentationTheory.CoinducedHomotopyIdentity | unclaimed | Remove the proof import; prove the two specialized tuple equalities locally. |
| Sheaf.RepresentationTheory.CoinducedContinuousAcyclic | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.DiscreteContinuousCohomology | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.DvrGalois | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.DvrGaloisComparison | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.DvrGaloisProcyclic | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.KernelInvariantsCohomology | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |
| Sheaf.RepresentationTheory.ProcyclicTwoTerm | unclaimed | Transitive consumer; public interface unchanged; no adaptation. |

The canonical theorem has exactly the old signature. No target statement or definition
changes, so no target statement review is reopened. The adapted consumer compiles in 2.3 s.
A probe of the canonical theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261020T144250-L-2259590 2026-10-20 (merge of deliver/J1/Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding)
