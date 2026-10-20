# IsLocalRing.first_term_depth_ge: retire the duplicate Sheaf module

## Reason

The human-approved retirement table lists this item at depth zero, with the
upstream twin `WeilConjectures.RingTheory.CohenMacaulayDepthFirstTerm`.
The main theorem's signature is byte-identical, and the image-syzygy proof is
already present upstream. Its axiom check contains only `propext`,
`Classical.choice`, and `Quot.sound`. Withdraw the redundant Sheaf module and
point its DAG attachment at the upstream theorem. No upstream file changes.

The copy also exposed three depth helpers, whereas the upstream helpers are
private. No live Lean source imports the copy or uses these public helpers.
The former AuslanderBuchsbaum consumer is quarantined; its future restoration
must use the upstream API or supply any additional needed helpers under Sheaf.

## Old

The withdrawn module had the following public signatures:

```lean
theorem depth_equiv_local {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    (e : A ≃ₗ[R] B) : depth (R := R) A = depth (R := R) B

theorem depth_subsingleton {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Subsingleton A] :
    depth (R := R) A = ⊤

theorem depth_free_ge {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Free R A] :
    depth (R := R) R ≤ depth (R := R) A

theorem first_term_depth_ge
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d e : ℕ)
    (hcm : (d : ℕ∞) ≤ depth (R := R) R)
    (he : depth (R := R) M = (e : ℕ∞)) (hed : e ≤ d)
    (S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3))
    (hS : S.Exact) (hzero0 : IsZero (S.obj' 0))
    (hzero1 : IsZero (S.obj' (d - e + 3)))
    (hM : Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M))
    (hfree : ∀ i : Fin (d - e),
      Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
      Module.Finite R (S.obj' (i.val + 2) (by omega)))
    [Module.Finite R (S.obj' 1)] [Nontrivial (S.obj' 1)] :
    (d : ℕ∞) ≤ depth (R := R) (S.obj' 1)
```

The node attached `IsLocalRing.first_term_depth_ge` to
`Sheaf.RingTheory.CohenMacaulayDepthFirstTerm`.

## New

The Sheaf copy is withdrawn via `deleted.txt`; delivery produces an empty
module until maintainer pruning. The unchanged declaration
`IsLocalRing.first_term_depth_ge` is supplied by
`WeilConjectures.RingTheory.CohenMacaulayDepthFirstTerm`.
The node's `lean.module`, `lean.file`, `lean.existing`, and explanatory note
are updated accordingly. Its statement and proof dependencies are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CohenMacaulayDepthFirstTerm | J3 | Withdraw the redundant copy; zero holes before and after. |
| WeilConjectures.RingTheory.CohenMacaulayFreeResolutionMCM | unclaimed | Already imports the upstream twin; compiles unchanged. |
| Sheaf.RingTheory.CohenMacaulayFreeResolutionMCM | absent | Historical retirement-table consumer; no live source to adapt. |
| Sheaf.RingTheory.AuslanderBuchsbaum | quarantined | No live source to adapt; restoration remains a separate rework item. |

A scan of all live `lean/**/*.lean` sources finds no import of the copy.
The only live external use of `first_term_depth_ge` is the upstream consumer
above. Other similarly named private depth lemmas are local declarations in
unrelated files and do not use the retired helpers. No forced adaptations.

## Status

landed 20261020T135412-L-1819816 2026-10-20 (merge of deliver/J3/Sheaf.RingTheory.CohenMacaulayDepthFirstTerm)
