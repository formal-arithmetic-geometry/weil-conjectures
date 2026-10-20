# AlgebraicGeometry.exists_koszul_restriction_test_cycles

## Reason

The stage-3 queue marks `Sheaf.RingTheory.KoszulRestrictionTestCycles` as `retire`.
The upstream module `WeilConjectures.RingTheory.KoszulRestrictionTestCycles`
already proves the same theorem. The two public theorem signatures are
byte-for-byte identical. The only substantive source difference is the namespace
of private helpers. Keeping both copies duplicates the same public declaration.

`tools/downstream.py Sheaf.RingTheory.KoszulRestrictionTestCycles --uses
exists_koszul_restriction_test_cycles` reports zero downstream modules and only
the duplicate's own declaration as a textual use. A full Lean source search
confirms there are no imports of the Sheaf module. Its surviving consumer,
`WeilConjectures.RingTheory.SelfTorRestrictionConormalWedge`, already imports
the upstream module directly.

## Old

`lean/Sheaf/RingTheory/KoszulRestrictionTestCycles.lean` declares:

```lean
theorem exists_koszul_restriction_test_cycles
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (φ : A →+* B) (n : ℕ) (g : Fin n → I) (g' : Fin n → J)
    (hg : ∀ j, φ (g j) = g' j)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (Q : ProjectiveResolution (ModuleCat.of B (B ⧸ J)))
    (ψ : (A ⧸ I) →+* (B ⧸ J))
    (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj Q.complex)
    (k : ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
        (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
          (.down ℕ)).obj Q.complex))
    (ha : ∀ x : P.complex.X 0, Q.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x))
    (hk : ∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
      k.f j (x ⊗ₜ[A] y) = (show Q.complex.X j from a.f j x) ⊗ₜ[B] (ψ y)) :
    let KA := ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A))
    let KB := ExteriorAlgebra.koszulComplex B n (fun j ↦ (g' j : B))
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
    ∃ (aA : KA ⟶ P.complex) (aB : KB ⟶ Q.complex),
      aA.f 0 ≫ P.π.f 0 = ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin n →₀ A)).toLinearMap) ∧
      aB.f 0 ≫ Q.π.f 0 = ModuleCat.ofHom (J.mkQ.comp
        (exteriorPower.zeroEquiv B (Fin n →₀ B)).toLinearMap) ∧
      ∃ (zA : (TA.obj KA).cycles n) (zB : (TB.obj KB).cycles n),
        (TA.obj KA).iCycles n zA =
          (exteriorPower.ιMulti A n (fun j ↦ Finsupp.single j 1)) ⊗ₜ[A] (1 : A ⧸ I) ∧
        (TB.obj KB).iCycles n zB =
          (exteriorPower.ιMulti B n (fun j ↦ Finsupp.single j 1)) ⊗ₜ[B] (1 : B ⧸ J) ∧
        (TB.obj Q.complex).iCycles n (HomologicalComplex.cyclesMap (TB.map aB) n zB) =
          k.f n ((TA.obj P.complex).iCycles n
            (HomologicalComplex.cyclesMap (TA.map aA) n zA))
```

The DAG node `new-t2-koszul-restriction-test-cycles` points to that Sheaf module.

## New

Withdraw the Sheaf module through `deleted.txt`; landing leaves an empty module.
The DAG node points to the existing theorem of the identical name and signature
in `WeilConjectures.RingTheory.KoszulRestrictionTestCycles`.
The upstream module, its proof, public imports, and declarations are preserved.
The existing proof plan and dependencies remain applicable to that proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KoszulRestrictionTestCycles | P4 | Withdraw the duplicate. |
| WeilConjectures.RingTheory.SelfTorRestrictionConormalWedge | unchanged; no adaptation | Already imports the upstream theorem directly. |

There are no downstream modules of the withdrawn Sheaf module, so no consumer
adaptation is needed. No target statement or definition changes meaning.
The node attachment changes location only; the statement is identical.

## Status

landed 20261020T141314-L-2035499 2026-10-20 (merge of deliver/P4/Sheaf.RingTheory.KoszulRestrictionTestCycles)
