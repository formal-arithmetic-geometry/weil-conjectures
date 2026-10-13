# ExteriorAlgebra.exists_koszul_coefficient_extension

## Reason

No actual public interface changes. The preflight leanindex parser treats the
unindented existential conclusion as an independent command, so changing its
proof triggers the commands/interface check. This record reports that tool
limitation and documents the unchanged signature; no script was modified.
Two new independent component declarations are added in their own modules.

Repair of landing return X-43d17: indent the existential conclusion in the
parent and both component modules. The previous unindented conclusions caused
import_prune_check.py to compare only common binder prefixes, falsely reporting
that the nu component restated the parent. The full conclusions are distinct:
the parent quantifies chi and nu with two formulas; nu quantifies only nu with
one formula. Whitespace changes preserve all elaborated types and make the
complete conclusions visible to the command parser. No checker was edited.

## Old

```lean
theorem exists_koszul_coefficient_extension
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S))
    (q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)))
    (hq : ∀ b : A, q (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) :
∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f)))
  (ν : koszulNormalDeterminant A I r →ₗ[A]
    (ModuleCat.restrictScalars (algebraMap A S)).obj
      (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
  (∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v))) ∧
  (∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
    exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r (ν w)
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
        (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
          (algebraMap A S ∘ f) hs
          ((v i).mapRange (algebraMap A S) (map_zero _)))) =
    q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
      (exteriorPower.ιMulti (A ⧸ I) r
        (fun i ↦ koszulConormalVector A I r f hf (v i)))))
```

Proof: `by sorry`.

## New

```lean
theorem exists_koszul_coefficient_extension
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S))
    (q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)))
    (hq : ∀ b : A, q (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) :
  ∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f)))
  (ν : koszulNormalDeterminant A I r →ₗ[A]
    (ModuleCat.restrictScalars (algebraMap A S)).obj
      (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
  (∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v))) ∧
  (∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
    exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r (ν w)
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
        (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
          (algebraMap A S ∘ f) hs
          ((v i).mapRange (algebraMap A S) (map_zero _)))) =
    q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
      (exteriorPower.ιMulti (A ⧸ I) r
        (fun i ↦ koszulConormalVector A I r f hf (v i)))))
```

Proof: obtain the chi and nu witnesses and pair their evaluation formulas.
The new modules are imported with plain, proof-only imports.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KoszulCoefficientExtension | B4 | proof only; identical signature |
| Sheaf.RingTheory.KoszulRegularSequenceDualComplex | unclaimed locally; unchanged | same statement, definitions and imports; no adaptation |

All downstream users retain the identical theorem type and definitions.
No target definition changes and no target review is reopened.

## Status

landed 20261013T005854-L-2606112 2026-10-13 (merge of deliver/B4/Sheaf.RingTheory.KoszulCoefficientExtension)
