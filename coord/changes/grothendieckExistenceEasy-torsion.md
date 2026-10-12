# AlgebraicGeometry.grothendieckExistenceEasy

## Reason

The Lean statement omitted the source's torsion condition on the algebraized map a,
both for the produced triple and the triples to which uniqueness applies. The DAG
statement already includes this condition. The previous Lean signature is false:
let X = Spec k for a nonzero field k and let I = O_X. Every completion is zero.
Take G = 0 and F the zero formal system. Every coherent H, with its zero map to G,
then qualifies as a comparison triple in the old first clause. It would imply that
0 and O_X are isomorphic. The second clause has the same problem. The corrected
statement restores the exact conditions in Stacks 0889(1)(b) and (2)(b), including
for comparison triples; it does not change the DAG's natural-language statement.
This is an authorized intermediate-statement correction under brief-stage3 §4.

The previously public import CoherentFormalModuleAnnihilated becomes a proof-only
import of the new existence module: none of its declarations occur in this theorem's
signature. The former direct importer GrothendieckExistenceDevissage already imports that
module itself; its concurrent landing removes its import of this item altogether.

## Old

```lean
theorem grothendieckExistenceEasy (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (G : CoherentModules X)
    (F : CoherentFormalModule X I) :
    (∀ (α : F ⟶ (completion X I).obj G),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : H ⟶ G)
        (β : F ≅ (completion X I).obj H),
        α = β.hom ≫ (completion X I).map a ∧
        ∀ (H' : CoherentModules X) (a' : H' ⟶ G)
          (β' : F ≅ (completion X I).obj H'),
          α = β'.hom ≫ (completion X I).map a' →
          ∃! γ : H ≅ H',
            γ.hom ≫ a' = a ∧
              β.hom ≫ (completion X I).map γ.hom = β'.hom) ∧
    (∀ (α : (completion X I).obj G ⟶ F),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : G ⟶ H)
        (β : (completion X I).obj H ≅ F),
        α = (completion X I).map a ≫ β.hom ∧
        ∀ (H' : CoherentModules X) (a' : G ⟶ H')
          (β' : (completion X I).obj H' ≅ F),
          α = (completion X I).map a' ≫ β'.hom →
          ∃! γ : H ≅ H',
            a ≫ γ.hom = a' ∧
              (completion X I).map γ.hom ≫ β'.hom = β.hom)
```

Public imports: CoherentFormalModule and CoherentFormalModuleAnnihilated.

## New

```lean
theorem grothendieckExistenceEasy (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (G : CoherentModules X)
    (F : CoherentFormalModule X I) :
    (∀ (α : F ⟶ (completion X I).obj G),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : H ⟶ G)
        (β : F ≅ (completion X I).obj H),
        (∃ t : ℕ, 1 ≤ t ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (kernel a.hom)) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a.hom))) ∧
        α = β.hom ≫ (completion X I).map a ∧
        ∀ (H' : CoherentModules X) (a' : H' ⟶ G)
          (β' : F ≅ (completion X I).obj H'),
          (∃ t : ℕ, 1 ≤ t ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (kernel a'.hom)) ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a'.hom))) →
          α = β'.hom ≫ (completion X I).map a' →
          ∃! γ : H ≅ H',
            γ.hom ≫ a' = a ∧
              β.hom ≫ (completion X I).map γ.hom = β'.hom) ∧
    (∀ (α : (completion X I).obj G ⟶ F),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : G ⟶ H)
        (β : (completion X I).obj H ≅ F),
        (∃ t : ℕ, 1 ≤ t ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (kernel a.hom)) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a.hom))) ∧
        α = (completion X I).map a ≫ β.hom ∧
        ∀ (H' : CoherentModules X) (a' : G ⟶ H')
          (β' : (completion X I).obj H' ≅ F),
          (∃ t : ℕ, 1 ≤ t ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (kernel a'.hom)) ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a'.hom))) →
          α = (completion X I).map a' ≫ β'.hom →
          ∃! γ : H ≅ H',
            a ≫ γ.hom = a' ∧
              (completion X I).map γ.hom ≫ β'.hom = β.hom)
```

Public import: CoherentFormalModule. Proof imports: GrothendieckExistenceEasyTorsionTriple,
GrothendieckExistenceEasyFromExists, and CompletionIsogenyFromHomLift. Part (1) uses
C1's existing source-faithful torsion-triple statement, which landed during this work.
Part (2) is split into existence without uniqueness and unique compatible Hom descent
without algebraization existence. The item constructs the inverse isomorphism, proves
its inverse identities, and proves uniqueness by cancellation and uniqueness of Hom lifts.
No definition or target signature changes. The DAG statement already has the correct
torsion restrictions, so only its Lean record and proof route are changed.

## Users

Source-only downstream.py found zero transitive importers on the current base.
During this session C1 changed GrothendieckExistenceDevissage to use the separate
GrothendieckExistenceEasyTorsionTriple declaration; it no longer imports this module.
The old first-direction defect was independently identified there. No downstream
module needs adaptation. Earlier in this session the inventory had 193 importers,
but none called grothendieckExistenceEasy. The only direct importer at that point,
GrothendieckExistenceDevissage, imported CoherentFormalModuleAnnihilated itself.
No target statement meaning is changed by this intermediate-theorem correction.

| module | group holding it | effect |
|---|---|---|


## Status

landed 20261012T213437-L-1178375 2026-10-12 (merge of deliver/P1/Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy)
