# Completed-adic Koszul construction module relocation

## Reason

Profiling the integrated, fully proved item exposed expensive definitional comparisons.
Scoped irreducibility and explicit type changes removed the largest hotspots, but the
file still exceeded 60 seconds. The self-contained construction segment is separated
from representative independence. No mathematical definition or statement changes.
The assigned module publicly imports the new construction module, preserving its API.

## Old

The following public headers were declared in `Sheaf.Paper.CompletedAdicIntrinsicCompletion`.
Their definition bodies and already proved theorem bodies are preserved; the three
previously missing unit proofs are supplied in the delivery.

```lean
theorem completedAdicScalar_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃! α : adicConstantRing T A ⟶ completedAdicCommRing T d,
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A),
        (completedAdicProjection T d n).hom.app U
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
            ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down))

def completedAdicScalar (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    adicConstantRing T A ⟶ completedAdicCommRing T d

def completedAdicScalarExtensionData (T : Scheme.{t}) (d : AdicCoefficientDatum A)

def completedAdicScalarExtension (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    SheafOfModules.{t + 1} (adicModuleRing T A) ⥤ CompletedAdicModules T d

def completedAdicScalarTensor (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (M : SheafOfModules.{t + 1} (adicModuleRing T A)) (U : T.ProEtᵒᵖ)
    (s : (completedAdicCommRing T d).obj.obj U) (x : M.val.obj U) :
    ((completedAdicScalarExtension T d).obj M).val.obj U

def completedAdicKoszul (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) : CochainComplex (CompletedAdicModules T d) ℤ

def completedAdicKoszulStep (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    completedAdicKoszul T d r a (m + 1) ⟶ completedAdicKoszul T d r a m

theorem completedAdicKoszulUnitZero_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    ∃! u : SheafOfModules.unit (completedAdicRing T d) ⟶ (completedAdicKoszul T d r a m).X 0,
      ∀ U : T.ProEtᵒᵖ, u.val.app U (1 : (completedAdicRing T d).obj.obj U) =
        completedAdicScalarTensor T d _ U 1
          ((koszulSheafUnitZero T A r a m).val.app U
            (1 : (adicModuleRing T A).obj.obj U))

def completedAdicKoszulUnitZero (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    SheafOfModules.unit (completedAdicRing T d) ⟶ (completedAdicKoszul T d r a m).X 0

def completedAdicKoszulTensor (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ)

def completedAdicKoszulTensorStep (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    completedAdicKoszulTensor T d r a C (m + 1) ⟶ completedAdicKoszulTensor T d r a C m

def completedAdicKoszulTensorUnitF (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) (p : ℤ) :
    C.X p ⟶ (completedAdicKoszulTensor T d r a C m).X p

theorem completedAdicKoszulTensorUnitF_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)
    (m : ℕ) (p q : ℤ) (_hpq : (ComplexShape.up ℤ).Rel p q) :
    completedAdicKoszulTensorUnitF T d r a C m p ≫
        (completedAdicKoszulTensor T d r a C m).d p q =
      C.d p q ≫ completedAdicKoszulTensorUnitF T d r a C m q

def completedAdicKoszulTensorUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    C ⟶ completedAdicKoszulTensor T d r a C m

def completedAdicKoszulProduct (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)

def completedAdicKoszulOneSubShift (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    completedAdicKoszulProduct T d r a C ⟶ completedAdicKoszulProduct T d r a C

def completedAdicKoszulFibre (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    CochainComplex (CompletedAdicModules T d) ℤ

def completedAdicKoszulProductUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    C ⟶ completedAdicKoszulProduct T d r a C

theorem completedAdicKoszulUnitF_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)
    (p q : ℤ) (_hpq : (ComplexShape.up ℤ).Rel p q) :
    ((completedAdicKoszulProductUnit T d r a C).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
        p (p + (-1)) (by change p + (-1) + 1 = p; omega)) ≫
        (completedAdicKoszulFibre T d r a C).d p q =
      C.d p q ≫ (completedAdicKoszulProductUnit T d r a C).f q ≫
        HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
          q (q + (-1)) (by change q + (-1) + 1 = q; omega)

def completedAdicKoszulUnitComplex (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    C ⟶ completedAdicKoszulFibre T d r a C

def completedAdicIntrinsicCompletion (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d)) :
    DerivedCategory (CompletedAdicModules T d)

def completedAdicIntrinsicUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d)) :
    K ⟶ completedAdicIntrinsicCompletion T d r a K

def IsCompletedAdicDerivedComplete (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (_ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (CompletedAdicModules T d)) : Prop
```

## New

Exactly the same public headers, universes, attributes, visibility and definition bodies
are in `Sheaf.Paper.CompletedAdicKoszulConstruction`. The old module publicly imports
that module and retains `completedAdicIntrinsicCompletion_comparison` with its unchanged
signature. No declaration is withdrawn or renamed, and no source-library file is changed.
The precise moved source is the new construction module, whose public declaration list
is also recorded in node `lem-weil-pbc-completed-adic-koszul-unit-chain-map`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedAdicIntrinsicCompletion | J1 | Construction imported publicly; comparison proved here. |
| Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones | not adapted | API preserved; original compiled against delivery. |
| Sheaf.Paper.CompletedAdicKoszulKFlat | not adapted | API preserved; original compiled against delivery. |
| Sheaf.Paper.KoszulReconstructionModels | not adapted | API preserved; original compiled against delivery. |
| Sheaf.Paper.FinitePerfectQuotientModels | not adapted | API preserved; original compiled against delivery. |
| Sheaf.Paper.ResidueLissePerfectLift | not adapted | API preserved; original compiled against delivery. |

## Status

landed 20261026T222717-L-685418 2026-10-26 (merge of deliver/J1/Sheaf.Paper.CompletedAdicIntrinsicCompletion)
