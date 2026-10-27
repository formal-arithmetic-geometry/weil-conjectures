# AlgebraicGeometry.ProEtale.lisseLattice_constant_reductions

## Reason

Preflight classifies the added module commands as a visibility change. The public
signature and all original public imports are unchanged. The added declarations are
private and fully proved; their definitions construct only the objects in this proof.
The local irreducibility attributes prevent expensive unfolding of free coproducts
and tensor coordinate equivalences during elaboration. They are local to this file.
The transparency option affects elaboration in this file, not theorem meaning.
No definition used by a target changes, so no target statement review is reopened.

The only private import additions are the existing coefficient quotient API,
Mathlib.LinearAlgebra.TensorProduct.Pi, and proof-only `import all` imports of
Sheaf.SixFunctors.IntegralLisseTowerLocalBases and
Sheaf.SixFunctors.IntegralLisseTowerEffective. The last two imports reuse four
existing proved private lemmas, resolving the duplicate-declaration return at
`77f2b9e5136`; no source file of those lemmas is changed.
The report lists the four removed private imports. No additional module sees those
private imports. The independent reader can inspect the local commands below and
compare the repeated public signature verbatim.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
```

```lean
theorem lisseLattice_constant_reductions
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : IntegralLisseModule l E X) (d : ℕ)
    (hconstant : ∀ n : ℕ, Nonempty
      (integralLisseCokernel l E X N.obj n ≅
        integralLisseCokernel l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))) n))
    (b1 : integralLisseCokernel l E X N.obj 0 ≅
      integralLisseCokernel l E X
        (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))) 0) :
    ∃ (B : integralLisseCokernelTower l E X N.obj ≅
        integralLisseCokernelTower l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))))
      (b : N.obj ≅
        SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d)))
      (bE : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (lisseIntegerToFieldSized l E X) N.obj ≅
        SheafOfModules.free
          (R := (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X))
          (ULift.{u + 1} (Fin d))),
      B.app (op 0) = b1 ∧
      (∀ n : ℕ, ((integralLisseCokernelFunctor l E X).mapIso b).app (op n) = B.app (op n)) ∧
      ∀ (U : X.ProEtᵒᵖ) (s : (lisseFieldSheafSized l E X).obj.obj U)
        (x : N.obj.val.obj U) (i : ULift.{u + 1} (Fin d)),
        (SheafOfModules.freeπ
          (R := (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X))
          i).val.app U
            (bE.hom.val.app U
              (((PresheafOfModules.sheafificationAdjunction
                (R := (sheafCompose (Scheme.ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                    (lisseFieldSheafSized l E X)) (𝟙 _)).unit.app
                      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
                        (lisseIntegerToFieldSized l E X) N.obj)).app U
                          (s ⊗ₜ[(lisseIntegerSheafSized l E X).obj.obj U,
                            ((lisseIntegerToFieldSized l E X).hom.app U).hom] x))) =
          s * (lisseIntegerToFieldSized l E X).hom.app U
            ((SheafOfModules.freeπ i).val.app U (b.hom.val.app U x))
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] SheafOfModules.free

universe u
```

Later, after proving the sectionwise coordinate formula:

```lean
attribute [local irreducible] tensorSection SheafOfModules.freeSectionsLinearEquiv
```

The private helpers use a `section` and `section Rationalization`, each closed before
the public theorem; their section variables do not alter its binders.

```lean
theorem lisseLattice_constant_reductions
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : IntegralLisseModule l E X) (d : ℕ)
    (hconstant : ∀ n : ℕ, Nonempty
      (integralLisseCokernel l E X N.obj n ≅
        integralLisseCokernel l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))) n))
    (b1 : integralLisseCokernel l E X N.obj 0 ≅
      integralLisseCokernel l E X
        (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))) 0) :
    ∃ (B : integralLisseCokernelTower l E X N.obj ≅
        integralLisseCokernelTower l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))))
      (b : N.obj ≅
        SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d)))
      (bE : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (lisseIntegerToFieldSized l E X) N.obj ≅
        SheafOfModules.free
          (R := (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X))
          (ULift.{u + 1} (Fin d))),
      B.app (op 0) = b1 ∧
      (∀ n : ℕ, ((integralLisseCokernelFunctor l E X).mapIso b).app (op n) = B.app (op n)) ∧
      ∀ (U : X.ProEtᵒᵖ) (s : (lisseFieldSheafSized l E X).obj.obj U)
        (x : N.obj.val.obj U) (i : ULift.{u + 1} (Fin d)),
        (SheafOfModules.freeπ
          (R := (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X))
          i).val.app U
            (bE.hom.val.app U
              (((PresheafOfModules.sheafificationAdjunction
                (R := (sheafCompose (Scheme.ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                    (lisseFieldSheafSized l E X)) (𝟙 _)).unit.app
                      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
                        (lisseIntegerToFieldSized l E X) N.obj)).app U
                          (s ⊗ₜ[(lisseIntegerSheafSized l E X).obj.obj U,
                            ((lisseIntegerToFieldSized l E X).hom.app U).hom] x))) =
          s * (lisseIntegerToFieldSized l E X).hom.app U
            ((SheafOfModules.freeπ i).val.app U (b.hom.val.app U x))
```

## Users

`python3 tools/downstream.py Sheaf.Paper.LisseLatticeConstantReductions --uses
lisseLattice_constant_reductions` reports zero downstream modules and only the item's
own declaration as a textual use. This is not a withdrawal: the pending parent DAG
argument still needs this node, and its attachment is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseLatticeConstantReductions | Y8 | The public theorem is proved with the same signature; added helper declarations and irreducibility attributes are private/local. |

No consumer adaptation is necessary or delivered.

## Status

landed 20261023T152146-L-456502 2026-10-23 (merge of deliver/Y8/Sheaf.Paper.LisseLatticeConstantReductions)
