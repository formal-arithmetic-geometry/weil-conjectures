# WeilConjectures.FiniteHomNuChainTensorNormalization

## Reason

The old normalization repeatedly elaborates the sections of an explicitly
expanded signed total tensor. Replace it by the equivalent equation on its
summand maps, using the natural ordinary comparison normalized on pure sections.
The complexes and comparison isomorphism remain the predicate's arguments, now
inferred from the generic API. The tensor-existence instances are inferred from
the published canonical instances and are propositions; the predicate is
independent of their proofs. The termwise functor also receives an explicit
annotation of its existing inferred type. No target statement is
changed, and the canonical map remains determined by the same normalization.

For the forward implication from the new predicate, fix the ordinary normalized
natural tensor comparison e supplied by the predicate. Evaluate its total
summand equation on the image of an etale sheaf pure tensor under the two
comparison units. Naturality of those units identifies the left side with the
chain map on the image of the etale total inclusion. The ordinary normalization
identifies the right side with the intrinsic tensor of the two compared sections,
then its total inclusion. By the existing representative-data generator theorem,
the etale total inclusion is the recorded `finiteHomEtaleTotalSection`. The
intrinsic inclusion is exactly `coefficientTensorGenerator`. Choose the three
sections specified by the old existential witnesses; their first three equalities
are reflexive and the final equality is the one just obtained.

Conversely, first eliminate the old witnesses by their heterogeneous equalities.
Choose the ordinary normalized natural tensor comparison from
`finiteCoefficientIntrinsicTensor_generators`; its pure-section normalization
uniquely determines it. For each degree summand, compare the two maps obtained
by composing the chain map after the image of the etale inclusion, or composing
the ordinary comparison before the intrinsic inclusion. Apply the scalar module
sheafification adjunction, then the etale-to-pro-etale adjunction. Equality of
these maps reduces to equality on etale sheaf tensor generators, by sheaf tensor
extensionality and the sectionwise module tensor universal property. On every
pure section, the old normalization, the representative-data formula and the
ordinary normalization give precisely the same intrinsic total generator. Thus
the summand maps are equal, as required by the new predicate.

This includes every degree and section, empty schemes, zero complexes and the
zero coefficient ring. No boundedness, flatness or further hypotheses enter.

## Old

```lean
def FiniteHomNuChainTensorNormalization (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (e : (finiteHomNuComplex l E X n).obj (HomologicalComplex.tensorObj P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q)) : Prop :=
  ∀ (p q k : ℤ) (h : p + q = k) (U : X.Etale)
  (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)),
  ∃ (x' : (((finiteHomNuComplex l E X n).obj P).X p).val.obj (op (X.toProEt.obj U)))
    (y' : (((finiteHomNuComplex l E X n).obj Q).X q).val.obj (op (X.toProEt.obj U)))
    (z : (((finiteHomNuComplex l E X n).obj
      (HomologicalComplex.tensorObj P Q)).X k).val.obj (op (X.toProEt.obj U))),
    HEq x' (finiteHomNuSection l E X n (P.X p) U x) ∧
    HEq y' (finiteHomNuSection l E X n (Q.X q) U y) ∧
    HEq z (finiteHomNuSection l E X n ((HomologicalComplex.tensorObj P Q).X k) U
      (finiteHomEtaleTotalSection l E X n P Q p q k h U x y)) ∧
    HEq (((e.hom.f k).val.app (op (X.toProEt.obj U))) z)
      (coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((finiteHomNuComplex l E X n).obj P) ((finiteHomNuComplex l E X n).obj Q)
        p q k h (op (X.toProEt.obj U)) x' y')
```

## New

```lean
def FiniteHomNuChainTensorNormalization (n : ℕ) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  ProEtale.FiniteCoefficientChainTensorNormalization.{u} X
    (Padic.coefficientExtensionRing l E (n + 1))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | A4 | Equivalent normalization; theorem proved and canonical choice retained. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Uses only the canonical isomorphism, with the identical type. No adaptation needed. |

The sole direct importer is `FiniteCoefficientSiteHomArrow`. It does not
unfold the normalization or inspect its witnesses. The library search finds no
external reference to `FiniteHomNuChainTensorNormalization`. All target statements
remain verbatim. Targets depending on the canonical comparison should have the
usual definition review reopened, with the equivalence argument above.

## Status

landed 20261022T002344-L-1920030 2026-10-22 (merge of deliver/A4/Sheaf.Paper.FiniteCoefficientSiteChainTensor)
