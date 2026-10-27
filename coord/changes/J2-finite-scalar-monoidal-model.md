# WeilConjectures.PurityFiniteSetting.finiteScalarMonoidalModel

## Reason

Construct an actual monoidal scalar model using the native total left derived functor
and its canonical comparison of left adjoints. No unproved existence assertion supplies
data. The remaining lemma is only the full representative equation for this fixed model;
the original module proves existence and the complete uniqueness argument from it.

## Old

These two declarations and their modules were absent.

## New

```lean
@[irreducible] def finiteScalarMonoidalModel {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CoreMonoidal := by
  letI : Algebra A B := φ.toAlgebra
  let F := ProEtale.sheafExtendScalars φ T
  letI : F.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  letI : F.leftDerivedFunctor.Monoidal :=
    F.leftDerivedFunctorMonoidal
  let a : F.leftDerivedFunctor ⊣
      ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T :=
    ProEtale.leftDerivedSheafExtendScalarsAdjunction A B T
  let b := Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  exact Functor.Monoidal.coreMonoidalTransport (a.leftAdjointUniq b)
```

The only new theorem left with `sorry` is:

```lean
theorem finiteScalarMonoidalModel_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (finiteScalarTensorData φ T).source C D =
      ((finiteScalarMonoidalModel φ T).μIso
        (_root_.DerivedCategory.Q.obj C) (_root_.DerivedCategory.Q.obj D)).inv ≫
          (finiteScalarTensorData φ T).tail C D
```

The source and tail fields of `finiteScalarTensorData` are the entire original
scalar-first cochain representative square. The independent definition repair record
is `coord/changes/J2-tensor-representative-data.md`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteScalarMonoidalModel | J2, new | Constructs actual data using proved native APIs. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | J2, new | States the full counit equation for that fixed tensorator. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | Uses that equation to prove existence and proves uniqueness by cancellation and K-flat density. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed (Y7 landed 2026-10-26) | Uses native braided transport of this same model, then normalized-core uniqueness. |

The assigned item and adapted symmetry consumer are the new users. Their public
theorem signatures and
original public imports stay verbatim. The existing chosen core definition keeps its
body. Its normalization predicate projects the identical actual diagram, as separately
recorded. The signed-line theorem uses a generic proved nested-uniqueness assembly with
exactly its former ordinary and pointwise derived inputs. Its signature and argument
stay the same. Local irreducibility of chosen data and ordinary concurrent checking
replace the item's former `Elab.async false` restriction. The normalization and native
cochain interfaces and necessary symmetry consumer adaptation are recorded separately
in the other four change records, including the complete pointwise-predicate
interface for the two existing signed-line consumers; no adopted source module is edited.

## Status

landed 20261026T070008-L-3329438 2026-10-26 (merge of deliver/J2/Sheaf.Paper.FiniteTensorSignedReduction)
