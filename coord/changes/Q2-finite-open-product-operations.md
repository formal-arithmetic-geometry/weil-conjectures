# WeilConjectures.FiniteOpenProduct.proetSigma and the finite-open operations module

## Reason

The original module mixes the concrete operations with the theorem about them.
Its planned proof dependencies TwoOpenTensorChainNormalization and
SupportedTensorIsomorphismTransport publicly import it, so the theorem cannot import
them without a cycle. Extract the original operations into a standalone module and
publicly reexport it from the original module, preserving every existing name and
signature. The two smaller calculation modules can import the operations without
importing the theorem they are used to prove. No source-library file changes.

The raw leftDerived₂Lift expression in proetSigma also makes instance synthesis of
its invertibility exceed the compile limit. Replace it by the native named braiding
from DerivedCategoryBraided. This is the same construction: braidedCategory'.braiding
is DerivedMonoidal.braiding'; its hom is braidingNatTrans applied at N then M;
braidingNatTrans is the leftDerived₂Lift of braidingCounit. Expanding braidingCounit
and counit gives exactly the original mu, W and tau expression. This names the
existing isomorphism instead of reconstructing its hom. Tensor, sign, orientation,
coefficients and all hypotheses are preserved. In particular this is not an
arbitrary braiding instance: the definition explicitly names the K-flat native one.

The target closure uses these definitions, so the independent statement review
should confirm this definitional presentation change preserves their meaning.
No target declaration text changes. Moving the definitions changes their owning
module; the original public module reexports every original public import and name.

## Old

```lean
def proetSigma (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalClosed V]
    [MonoidalPreadditive V] [SymmetricCategory V] [Abelian.HasFunctorialFlatResolution V]
    (Y : Scheme.{u}) (M N : DerivedCategory (Sheaf (ProEt.topology Y) V)) :
    ((ProEtale.derivedTensor V Y).obj M).obj N ⟶
      ((ProEtale.derivedTensor V Y).obj N).obj M :=
  let μ := Functor.LaxMonoidal.μNatTrans
    (DerivedCategory.Qh (C := Sheaf (ProEt.topology Y) V))
  let W := HomotopyCategory.quasiIso (Sheaf (ProEt.topology Y) V) (.up ℤ)
  let τ := (ProEtale.derivedTensor V Y).leftDerived₂Lift μ W W
    (ProEtale.derivedTensor V Y).flip
    ((flipFunctor _ _ _).map μ ≫
      Functor.whiskerRight ((flipFunctor _ _ _).map
        (BraidedCategory.curriedBraidingNatIso
          (HomotopyCategory (Sheaf (ProEt.topology Y) V) (.up ℤ))).hom)
        ((Functor.whiskeringRight
          (HomotopyCategory (Sheaf (ProEt.topology Y) V) (.up ℤ))
          (HomotopyCategory (Sheaf (ProEt.topology Y) V) (.up ℤ))
          (DerivedCategory (Sheaf (ProEt.topology Y) V))).obj DerivedCategory.Qh))
  (τ.app N).app M
```

All public operations were declared directly in
lean/Sheaf/Paper/FiniteOpenProductSwap.lean.

## New

```lean
def proetSigma (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalClosed V]
    [MonoidalPreadditive V] [SymmetricCategory V] [Abelian.HasFunctorialFlatResolution V]
    (Y : Scheme.{u}) (M N : DerivedCategory (Sheaf (ProEt.topology Y) V)) :
    ((ProEtale.derivedTensor V Y).obj M).obj N ⟶
      ((ProEtale.derivedTensor V Y).obj N).obj M :=
  (DerivedCategory.braidedCategory' (Sheaf (ProEt.topology Y) V)).braiding M N |>.hom
```

The operations are declared in lean/Sheaf/Paper/FiniteOpenProductOperations.lean.
The original module starts with:

```lean
public import Sheaf.Paper.FiniteOpenProductOperations
```

Every other moved declaration has its original signature and body verbatim.
The original theorem has its original signature verbatim and a complete proof
from two strictly smaller restriction calculations.

## Users

The table is the complete downstream.py output for the original module. Direct
textual use of proetSigma is only inside that module. tensor and the other public
operations remain visible to all of these consumers. Existing signatures and
canonical morphisms do not change. No consumer module is adapted in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTripleProductNormalForms | D4 | Same names and types through the public reexport; no edit needed. |
| Sheaf.Paper.ProductOpenTensorProjection | H5 | Same names and types through the public reexport; no edit needed. |
| Sheaf.Paper.SupportedTensorIsomorphismTransport | R6 | Same names and types through the public reexport; no edit needed. |
| Sheaf.Paper.TwoOpenTensorChainNormalization | S5 | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.OpenNormalizedProductCoherence | unclaimed | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Same names and types through the public reexport; no edit needed. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | Same names and types through the public reexport; no edit needed. |

## Status

landed 20261025T205537-L-3284109 2026-10-25 (merge of deliver/Q2/Sheaf.Paper.FiniteOpenProductSwap)
