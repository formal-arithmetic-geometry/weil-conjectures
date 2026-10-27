# SystemProperOpenScalarSquare construction extraction

## Reason

The remaining theorem requires two independently provable inverse-image coherence
lemmas. They must refer to the existing scalar constructions without importing the
item theorem and creating an import cycle. Extract those constructions verbatim
into SystemProperOpenScalarData and publicly reexport them from the item.

## Old

The file lean/Sheaf/SixFunctors/SystemProperOpenScalarSquare.lean contains the
construction declarations levelMap through beta, followed by:

```lean
theorem systemProperOpenScalarSquare :
    (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived A a U),
      (T A B a b φ hφ d hd e Z).map ((gamma A a k r p i h).app M) ≫
          (chi A B a b φ hφ d hd e p).app ((J A a k).obj M) ≫
          (R B b p).map ((beta A B a b φ hφ d hd e k).hom.app M) =
        (beta A B a b φ hφ d hd e i).hom.app ((R A a r).obj M) ≫
          (J B b i).map ((chi A B a b φ hφ d hd e r).app M) ≫
          (gamma B b k r p i h).app ((T A B a b φ hφ d hd e U).obj M)) ∧
    (∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z) (M : Derived A a X),
      (T A B a b φ hφ d hd e Z).map ((sComp A a v w).hom.app M) ≫
          (chi A B a b φ hφ d hd e (v ≫ w)).app M =
        (chi A B a b φ hφ d hd e w).app ((R A a v).obj M) ≫
          (R B b w).map ((chi A B a b φ hφ d hd e v).app M) ≫
          (sComp B b v w).hom.app ((T A B a b φ hφ d hd e X).obj M)) ∧
    (∀ (X : Scheme.{u}) (M : Derived A a X),
      (chi A B a b φ hφ d hd e (𝟙 X)).app M ≫
          (sId B b X).hom.app ((T A B a b φ hφ d hd e X).obj M) =
        (T A B a b φ hφ d hd e X).map ((sId A a X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (v : X ⟶ Y),
      NatTrans.CommShift (ell A B a b φ hφ d hd e v).hom ℤ ∧
        NatTrans.CommShift (chi A B a b φ hφ d hd e v) ℤ) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
      NatTrans.CommShift (beta A B a b φ hφ d hd e j).hom ℤ) ∧
    (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      NatTrans.CommShift (gamma A a k r p i h) ℤ ∧
        NatTrans.CommShift (gamma B b k r p i h) ℤ)
```

Its public imports are:

```lean
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.DiagramOpenClopenShiftModels
public import Mathlib.LinearAlgebra.Basis.Defs
```

## New

The original four public imports remain explicitly in the item, followed by:

```lean
public import Sheaf.SixFunctors.SystemProperOpenScalarData
```

SystemProperOpenScalarData contains exactly the former construction declarations,
with identical public names, signatures, instances, and bodies. It retains all four
old public imports, so the item's public reexports are preserved transitively.
No mathematical definition or statement changes. In the node
lem-sf-system-proper-open-scalar-square, stmt_deps gains the construction owner
def-sf-system-finite-free-scalar-data and lean.declarations now lists only the
item theorem; the extracted construction declarations are attached to the new
owner instead. The node statement is unchanged. This dependency/attachment
repair is the metadata change flagged as a statement change by preflight. The former private helper
model_limits_of_flat is renamed scalarModel_limits_of_flat in the data module;
the item retains model_limits_of_flat, with its identical signature and a proved
forwarding body, because an existing consumer imports it using import all.
The item theorem's signature is identical. Its proof reduces to the intrinsic
inverse-image alpha cube and composition/identity coherence for ell, followed by
mate calculus; the shift clauses use existing exact-functor APIs.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in the local claim scan | Same public declarations and reexports; no adaptation needed. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed in the local claim scan | Same public declarations and reexports; the private model_limits_of_flat entry point is also retained verbatim in type. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed in the local claim scan | Indirect user of calculus, E and T through EtaleSystemScalarMateCoherence; their types and bodies are unchanged. |

The first two rows are all direct importers of the item. No other existing module is
changed. Both unchanged direct consumers compiled successfully against this extraction;
validation is recorded in report.md. Their temporary copies were removed.

## Status

landed 20261027T021254-L-2751689 2026-10-27 (merge of deliver/A2/Sheaf.SixFunctors.SystemProperOpenScalarSquare)
