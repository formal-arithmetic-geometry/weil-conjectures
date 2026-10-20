# AlgebraicGeometry.VectorBundleZeroSection.algebraIso

## Reason

The original definition exposes a `Classical.choose` from a large dependent
existential every time its structure-algebra functor is reduced. Profiling isolated
repeated dependent conversions in the zero-section section calculation, and the
complete proof exceeded the 60-second check. The replacement constructs that
functor on objects and section maps and proves it is an equivalence by the object
and morphism characterizations of `affine_morphism_relative_spec`. Its chosen
quasi-inverse is a genuine inverse, uniquely determined up to algebra-compatible
isomorphism. No existence-only arbitrary geometric object is introduced.

The module still constructs `Spec_S Sym(F)`, with the same augmentation and
fully faithful inverse image defining the zero section. All existing public
signatures remain identical. The concrete choice of quasi-inverse can change;
this is a representation repair, not a claim of literal equality of chosen
schemes. The algebra-compatible isomorphism preserves the projection,
augmentation, charts, frame coordinates, and their transition formulas. The
meaning review of targets using these definitions must therefore be reopened;
their Lean statements and mathematical strength are unchanged.

The functor now returns the structure algebra definitionally, so the mapped
inverse counit already has the required codomain; the old object-equality cast
is unnecessary.

## Old

```lean
def algebraIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    SymmetricAlgebraSheaf.algebra F ≅
      Under.mk (⟨(π S d F).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (π S d F).base).obj
          (scheme S d F).sheaf) :=
  ((ObjectProperty.ι (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((antiEquivalence S).counitIso.app (algebraObject S d F))).symm ≪≫
      eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose (over S d F))
```

## New

```lean
def algebraIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    SymmetricAlgebraSheaf.algebra F ≅
      Under.mk (⟨(π S d F).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (π S d F).base).obj
          (scheme S d F).sheaf) :=
  ((ObjectProperty.ι (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((antiEquivalence S).counitIso.app (algebraObject S d F))).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | N3 | Same relative-spectrum universal property; signature unchanged. |

## Status

landed 20261020T211804-L-3502452 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.VectorBundleZeroSection)
