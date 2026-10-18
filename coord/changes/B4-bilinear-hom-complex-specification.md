# CategoryTheory.ProductHomComplexSpecification

## Reason

Package the product, differential and chain-map formulas of the new generic Hom-complex
construction as a proposition. Directly specializing these expanded formulas to sheaves
of modules caused typeclass elaboration to exceed its standard heartbeat budget while
inferring the integer-unit action on morphisms. The proposition keeps the generic
preadditive structures abstract during specialization; no limit is increased.

## Old

No declaration named `CategoryTheory.ProductHomComplexSpecification` existed.

## New

The following explicit proposition specifies a given bifunctor with all three formulas. It
contains no proof hole and chooses no data. Its existence theorem constructs every witness.
Keeping the bifunctor as an argument also permits comparing the constructed coefficient
complex with the existing chosen Hom complex while retaining its complete specification.

```lean
def ProductHomComplexSpecification
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ) : Prop :=
      ∃ π : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
        (((F.obj (op L)).obj M).X n ⟶ (H.obj (op (L.X p))).obj (M.X q)),
        (∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
            (fun p : ℤ ↦ π L M n p (p + n) rfl)))) ∧
        (∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n m p q q' p' : ℤ)
          (_hnm : n + 1 = m) (hpq : p + m = q)
          (hq' : p + n = q') (hp' : p' + n = q),
          ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
            π L M n p q' hq' ≫ (Functor.uncurry.obj H).map
                (X := (op (L.X p), M.X q')) (Y := (op (L.X p), M.X q))
                ((𝟙 (L.X p)).op, M.d q' q) -
              n.negOnePow • (π L M n p' q hp' ≫
                (Functor.uncurry.obj H).map
                  (X := (op (L.X p'), M.X q)) (Y := (op (L.X p), M.X q))
                  ((L.d p p').op, 𝟙 (M.X q)))) ∧
        (∀ (L L' : CochainComplex A ℤ) (M M' : CochainComplex B ℤ) (f : L' ⟶ L) (g : M ⟶ M')
          (n p q : ℤ) (hpq : p + n = q),
          (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
            π L M n p q hpq ≫ (Functor.uncurry.obj H).map
              (X := (op (L.X p), M.X q)) (Y := (op (L'.X p), M'.X q))
              ((f.f p).op, g.f q))
```

## Users

No existing module uses this new declaration. All consumers are included in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BilinearHomComplex | new, B4 | Constructs the specified complex bifunctor. |
| Sheaf.Paper.RestrictedCoefficientHomComplex | new, B4 | Specializes to coefficient Homs of module sheaves. |

## Status

landed 20261018T103529-L-18130 2026-10-18 (merge of deliver/B4/Sheaf.Paper.FlatRingedIdealCompleteEquivalence)
