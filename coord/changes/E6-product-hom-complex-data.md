# CategoryTheory.ProductHomComplexSpecification

## Reason

The complete coefficient-Hom unit proof exceeded the per-file time limit, with
most time in kernel checks that repeatedly substituted the concrete coefficient
categories into the large existential specification. Store the data in a named
structure with separate fields, so a use of a projection does not expose the
entire conjunction of its three laws. This is the structure representation fix
requested by the compile-time rule, not a split of the proof between files.
Both existing modules changed here are unclaimed at the time of the change.

## Old

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

## New

```lean
structure ProductHomComplexData [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ) where
  π : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj M).X n ⟶ (H.obj (op (L.X p))).obj (M.X q))
  isLimit : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n : ℤ),
    Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
      (fun p : ℤ ↦ π L M n p (p + n) rfl)))
  differential : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ)
    (n m p q q' p' : ℤ) (_hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q),
    ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ (Functor.uncurry.obj H).map
        (X := (op (L.X p), M.X q')) (Y := (op (L.X p), M.X q))
        ((𝟙 (L.X p)).op, M.d q' q) -
      n.negOnePow • (π L M n p' q hp' ≫ (Functor.uncurry.obj H).map
        (X := (op (L.X p'), M.X q)) (Y := (op (L.X p), M.X q))
        ((L.d p p').op, 𝟙 (M.X q)))
  naturality : ∀ (L L' : CochainComplex A ℤ) (M M' : CochainComplex B ℤ)
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q),
    (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
      π L M n p q hpq ≫ (Functor.uncurry.obj H).map
        (X := (op (L.X p), M.X q)) (Y := (op (L'.X p), M'.X q))
        ((f.f p).op, g.f q)

/-- Product projections, differential, and functoriality specifying a product Hom complex.
Source: Stacks Project, Algebraization, Tag 099I; sites-cohomology.tex, Section 0A8X
(blueprint: lem-weil-pbc-bilinear-hom-complex).
This proposition packages the full formulas so coefficient specializations can use the
abstract preadditive hom structures without re-elaborating them after substitution. -/
def ProductHomComplexSpecification [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ) : Prop :=
  Nonempty (ProductHomComplexData H F)
```

`productHomComplexSpecification_iff` proves equivalence with the former
existential proposition, copied verbatim as its right side. Its proof packs and
unpacks the same four fields. All conditions, quantifiers, equations and signs
are retained. The existence theorem supplies the same explicit `homProj` and
its same three proved properties, now inside the structure. No data is obtained
from an unproved existence theorem, and no holes are introduced.

The data and specification need only zero morphisms in the two source
categories; preadditivity remains required in the output category, where the
differential formula uses subtraction and integer scalar multiplication. Their
new explicit `HasZeroMorphisms A` and `HasZeroMorphisms B` parameters replace
the previously inherited preadditive source parameters. Under the original
preadditive assumptions the same canonical zero morphisms are supplied, and
the displayed equivalence proves exactly the former condition. The private
unit-chain proof can consequently use only zero morphisms in its restriction
target, avoiding unused additive structures in that interface.

The declaration text of `exists_bilinearHomComplexFunctor` is unchanged.
The existing consumer `RestrictedCoefficientHomComplex` now reads the named
fields of `Classical.choice hG`. Its private comparison retains the projection
normalization that its existing proof already established, and uses the named
Hom bifunctor in place of a large local functor definition. The public theorem's
signature is unchanged. The assigned unit module reuses this normalized private
comparison and reads the same structured projection fields.
See `E6-normalized-coefficient-comparison.md` for the strengthened private interface.
No adopted source-library file is changed.

Any target statement using the changed specification through its definitions
requires renewed statement review under the definition-change rule. The exact
Lean equivalence certifies that its meaning is preserved. The statement of the
assigned coefficient-Hom unit theorem is byte-identical and does not mention
this specification.

The two consuming private proofs take `ProductHomComplexData` directly. Their
public existence proofs unpack the `Nonempty` specification once and retain
the existing public statements. In particular, comparison and unit maps use
the same explicit projection data rather than separately choosing witnesses.

## Users

The table includes every module printed by
`python3 -B tools/downstream.py Sheaf.Algebra.Homology.BilinearHomComplex --uses ProductHomComplexSpecification`
and the new consumer in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BilinearHomComplex | unclaimed | Structured data; exact equivalence certificate; explicit existence proof repackaged. |
| Sheaf.Paper.RestrictedCoefficientHomComplex | unclaimed | Named data fields; retain the private comparison normalization; remove the large local Hom-functor definition. Public signature unchanged. |
| Sheaf.Paper.CoefficientHomUnit | E6 | Proved the assigned theorem; named projections avoid repeatedly unfolding the specification. |

## Status

landed 20261026T111828-L-1744881 2026-10-26 (merge of deliver/E6/Sheaf.Paper.CoefficientHomUnit)
