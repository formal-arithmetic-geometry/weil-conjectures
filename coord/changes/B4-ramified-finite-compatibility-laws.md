# WeilConjectures.RamifiedScalarSystemTranspose.FiniteCompatibility

## Reason

The dependent record mixed the finite Change data and six large equality laws.
Sequential profiling found repeated kernel expansion while generating its projections
and recursor. Separating the proof-only part into a Prop structure reduced the main
file's declaration-checking cost. Artifact serialization is also a substantial part of the measured compile time. This changes the
representation of the definition, without changing any compatibility equation or
which Change data those equations constrain. It adds no assumption or proof hole.

## Old

```lean
structure FiniteCompatibility
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F) where
  change : ∀ n : ℕ,
    Change (inclusion l E L i n) c (rR.finite n) (rS.finite n)
  /-- The finite comparison is the specified proper/open map, on every finite input. -/
  canonical : ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory),
    (change n).projection.hom.app K = (finiteComparison l E L i c n).app K.obj
  /-- Evaluation of the whole-system map is precisely this finite comparison. -/
  comparison_evaluation : ∀ (n : ℕ)
    (M : (domain (lowerRings l E) (lowerMaps l E) X).FullSubcategory),
    (level (upperRings l E L i) (upperMaps l E L i) Y n).map
        ((α.hom.app M).hom) ≫
        ((rS.left n).hom.app ((T l E L i X).obj M)).hom ≫
        (lower (upperRings l E L i n) c).map
          ((scalarEvaluation l E L i X n).hom.app M.obj) =
      (scalarEvaluation l E L i Y n).hom.app (rR.F.obj M).obj ≫
        (tensor (inclusion l E L i n) Y).map (((rR.left n).hom.app M).hom) ≫
        (change n).projection.hom.app
          ((evaluation (lowerRings l E) (lowerMaps l E) X n).obj M)
  /-- Evaluation is the finite exceptional counit transpose, with no faithfulness claim. -/
  transpose_evaluation : ∀ (n : ℕ)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory),
    evaluatedTranspose l E L i c rR rS α n N =
      (change n).mate.hom.app
        ((evaluation (lowerRings l E) (lowerMaps l E) Y n).obj N)
  /-- Every finite coefficient square commutes, including its specified quotient maps. -/
  comparison_quotient : ∀ {m n : ℕ} (h : n ≤ m)
    (K : (ctf (lowerRings l E m) X).FullSubcategory),
    (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom Y).map
        ((change m).projection.hom.app K) ≫
        (rS.quotient h).projection.hom.app
          ⟨(tensor (inclusion l E L i m) X).obj K.obj,
            (change m).tensor_preserves_X K.obj K.property⟩ ≫
        (lower (upperRings l E L i n) c).map
          ((reassociate l E L i X h).hom.app K.obj) =
      (reassociate l E L i Y h).hom.app ((lower (lowerRings l E m) c).obj K.obj) ≫
        (tensor (inclusion l E L i n) Y).map ((rR.quotient h).projection.hom.app K) ≫
        (change n).projection.hom.app
          ⟨(tensor (quotientMap (lowerRings l E) (lowerMaps l E) h).hom X).obj K.obj,
            (rR.quotient h).tensor_preserves_X K.obj K.property⟩
  /-- In every reduction of a single integral basis, the underlying finite map is
  finite-sum distributivity, characterized on each canonical summand inclusion. -/
  finite_sum : ∀ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L),
    Function.Bijective (fun a : Fin d → Padic.coefficientExtensionIntegers l E ↦
      ∑ j, integralScalarIntegerInclusion l E L i (a j) * b j) →
    ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory) (j : Fin d),
      basisLeg l E L i Y n ((lower (lowerRings l E n) c).obj K.obj)
          (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j)) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y)
            (inclusion l E L i n)).map ((change n).projection.hom.app K) =
        (lower (lowerRings l E n) c).map
            (basisLeg l E L i X n K.obj
              (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j))) ≫
          (ProEtale.compactSupportRestrictionIso (inclusion l E L i n) c).hom.app
            ((tensor (inclusion l E L i n) X).obj K.obj)
  /-- The full explicit quotient square, with the retained upper quotient maps. -/
  quotient_square : ∀ {m n : ℕ} (h : n ≤ m)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory),
    (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom X).map
        (evaluatedTranspose l E L i c rR rS α m N) ≫
        (rS.quotient h).mate.hom.app
          ⟨(tensor (inclusion l E L i m) Y).obj
              ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj),
            (change m).tensor_preserves_Y _ (N.property.2 m)⟩ ≫
        (upper (upperRings l E L i n) c).map
          ((reassociate l E L i Y h).hom.app
              ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj) ≫
            (tensor (inclusion l E L i n) Y).map
              (red (lowerRings l E) (lowerMaps l E) Y h N.obj)) =
      (reassociate l E L i X h).hom.app
          ((upper (lowerRings l E m) c).obj
            ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj)) ≫
        (tensor (inclusion l E L i n) X).map
          ((rR.quotient h).mate.hom.app
              ((evaluation (lowerRings l E) (lowerMaps l E) Y m).obj N) ≫
            (upper (lowerRings l E n) c).map
              (red (lowerRings l E) (lowerMaps l E) Y h N.obj)) ≫
        evaluatedTranspose l E L i c rR rS α n N
```

## New

```lean
structure FiniteCompatibilityLaws
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F)
    (change : ∀ n : ℕ,
      Change (inclusion l E L i n) c (rR.finite n) (rS.finite n)) : Prop where
  /-- The finite comparison is the specified proper/open map, on every finite input. -/
  canonical : ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory),
    (change n).projection.hom.app K = (finiteComparison l E L i c n).app K.obj
  /-- Evaluation of the whole-system map is precisely this finite comparison. -/
  comparison_evaluation : ∀ (n : ℕ)
    (M : (domain (lowerRings l E) (lowerMaps l E) X).FullSubcategory),
    (level (upperRings l E L i) (upperMaps l E L i) Y n).map
        ((α.hom.app M).hom) ≫
        ((rS.left n).hom.app ((T l E L i X).obj M)).hom ≫
        (lower (upperRings l E L i n) c).map
          ((scalarEvaluation l E L i X n).hom.app M.obj) =
      (scalarEvaluation l E L i Y n).hom.app (rR.F.obj M).obj ≫
        (tensor (inclusion l E L i n) Y).map (((rR.left n).hom.app M).hom) ≫
        (change n).projection.hom.app
          ((evaluation (lowerRings l E) (lowerMaps l E) X n).obj M)
  /-- Evaluation is the finite exceptional counit transpose, with no faithfulness claim. -/
  transpose_evaluation : ∀ (n : ℕ)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory),
    evaluatedTranspose l E L i c rR rS α n N =
      (change n).mate.hom.app
        ((evaluation (lowerRings l E) (lowerMaps l E) Y n).obj N)
  /-- Every finite coefficient square commutes, including its specified quotient maps. -/
  comparison_quotient : ∀ {m n : ℕ} (h : n ≤ m)
    (K : (ctf (lowerRings l E m) X).FullSubcategory),
    (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom Y).map
        ((change m).projection.hom.app K) ≫
        (rS.quotient h).projection.hom.app
          ⟨(tensor (inclusion l E L i m) X).obj K.obj,
            (change m).tensor_preserves_X K.obj K.property⟩ ≫
        (lower (upperRings l E L i n) c).map
          ((reassociate l E L i X h).hom.app K.obj) =
      (reassociate l E L i Y h).hom.app ((lower (lowerRings l E m) c).obj K.obj) ≫
        (tensor (inclusion l E L i n) Y).map ((rR.quotient h).projection.hom.app K) ≫
        (change n).projection.hom.app
          ⟨(tensor (quotientMap (lowerRings l E) (lowerMaps l E) h).hom X).obj K.obj,
            (rR.quotient h).tensor_preserves_X K.obj K.property⟩
  /-- In every reduction of a single integral basis, the underlying finite map is
  finite-sum distributivity, characterized on each canonical summand inclusion. -/
  finite_sum : ∀ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L),
    Function.Bijective (fun a : Fin d → Padic.coefficientExtensionIntegers l E ↦
      ∑ j, integralScalarIntegerInclusion l E L i (a j) * b j) →
    ∀ (n : ℕ) (K : (ctf (lowerRings l E n) X).FullSubcategory) (j : Fin d),
      basisLeg l E L i Y n ((lower (lowerRings l E n) c).obj K.obj)
          (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j)) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y)
            (inclusion l E L i n)).map ((change n).projection.hom.app K) =
        (lower (lowerRings l E n) c).map
            (basisLeg l E L i X n K.obj
              (Ideal.Quotient.mk (upperStage l E L i n).ideal (b j))) ≫
          (ProEtale.compactSupportRestrictionIso (inclusion l E L i n) c).hom.app
            ((tensor (inclusion l E L i n) X).obj K.obj)
  /-- The full explicit quotient square, with the retained upper quotient maps. -/
  quotient_square : ∀ {m n : ℕ} (h : n ≤ m)
    (N : (domain (lowerRings l E) (lowerMaps l E) Y).FullSubcategory),
    (tensor (quotientMap (upperRings l E L i) (upperMaps l E L i) h).hom X).map
        (evaluatedTranspose l E L i c rR rS α m N) ≫
        (rS.quotient h).mate.hom.app
          ⟨(tensor (inclusion l E L i m) Y).obj
              ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj),
            (change m).tensor_preserves_Y _
              (((evaluation (lowerRings l E) (lowerMaps l E) Y m).obj N).property)⟩ ≫
        (upper (upperRings l E L i n) c).map
          ((reassociate l E L i Y h).hom.app
              ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj) ≫
            (tensor (inclusion l E L i n) Y).map
              (red (lowerRings l E) (lowerMaps l E) Y h N.obj)) =
      (reassociate l E L i X h).hom.app
          ((upper (lowerRings l E m) c).obj
            ((level (lowerRings l E) (lowerMaps l E) Y m).obj N.obj)) ≫
        (tensor (inclusion l E L i n) X).map
          ((rR.quotient h).mate.hom.app
              ((evaluation (lowerRings l E) (lowerMaps l E) Y m).obj N) ≫
            (upper (lowerRings l E n) c).map
              (red (lowerRings l E) (lowerMaps l E) Y h N.obj)) ≫
        evaluatedTranspose l E L i c rR rS α n N

/-- Finite comparison data together with all six proof-only compatibility laws.
Source: the finite-coordinate clauses of the node
(blueprint: lem-coef-ramified-scalar-system-transpose).
The proof-only package changes only the representation: its projections are the
same equalities, with exactly the same finite comparison data. -/
structure FiniteCompatibility
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F) where
  change : ∀ n : ℕ,
    Change (inclusion l E L i n) c (rR.finite n) (rS.finite n)
  laws : FiniteCompatibilityLaws l E L i c rR rS α change
```

The six old public accessor names canonical, comparison_evaluation,
transpose_evaluation, comparison_quotient, finite_sum and quotient_square are
proved projection aliases through laws. Their equality types and the change
projection are retained. The constructor now accepts the six laws as one proof
record. The six fields of FiniteCompatibilityLaws are copied verbatim from the
pre-refactor structure, apart from the already recorded proof-irrelevant change
in quotient_square: its finite-Tor witness comes from the canonical evaluation
object rather than directly from the domain conjunction.

For fixed change data, the old six proof fields correspond exactly to one
FiniteCompatibilityLaws proof, by its constructor and its six projections.
Consequently Nonempty FiniteCompatibility has exactly its old mathematical
meaning. No target text, geometric functor, coefficient ring, or finite comparison
is changed. A target whose statement depends on this definition requires the
normal semantic review of this representation change.

The representation check uses a temporary module: the Old
structure above was copied verbatim under the name OriginalFiniteCompatibility,
and the following equivalence compares the two representations without holes. The
coefficient, scheme and compactification variables are the same as above. This
also checks the proof-irrelevant finite-Tor witness change in quotient_square.

```lean
def compatibilityRepresentationEquiv
    (rR : SystemAdjunction (lowerRings l E) (lowerMaps l E) c)
    (rS : SystemAdjunction (upperRings l E L i) (upperMaps l E L i) c)
    (α : rR.F ⋙ T l E L i Y ≅ T l E L i X ⋙ rS.F) :
    OriginalFiniteCompatibility l E L i c rR rS α ≃
      FiniteCompatibility l E L i c rR rS α where
  toFun d :=
    { change := d.change
      laws :=
        { canonical := d.canonical
          comparison_evaluation := d.comparison_evaluation
          transpose_evaluation := d.transpose_evaluation
          comparison_quotient := d.comparison_quotient
          finite_sum := d.finite_sum
          quotient_square := d.quotient_square } }
  invFun d :=
    { change := d.change
      canonical := d.canonical
      comparison_evaluation := d.comparison_evaluation
      transpose_evaluation := d.transpose_evaluation
      comparison_quotient := d.comparison_quotient
      finite_sum := d.finite_sum
      quotient_square := d.quotient_square }
  left_inv := by intro d; cases d; rfl
  right_inv := by intro d; cases d; rfl
```

## Users

The downstream.py --uses audit lists one downstream importer and no external
uses of this FiniteCompatibility declaration. The changed item is held by B4.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | Same theorem statements and six equations; proof-only record packaging and accessor implementation changed. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed in the local claim snapshot | Imports the item but does not mention this FiniteCompatibility; unchanged source is checked against the delivered interface. |

No consumer adaptation is needed. No adopted WeilConjectures source file changes.

Validation: the equivalence with the actual exported replacement record compiled in a
temporary verification module against the successful main-module artifact build. The
unchanged direct consumer also compiled against that artifact.

## Status

landed 20261026T022824-L-465056 2026-10-26 (merge of deliver/B4/Sheaf.Paper.RamifiedScalarSystemTranspose)
