# WeilConjectures.IntegralHom.finite_tensor_presentation_evaluation

## Reason

The old statement asserted the prescribed evaluation for an arbitrary left tensor-Hom
adjunction, unrelated to the right-tensor adjunction normalized by `T.uncurry_model`.
This is false: in an additive category one can negate both the unit and counit of
an adjunction. The triangle identities still hold but a nonzero counit changes sign.
For example, for coefficients of odd residue characteristic, the degree-zero unit
pairing is nonzero and differs from its negative.

The caller already has the Koszul symmetry and its representative normalization.
The corrected theorem uses that data and constructs the transported adjunction
along with its evaluation property. Both generator and derived comparison equations
are retained. The sole caller, currently unclaimed (checked on the server), is
adapted in this delivery; its signature and `TensorPresentation` are unchanged.
The generic ringed-derived import becomes public because the corrected statement
uses its symmetry-model predicate. The proved unsigned uncurrying module is imported privately by the item;
its chain-equivalence proof import is private.
The proof uses no finite-coefficient facts, so its repaired statement is generalized
to an arbitrary ring sheaf R. The finite-level caller instantiates that parameter
with its original coefficient ring. This avoids repeatedly checking the large
concrete coefficient construction in the proof (the concrete version type-checked
but took 75 seconds). The statement uses `coefficientTotalTensor`, `coefficientTensorGenerator`, and
`homComplexπ` directly, rather than the definitionally equal integral wrappers
`totalTensor`, `totalPair`, and `projection`/`evaluate`. Compilation of the unchanged
`TensorPresentation` conclusion in the adapted caller checks these conversions.
No target statement or definition used by a target changes.

## Old

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
  [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
  (S : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n) S)
  (adj : ∀ K : DerivedCategory
      (Modules.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)),
    (Functor.curry.obj S.tensor).obj K ⊣
      (Functor.curry.obj
        (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
          (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n))).obj (op K))

/-- The finite-level representative evaluation normalization is supplied by the same
closed tensor construction as the generic coefficient theorem.  The proof chooses
K-flat representatives and K-injective targets, then applies the sectionwise
currying calculation; the signs are those of the total-complex tensor.
Source: Stacks Tags 07A4, 07A6 and 08J9; blueprint paragraph 2.
(blueprint: new-sf-integral-hom-reduction-target-evaluation). -/
theorem finite_tensor_presentation_evaluation :
    ∀ (P I S' : CochainComplex (Modules.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) ℤ)
      (hP : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n) P)
      (hS : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n) S'),
      I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := integralCoefficientCommRingSheaf l E Y n) P I,
      ∃ beta : ((totalTensor.{t, u} Y
          (integralCoefficientCommRingSheaf l E Y n)).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i + j)).val.app U
              (totalPair.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
                P S' i j U x s) =
            (i * j).negOnePow • evaluate.{t, u} Y
              (integralCoefficientCommRingSheaf l E Y n) P I j i U
              ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P, hP⟩, ⟨S', hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫
              homModelMap.{t, u} Y
                (integralCoefficientCommRingSheaf l E Y n) P I)) ≫
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)
```

## New

```lean
variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
  [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

variable
  (S : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
  (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)

theorem finite_tensor_presentation_evaluation
  (β : @SymmetricCategory (DerivedCategory (Modules.{t, u} Y R)) _ S.monoidal)
  (hβ : RingedDerivedTensorSymmetryModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (AlgebraicGeometry.Scheme.ProEt.topology Y)
    R S T β) :
    ∃ adj : ∀ K : DerivedCategory (Modules.{t, u} Y R),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj (derivedInternalHomOfUniverses.{t + 1, t, u,
          (max u (t + 1)) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) R)).obj (op K),
    ∀ (P I S' : CochainComplex (Modules.{t, u} Y R) ℤ)
      (hP : flat.{t, u} Y R P)
      (hS : flat.{t, u} Y R S'),
      I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R) P I,
      ∃ beta : (coefficientTotalTensor.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, S') ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i + j)).val.app U
              (coefficientTensorGenerator.{u, t + 1, t}
                (AlgebraicGeometry.Scheme.ProEt.topology Y) R P S' i j (i + j) rfl U x s) =
            (i * j).negOnePow •
              ((((q.f j ≫ homComplexπ P I j i (i + j) rfl).val.app U s).app
                (op (Over.mk (𝟙 U.unop)))) x)) ∧
        T.comparison.inv.app (⟨P, hP⟩, ⟨S', hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫
              homModelMap.{t, u} Y R P I)) ≫
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)
```

The new module `Sheaf.Paper.IntegralHomRepresentativeUncurry` publicly states and
proves `WeilConjectures.IntegralHom.representative_uncurry_evaluation`. Its full
signature is recorded in `lem-sf-integral-hom-representative-uncurry.json`; it
asserts unsigned representative evaluation and the right-tensor derived comparison.
It introduces no data definition or instance. The item is its sole consumer.
This proved helper is separated for compile performance, with zero new holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralHomRepresentativeUncurry | new, P8 | Fully proved unsigned representative evaluation and derived comparison; private proof import of the existing chain equivalence. |
| Sheaf.Paper.FiniteTensorPresentationEvaluation | P8 | Corrected and proved using the normalized symmetry and existing chain equivalence. |
| Sheaf.Paper.IntegralHomReductionComponents | unclaimed | Obtain the adjunction and evaluation property together; remove the duplicated adjunction construction from the proof. Signature unchanged. |

`tools/downstream.py --uses` reports precisely these two name occurrences. The direct
importer of the adapted caller is `Sheaf.Paper.IntegralHomReductionPresentation`;
its proof and signature need no changes. It was compiled against this delivery (3.7 seconds);
the evaluation theorem and adapted caller compiled in 46.4 and 39.1 seconds.

## Status

landed 20261028T072439-L-1949508 2026-10-28 (merge of deliver/P8/Sheaf.Paper.FiniteTensorPresentationEvaluation)
