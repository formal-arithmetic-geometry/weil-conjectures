# AlgebraicGeometry.NodalLocal.Comparison.IsNatural

## Reason

Separate the mathematical data from the theorem proving its existence. The new proof
lemmas need the existing definitions, while the item imports their proofs; keeping
those definitions in the item would create an import cycle. Relocate all existing
NodalLocal data to NodalLocalTangentData, publicly imported by the original item.
Preserve their names, signatures, visibility, instances and mathematical meaning.
The ring-level naturality predicate IsNaturalIso exposes the original predicate
without requiring a complete scheme-level Comparison first.

## Old

```lean
def Comparison.IsNatural {C : Scheme.{u}} {x : C}
    [GradedRing (tangentGrading (C.presheaf.stalk x))] (D : Comparison C x) : Prop :=
  ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [GradedRing (tangentGrading A')]
    (e : C.presheaf.stalk x ≃+* A')
    (i' : Proj (tangentGrading A') ≅ Spec (.of (ResidueAlgebra A'))),
    IsNormalized A' i' →
    ∃ (g : tangentGrading (C.presheaf.stalk x) →+*ᵍ tangentGrading A')
      (ν : Normalization (C.presheaf.stalk x) ≃+* Normalization A')
      (r : ResidueAlgebra (C.presheaf.stalk x) ≃+* ResidueAlgebra A')
      (hg : HomogeneousIdeal.irrelevant (tangentGrading A') ≤
        (HomogeneousIdeal.irrelevant (tangentGrading (C.presheaf.stalk x))).map g),
      (∀ (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal (C.presheaf.stalk x)) ^ n))
        (ha : e a.val ∈ (IsLocalRing.maximalIdeal A') ^ n),
        g (initialForm (C.presheaf.stalk x) n a) = initialForm A' n ⟨e a.val, ha⟩) ∧
      (∀ a : C.presheaf.stalk x,
        ν (algebraMap (C.presheaf.stalk x) (Normalization (C.presheaf.stalk x)) a) =
          algebraMap A' (Normalization A') (e a)) ∧
      (∀ b : Normalization (C.presheaf.stalk x),
        r (Ideal.Quotient.mk (normalizationIdeal (C.presheaf.stalk x)) b) =
          Ideal.Quotient.mk (normalizationIdeal A') (ν b)) ∧
      Proj.map g hg ≫ D.iso.hom = i'.hom ≫ Spec.map (CommRingCat.ofHom r.toRingHom)
```

All other relocated declarations are verbatim from the original item, apart from their
blueprint docstring tags. The original item publicly imported the modules needed by
these definitions directly.

## New

```lean
def IsNaturalIso (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)]
    (i : Proj (tangentGrading A) ≅ Spec (.of (ResidueAlgebra A))) : Prop :=
  ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [GradedRing (tangentGrading A')]
    (e : A ≃+* A')
    (i' : Proj (tangentGrading A') ≅ Spec (.of (ResidueAlgebra A'))),
    IsNormalized A' i' →
    ∃ (g : tangentGrading A →+*ᵍ tangentGrading A')
      (ν : Normalization A ≃+* Normalization A')
      (r : ResidueAlgebra A ≃+* ResidueAlgebra A')
      (hg : HomogeneousIdeal.irrelevant (tangentGrading A') ≤
        (HomogeneousIdeal.irrelevant (tangentGrading A)).map g),
      (∀ (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal A) ^ n))
        (ha : e a.val ∈ (IsLocalRing.maximalIdeal A') ^ n),
        g (initialForm A n a) = initialForm A' n ⟨e a.val, ha⟩) ∧
      (∀ a : A,
        ν (algebraMap A (Normalization A) a) = algebraMap A' (Normalization A') (e a)) ∧
      (∀ b : Normalization A,
        r (Ideal.Quotient.mk (normalizationIdeal A) b) =
          Ideal.Quotient.mk (normalizationIdeal A') (ν b)) ∧
      Proj.map g hg ≫ i.hom = i'.hom ≫ Spec.map (CommRingCat.ofHom r.toRingHom)

/-- Naturality of the underlying normalized tangent comparison.
Source: Stacks Project, curves.tex, Tag 0CBT, intrinsic construction (3).
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def Comparison.IsNatural {C : Scheme.{u}} {x : C}
    [GradedRing (tangentGrading (C.presheaf.stalk x))] (D : Comparison C x) : Prop :=
  IsNaturalIso (C.presheaf.stalk x) D.iso
```

Expanding IsNaturalIso gives the old Comparison.IsNatural body definitionally. The
original module publicly imports NodalLocalTangentData, so its original API remains
available. In the theorem's existential binder, the otherwise implicit graded argument
of Comparison is made explicit as `@Comparison C x graded`; its elaborated type is
unchanged. No Challenge target or original declaration signature is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NodalLocalTangentNormalization | K7 | Uses the relocated definitions through a public import; proof replaced by assembly. |

`tools/downstream.py` reports zero downstream importers and only the item as a textual
user of Comparison.IsNatural. No other existing module is adapted. The new proof
modules import the data module directly. Target statements and all their definitions
retain the same meaning; this is a definitionally equal refactoring, not a mathematical
change.

## Status

landed 20261023T135019-L-2824655 2026-10-23 (merge of deliver/K7/Sheaf.AlgebraicGeometry.NodalLocalTangentNormalization)
