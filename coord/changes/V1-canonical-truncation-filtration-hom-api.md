# CochainComplex.exists_canonicalTruncationFiltration

## Reason

Restore the zero-hole module preserved at
`quarantine/Sheaf/Algebra/Homology/CanonicalTruncationFiltration.lean`, as assigned
by `coord/rework.tsv`. The unmodified archive fails compilation with
`Unknown constant CategoryTheory.FilteredObject.HomPreservingSteps` at lines
68 and 174. The retired structure duplicated `FilteredObject.Hom` from
`WeilConjectures.CategoryTheory.Filtration`; its retirement was reviewed in
`coord/changes/Filtration-official-api-retirement.md`.

The replacement has the same `hom` field and the same existential preservation
condition. Its `F` is definitionally the compatibility accessor `step`. Replace
all five uses of the retired type name: one private helper signature and four
positions in the public theorem. No proof body or mathematical clause changes.
No definition, target, public import, or adopted source module changes.

The complete proof still constructs the actual canonical truncation subobjects,
transports their cokernels through the canonical step isomorphisms, and applies
`CochainComplex.exists_upperTruncationStepSES` for the graded comparison.
Naturality follows by cancellation of cokernel projections; homotopies restrict
degreewise, and quasi-isomorphism invariance follows by two-out-of-three.
Neither an arbitrary object nor a replacement filtration is postulated.

## Old

```lean
theorem exists_canonicalTruncationFiltration :
    ∃ (F : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      DecreasingFiltration K)
      (pi : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).gradedPiece i ⟶
          (singleFunctor (ModuleCat.{u} R) (-i)).obj (K.homology (-i))),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (i : ℤ),
        (F K).step i = Subobject.mk (K.ιTruncLE (-i))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
        (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
          ∃ (a b : ℤ), a < b ∧ (F K).step a = ⊤ ∧ (F K).step b = ⊥) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (i : ℤ),
        ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ)
          (e : (F K).gradedPiece i ≅ M)
          (e₀ : M.X (-i - 1) ≅ cokernel (kernel.ι (K.d (-i - 1) (-i))))
          (e₁ : M.X (-i) ≅ K.cycles (-i)),
          (∀ (r : ℤ), r ≠ -i - 1 → r ≠ -i → IsZero (M.X r)) ∧
          Mono (M.d (-i - 1) (-i)) ∧
          cokernel.π (kernel.ι (K.d (-i - 1) (-i))) ≫ e₀.inv ≫
              M.d (-i - 1) (-i) ≫ e₁.hom ≫ K.iCycles (-i) =
            K.d (-i - 1) (-i) ∧
          (pi K i).f (-i) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-i)
                (K.homology (-i))).hom =
            e.hom.f (-i) ≫ e₁.hom ≫ K.homologyπ (-i) ∧
          QuasiIso (pi K i)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        ∃ (φ : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
          φ.hom = f ∧
          ∀ (i : ℤ),
            FilteredObject.gradedMapSteps φ i ≫ pi L i =
              pi K i ≫
                (singleFunctor (ModuleCat.{u} R) (-i)).map
                  (HomologicalComplex.homologyMap f (-i))) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f g : K ⟶ L),
        (h : Homotopy f g) →
          ∃ (hf : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
            hf.hom = f ∧
            ∃ (hg : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
              hg.hom = g ∧
              ∀ (i n m : ℤ),
                ∃ lift : ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
                  ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ).X m,
                  lift ≫ ((F L).step i).arrow.f m =
                    ((F K).step i).arrow.f n ≫ h.hom n m) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        (∀ (r : ℤ), IsIso (K.homologyMap f r)) →
          ∀ (i : ℤ), ∃ (φ : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
            φ.hom = f ∧ QuasiIso (FilteredObject.gradedMapSteps φ i))
```

The private `canonicalFilteredMap` likewise returned
`FilteredObject.HomPreservingSteps ⟨K, canonicalFiltration K⟩
  ⟨L, canonicalFiltration L⟩`.

## New

```lean
theorem exists_canonicalTruncationFiltration :
    ∃ (F : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      DecreasingFiltration K)
      (pi : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).gradedPiece i ⟶
          (singleFunctor (ModuleCat.{u} R) (-i)).obj (K.homology (-i))),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (i : ℤ),
        (F K).step i = Subobject.mk (K.ιTruncLE (-i))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
        (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
          ∃ (a b : ℤ), a < b ∧ (F K).step a = ⊤ ∧ (F K).step b = ⊥) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (i : ℤ),
        ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ)
          (e : (F K).gradedPiece i ≅ M)
          (e₀ : M.X (-i - 1) ≅ cokernel (kernel.ι (K.d (-i - 1) (-i))))
          (e₁ : M.X (-i) ≅ K.cycles (-i)),
          (∀ (r : ℤ), r ≠ -i - 1 → r ≠ -i → IsZero (M.X r)) ∧
          Mono (M.d (-i - 1) (-i)) ∧
          cokernel.π (kernel.ι (K.d (-i - 1) (-i))) ≫ e₀.inv ≫
              M.d (-i - 1) (-i) ≫ e₁.hom ≫ K.iCycles (-i) =
            K.d (-i - 1) (-i) ∧
          (pi K i).f (-i) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-i)
                (K.homology (-i))).hom =
            e.hom.f (-i) ≫ e₁.hom ≫ K.homologyπ (-i) ∧
          QuasiIso (pi K i)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        ∃ (φ : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
          φ.hom = f ∧
          ∀ (i : ℤ),
            FilteredObject.gradedMapSteps φ i ≫ pi L i =
              pi K i ≫
                (singleFunctor (ModuleCat.{u} R) (-i)).map
                  (HomologicalComplex.homologyMap f (-i))) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f g : K ⟶ L),
        (h : Homotopy f g) →
          ∃ (hf : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
            hf.hom = f ∧
            ∃ (hg : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
              hg.hom = g ∧
              ∀ (i n m : ℤ),
                ∃ lift : ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
                  ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ).X m,
                  lift ≫ ((F L).step i).arrow.f m =
                    ((F K).step i).arrow.f n ≫ h.hom n m) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        (∀ (r : ℤ), IsIso (K.homologyMap f r)) →
          ∀ (i : ℤ), ∃ (φ : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
            φ.hom = f ∧ QuasiIso (FilteredObject.gradedMapSteps φ i))
```

The private `canonicalFilteredMap` now returns
`FilteredObject.Hom ⟨K, canonicalFiltration K⟩ ⟨L, canonicalFiltration L⟩`.
Its constructor and preservation proof are unchanged.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.CanonicalTruncationFiltration
--uses exists_canonicalTruncationFiltration` reports an unknown module because the
item is quarantined. Searches of both `lean/` and `quarantine/` find exactly one
direct importer/declaration user, listed below. A DAG reverse-dependency check
likewise finds only `lem-kun-derived-canonical-filtration`; its attachment,
dependency and intended argument are preserved. The queue lists 16 quarantined
transitive importers; no live module imports or names the repaired item.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.CanonicalTruncationFiltration | V1, assigned repair | Restore the full proof using the canonical filtered-map type; zero holes. |
| Sheaf.Algebra.Homology.DerivedCanonicalFiltration | unclaimed; quarantine | Its use of the theorem at line 588 destructures exactly the same witnesses and six clauses. The bound, map, homotopy and graded quasi-isomorphism interfaces have the same mathematical meaning. Its own retired HomPreservingSteps occurrences and missing FilteredTensorLocalization dependency already require its separately listed rework; no new consumer failure is introduced by this restoration. |

The archived consumer cannot currently compile as a whole because its
`Sheaf.Algebra.Homology.FilteredTensorLocalization` import is quarantined. A
separate consumer probe checks its actual bound conversion and filtered-map witness extraction using the
canonical Hom representation. The consumer's remaining independent rework is not withdrawn or
replaced by an empty module.

## Status

landed 20261020T211841-L-3510388 2026-10-20 (merge of deliver/V1/Sheaf.Algebra.Homology.CanonicalTruncationFiltration)
