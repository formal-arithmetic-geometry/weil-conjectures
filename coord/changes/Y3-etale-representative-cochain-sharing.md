# Etale representative native complex and tensor sharing

## Reason

Complete `finiteHomEtaleRepresentativeData_existsUnique` within the single-file
time limit. Profiling showed expensive kernel comparisons in the representative
normalization and theorem. Store the native cochain category, its category
instance, the actual cochain tensor and localization functor alongside the
derived tensor and localization map in `FiniteHomNativeTensorData`. Its real
constructor supplies precisely `CochainComplex C ℤ`, its existing category,
`finiteHomCochainTensorGeneral C`, `DerivedCategory.Q`, the published derived
tensor, and the published lax localization tensorator. Nothing is chosen from
an existence statement.

The existing cochain tensor constructor is moved earlier without changing its
signature or proof. One generic etale specialization of the native data is
shared by its complex type, total object, derived tensor, localization and model
projections. Existing concrete domains, objects and maps are definitionally equal
to their old values. The two pointwise normalization conditions are fields of a
generic `Representatives.Normalization` record; the etale normalization is now
an abbreviation specializing this record. Giving the old two proofs is equivalent
to giving the new two fields, with no condition added or removed. Dot projections
`h.generator` and `h.model` access exactly the original pointwise heterogeneous
equalities. The old specialized constructor, recursor and qualified projection
names are not retained; source searches find no external code using these names
(the K-flat module has a comment mentioning the old qualified model projection).
This avoids repeated expanded comparisons of categorical instances and signed
total complexes.

The native inclusion API returns the projected total-tensor object already at the
generic category, with body `finiteHomTensorInclusionGeneral P Q p q k h`. The
canonical section calls this API with the same actual inclusion and the same
sheafified pure tensor. This avoids comparing the expanded signed-total object
after specializing to sheaves. Its etale wrapper specializes first to an arbitrary
coefficient category, and the section then specializes that wrapper to `ModuleCat`.
The source record uses the shared small Hom universe of the etale complex and
derived categories; their object universes remain independent.

The additional `FiniteHomTensorSourceData` record reuses those same native cochain,
category, tensor and localization projections. The generic `fromSources` abbreviation forms the same representative
record while sharing each source as a whole.

The native and source records' category projections are local instances for constructing
these definitions. The generic etale cochain category has its own public
`instance_reducible` category instance, projecting the same stored category.
The generic source specialization and representative proof explicitly provide
the indexed category family to avoid a repeated higher-order instance search.

All edits are in the item. No source-library module, public import, or target
signature changes. The generic native-data record gains real source fields; its
constructor therefore gains those fields. The old specialized normalization
inductive is replaced by an abbreviation, so its generated specialized names
are withdrawn as described above. Other existing concrete data signatures change only
by definitional equality. The existence-and-uniqueness theorem keeps its original
named statement; its normalization predicate is logically equivalent to the
original pair of conditions, as checked by the temporary Lean audit. The independent reader should recheck affected target meanings
through these definitional equalities under the usual statement-review rule.

## Old

```lean
structure FiniteHomNativeTensorData
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] where
  tensor : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C
  model (P Q : CochainComplex C ℤ) :
    tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q)
```

```lean
def finiteHomNativeTensorDataGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] : FiniteHomNativeTensorData C where
  tensor := tensor (DerivedCategory C)
  model P Q := Functor.LaxMonoidal.μ DerivedCategory.Q P Q
```

```lean
def finiteHomLocalizationTensorModelGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    (finiteHomNativeTensorDataGeneral C).tensor.obj
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q) :=
  (finiteHomNativeTensorDataGeneral C).model P Q
```

```lean
def finiteHomEtaleDerivedTensorGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  finiteHomDerivedTensorGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs
      (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A)))
```

```lean
def finiteHomEtaleLocalizationTensorModelGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : CochainComplex (Sheaf W.smallEtaleTopology A) ℤ) :=
  finiteHomLocalizationTensorModelGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs
      (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A))) P Q
```

```lean
abbrev finiteHomEtaleQ (n : ℕ) :
    CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ ⥤
      finiteHomEtale l E X n := DerivedCategory.Q
```

```lean
structure FiniteHomEtaleTensorSectionInput where
  n : ℕ
  P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  p : ℤ
  q : ℤ
  k : ℤ
  h : p + q = k
  U : X.Etale
  x : (P.X p).obj.obj (op U)
  y : (Q.X q).obj.obj (op U)
```

```lean
abbrev finiteHomEtaleTotalObject (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :=
  HomologicalComplex.tensorObj P Q
```

```lean
def finiteHomEtaleCanonicalTensorSectionGeneral
    (B : Type (u + 1)) [CommRing B] (W : Scheme.{u})
    (P Q : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : W.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    ((HomologicalComplex.tensorObj P Q).X k).obj.obj (op U) :=
  ((finiteHomTensorInclusionGeneral P Q p q k h).hom.app (op U)).hom'
    (((Functor.LaxMonoidal.μ (sheafToPresheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} B)) (P.X p) (Q.X q)).app (op U)).hom' (x ⊗ₜ y))
```

```lean
abbrev FiniteHomEtaleRepresentativeData :=
  (finiteHomEtaleData l E X).Representatives
    (fun n : ℕ ↦ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (finiteHomEtaleQ l E X) (finiteHomEtaleTotalObject l E X)
    (FiniteHomEtaleTensorSectionInput l E X) (finiteHomEtaleTensorSectionCarrier l E X)
```

```lean
def FiniteHomEtaleModelNormalizationGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    {V : CochainComplex (Sheaf W.smallEtaleTopology A) ℤ →
      CochainComplex (Sheaf W.smallEtaleTopology A) ℤ → Type (u + 1)}
    (v : ∀ P Q, V P Q) : Prop :=
  ∀ P Q, HEq (v P Q) (finiteHomEtaleLocalizationTensorModelGeneral A W P Q)
```

```lean
def finiteHomEtaleTotalSection (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :=
  (finiteHomEtaleRepresentativeData l E X).generator ⟨n, P, Q, p, q, k, h, U, x, y⟩
```

```lean
def finiteHomEtaleTensorModel (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :=
  (finiteHomEtaleRepresentativeData l E X).model n P Q
```

```lean
structure FiniteHomEtaleRepresentativeNormalization
    (S : FiniteHomEtaleRepresentativeData l E X) : Prop where
  generator : FiniteHomGeneratorNormalizationAux S.generator
    (finiteHomEtaleCanonicalTensorSection l E X)
  model : ∀ n, FiniteHomEtaleModelNormalizationGeneral
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))) X (S.model n)
```

## New

```lean
structure FiniteHomNativeTensorData
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] where
  cochain : Type (max a b)
  [cochainCategory : Category.{b} cochain]
  cochainTensor : cochain × cochain ⥤ cochain
  localization : cochain ⥤ DerivedCategory C
  tensor : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C
  model (P Q : cochain) :
    tensor.obj (localization.obj P, localization.obj Q) ⟶
      localization.obj (cochainTensor.obj (P, Q))
```

```lean
def finiteHomNativeTensorDataGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] : FiniteHomNativeTensorData C where
  cochain := CochainComplex C ℤ
  cochainCategory := inferInstance
  cochainTensor := finiteHomCochainTensorGeneral C
  localization := DerivedCategory.Q
  tensor := tensor (DerivedCategory C)
  model P Q := Functor.LaxMonoidal.μ DerivedCategory.Q P Q
```

```lean
def finiteHomLocalizationTensorModelGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : (finiteHomNativeTensorDataGeneral C).cochain) :=
  (finiteHomNativeTensorDataGeneral C).model P Q
```

```lean
structure FiniteHomTensorSourceData (D : Type a) [Category.{b} D] where
  cochain : Type c
  [cochainCategory : Category.{b} cochain]
  cochainTensor : cochain × cochain ⥤ cochain
  localization : cochain ⥤ D
```

```lean
def finiteHomEtaleNativeTensorDataGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  finiteHomNativeTensorDataGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs
      (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A)))
```

```lean
def finiteHomEtaleTensorSourceGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  FiniteHomTensorSourceData.mk
    (cochainCategory := (finiteHomEtaleNativeTensorDataGeneral A W).cochainCategory)
    (finiteHomEtaleNativeTensorDataGeneral A W).cochain
    (finiteHomEtaleNativeTensorDataGeneral A W).cochainTensor
    (finiteHomEtaleNativeTensorDataGeneral A W).localization
```

```lean
abbrev finiteHomEtaleCochainGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) := (finiteHomEtaleTensorSourceGeneral A W).cochain
```

```lean
@[instance_reducible] def finiteHomEtaleCochainCategoryGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) : Category.{u + 1} (finiteHomEtaleCochainGeneral A W) :=
  (finiteHomEtaleTensorSourceGeneral A W).cochainCategory
```

```lean
def finiteHomEtaleTotalObjectGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : finiteHomEtaleCochainGeneral A W) :=
  (finiteHomEtaleTensorSourceGeneral A W).cochainTensor.obj (P, Q)
```

```lean
def finiteHomEtaleDerivedTensorGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  (finiteHomEtaleNativeTensorDataGeneral A W).tensor
```

```lean
def finiteHomEtaleLocalizationTensorModelGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : finiteHomEtaleCochainGeneral A W) :=
  (finiteHomEtaleNativeTensorDataGeneral A W).model P Q
```

```lean
abbrev finiteHomEtaleQ (n : ℕ) :=
  (finiteHomEtaleTensorSourceGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).localization
```

```lean
structure FiniteHomEtaleTensorSectionInput where
  n : ℕ
  P : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X
  Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X
  p : ℤ
  q : ℤ
  k : ℤ
  h : p + q = k
  U : X.Etale
  x : (P.X p).obj.obj (op U)
  y : (Q.X q).obj.obj (op U)
```

```lean
abbrev finiteHomEtaleTotalObject (n : ℕ)
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) :=
  finiteHomEtaleTotalObjectGeneral _ X P Q
```

```lean
def finiteHomEtaleCanonicalTensorSectionGeneral
    (B : Type (u + 1)) [CommRing B] (W : Scheme.{u})
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1} B) W)
    (p q k : ℤ) (h : p + q = k) (U : W.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    ((finiteHomEtaleTotalObjectGeneral (ModuleCat.{u + 1} B) W P Q).X k).obj.obj (op U) :=
  ((finiteHomEtaleTensorInclusionGeneral (ModuleCat.{u + 1} B) W
      P Q p q k h).hom.app (op U)).hom'
    (((Functor.LaxMonoidal.μ (sheafToPresheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} B)) (P.X p) (Q.X q)).app (op U)).hom' (x ⊗ₜ y))
```

```lean
abbrev FiniteHomQuotientClosedData.Representatives.fromSources
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (N : ∀ n, FiniteHomTensorSourceData (C n)) (I : Type e) (V : I → Type f) :=
  letI : ∀ n, Category (N n).cochain := fun n ↦ (N n).cochainCategory
  S.Representatives (fun n ↦ (N n).cochain) (fun n ↦ (N n).localization)
    (fun n P Q ↦ (N n).cochainTensor.obj (P, Q)) I V
```

```lean
abbrev FiniteHomEtaleRepresentativeData :=
  FiniteHomQuotientClosedData.Representatives.fromSources (finiteHomEtaleData l E X)
    (fun n ↦ finiteHomEtaleTensorSourceGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)
    (FiniteHomEtaleTensorSectionInput l E X) (finiteHomEtaleTensorSectionCarrier l E X)
```

```lean
def FiniteHomEtaleModelNormalizationGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    {V : finiteHomEtaleCochainGeneral A W →
      finiteHomEtaleCochainGeneral A W → Type (u + 1)}
    (v : ∀ P Q, V P Q) : Prop :=
  ∀ P Q, HEq (v P Q) (finiteHomEtaleLocalizationTensorModelGeneral A W P Q)
```

```lean
def finiteHomEtaleTotalSection (n : ℕ)
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)
    (p q k : ℤ) (h : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :=
  (finiteHomEtaleRepresentativeData l E X).generator ⟨n, P, Q, p, q, k, h, U, x, y⟩
```

```lean
def finiteHomEtaleTensorModel (n : ℕ)
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) :=
  (finiteHomEtaleRepresentativeData l E X).model n P Q
```

```lean
structure FiniteHomQuotientClosedData.Representatives.Normalization
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    {S : FiniteHomQuotientClosedData C H F}
    {A : ℕ → Type c} [∀ n : ℕ, Category.{d} (A n)]
    {Q : ∀ n : ℕ, A n ⥤ C n} {T : ∀ n : ℕ, A n → A n → A n}
    {I : Type e} {V : I → Type f}
    (R : S.Representatives A Q T I V) (v : ∀ i : I, V i)
    {M : ∀ n : ℕ, A n → A n → Type b} (t : ∀ n P Z, M n P Z) : Prop where
  generator : ∀ i, HEq (R.generator i) (v i)
  model : ∀ n P Z, HEq (R.model n P Z) (t n P Z)
```

```lean
abbrev FiniteHomEtaleRepresentativeNormalization
    (S : FiniteHomEtaleRepresentativeData l E X) : Prop :=
  S.Normalization (finiteHomEtaleCanonicalTensorSection l E X)
    (fun n ↦ finiteHomEtaleLocalizationTensorModelGeneral
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) X)
```

```lean
def finiteHomNativeTensorInclusionGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : (finiteHomNativeTensorDataGeneral C (hD := hD)).cochain)
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶
      ((finiteHomNativeTensorDataGeneral C (hD := hD)).cochainTensor.obj (P, Q)).X k :=
  finiteHomTensorInclusionGeneral P Q p q k h
```

```lean
def finiteHomEtaleTensorInclusionGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : finiteHomEtaleCochainGeneral A W)
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶ (finiteHomEtaleTotalObjectGeneral A W P Q).X k :=
  finiteHomNativeTensorInclusionGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf W.smallEtaleTopology A))) P Q p q k h
```

## Users

`tools/downstream.py --uses` and source searches identify the item and the K-flat
presentation as direct users of the changed native-data declarations. The site
comparison consumers below use the localization and inferred tensor-model
endpoint. No source adaptations are made outside the item. Seven direct importers are
also checked, including the six not listed individually below:
`EtaleLisseHomReduction`, `FiniteCoefficientSiteScalarArrow`,
`FiniteFreeHomEvaluationCoordinates`, `CoefFiniteHomSiteDescent`,
`FiniteCoefficientIntrinsicChainTensor`, and `FiniteHomDomainCalculus`.
All mathematical meanings remain the same by the displayed real constructor,
projections and the identical two normalization clauses.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Y3 | Shared native complex and tensor data; representative theorem completed. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | no local claim; not adapted | Same native tensor, localization map and normalized model. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | no local claim; not adapted | Same localization functor. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | no local claim; not adapted | Same localization and inferred tensor-model endpoint. |
| Sheaf.Paper.FiniteCoefficientSiteTensorPresentation | no local claim; not adapted | Same localization and inferred tensor-model endpoint. |

Validation: the final item compiled cleanly in 50.4 seconds. The semantic audit
and all ten unchanged consumer sources compiled in the ordered validation batch.
No forced adaptation was needed. The temporary semantic audit source is
reproduced here for review:

```lean
module
public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

example (S : FiniteHomEtaleRepresentativeData l E X) :
    FiniteHomEtaleRepresentativeNormalization l E X S ↔
      FiniteHomGeneratorNormalizationAux S.generator
        (finiteHomEtaleCanonicalTensorSection l E X) ∧
      ∀ n, FiniteHomEtaleModelNormalizationGeneral
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))) X (S.model n) := by
  constructor
  · intro h
    exact ⟨h.generator, h.model⟩
  · rintro ⟨hg, hm⟩
    exact ⟨hg, hm⟩

end WeilConjectures
```

## Status

landed 20261026T003251-L-157414 2026-10-26 (merge of deliver/Y3/Sheaf.Paper.EtaleFiniteCoefficientHomArrow)
