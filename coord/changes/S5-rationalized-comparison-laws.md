# WeilConjectures.RationalizedSmoothAdjunction comparison laws

## Reason

Profiling the new coefficient-comparison proof showed repeated elaboration of
large scheme-specialized unit, counit, cocycle and identity expressions. Factor
each unchanged component equation into a generic predicate over categories and
functors; the existing definitions specialize those predicates to the original
scheme functors. Unfolding a predicate gives the old body, including the same
quantifiers, comparisons, associators and unitors. This is a representation
repair; no hypothesis or conclusion changes. All existing theorem signatures,
including Challenge targets, stay verbatim. Their semantic statement review
must check these equivalent definition bodies.

Generic law definitions and the private coefficient-localization lemmas are
placed outside the geometric section variables. Profiling showed that Lean was
repeatedly elaborating the unused r/c presentation context for those independent
lemmas. Their parameters, statements and proof content are retained; this is a
proof-context organization change, not an additional mathematical assumption.

The component types and predicates are named separately so that projections do
not carry expanded specification expressions as their implicit type parameters.
The named components and four generic laws unfold to the old bodies. The record
constructors and every mathematical field are retained. Private proved map lemmas
express the existing localization formulas in the canonical scheme notation.
The proof extracts the comparison witnesses once and then uses a fresh record
variable for coherence, avoiding repeated choice-term expansion.

## Old

```lean
abbrev IntegralComparisons := AdjunctionComparisonsData
  (∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    P l B.val j p d (s B) ⋙ integralC l Ω p₀ hl Y B F h ≅
      integralC l Ω p₀ hl X B F h ⋙ P l F.val j p d (s F))
  (∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    H l B.val j p d (s B) ⋙ integralC l Ω p₀ hl X B F h ≅
      integralC l Ω p₀ hl Y B F h ⋙ H l F.val j p d (s F))
  (fun b a ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    (integralC l Ω p₀ hl X B F h).map ((adjunction l B.val j p d (s B)).unit.app M) ≫
      (a B F h).hom.app ((P l B.val j p d (s B)).obj M) ≫
      (H l F.val j p d (s F)).map ((b B F h).hom.app M) =
        (adjunction l F.val j p d (s F)).unit.app
          ((integralC l Ω p₀ hl X B F h).obj M))
  (fun b a ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    (b B F h).hom.app ((H l B.val j p d (s B)).obj K) ≫
      (P l F.val j p d (s F)).map ((a B F h).hom.app K) ≫
      (adjunction l F.val j p d (s F)).counit.app
        ((integralC l Ω p₀ hl Y B F h).obj K) =
      (integralC l Ω p₀ hl Y B F h).map ((adjunction l B.val j p d (s B)).counit.app K))
```

```lean
abbrev RationalComparisons := LocalizedComparisonsData
  (∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalP l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl Y B F h ≅
      rationalC l Ω p₀ hl X B F h ⋙ rationalP l F.val j p d (s F))
  (∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalH l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl X B F h ≅
      rationalC l Ω p₀ hl Y B F h ⋙ rationalH l F.val j p d (s F))
  (fun b ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).hom.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).hom.app M)))
  (fun b ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).inv.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).inv.app M)))
  (fun a ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).hom.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).hom.app K)))
  (fun a ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).inv.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).inv.app K)))
  (fun b a ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfRationalConstructibleCategory l B.val X),
    (rationalC l Ω p₀ hl X B F h).map ((r B).adjunction.unit.app M) ≫
      (a B F h).hom.app ((rationalP l B.val j p d (s B)).obj M) ≫
      (rationalH l F.val j p d (s F)).map ((b B F h).hom.app M) =
        (r F).adjunction.unit.app ((rationalC l Ω p₀ hl X B F h).obj M))
  (fun b a ↦
    ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfRationalConstructibleCategory l B.val Y),
    (b B F h).hom.app ((rationalH l B.val j p d (s B)).obj K) ≫
      (rationalP l F.val j p d (s F)).map ((a B F h).hom.app K) ≫
      (r F).adjunction.counit.app ((rationalC l Ω p₀ hl Y B F h).obj K) =
        (rationalC l Ω p₀ hl Y B F h).map ((r B).adjunction.counit.app K))
```

```lean
def IntegralCocycles : Prop :=
  ∀ (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L),
    (∀ M : sfIntegralConstructibleCategory l B.val X,
      (integralC l Ω p₀ hl Y F L hFL).map ((c.b B F hBF).hom.app M) ≫
        (c.b F L hFL).hom.app ((integralC l Ω p₀ hl X B F hBF).obj M) ≫
        (P l L.val j p d (s L)).map
          ((sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
            p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app M) =
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
        p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app
          ((P l B.val j p d (s B)).obj M) ≫
        (c.b B L (le_trans hBF hFL)).hom.app M) ∧
    (∀ K : sfIntegralConstructibleCategory l B.val Y,
      (integralC l Ω p₀ hl X F L hFL).map ((c.a B F hBF).hom.app K) ≫
        (c.a F L hFL).hom.app ((integralC l Ω p₀ hl Y B F hBF).obj K) ≫
        (H l L.val j p d (s L)).map
          ((sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
            p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app K) =
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
        p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app
          ((H l B.val j p d (s B)).obj K) ≫
        (c.a B L (le_trans hBF hFL)).hom.app K)
```

```lean
def RationalCocycles (q : RationalComparisons l Ω p₀ hl j p d s r c) : Prop :=
  ∀ (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L),
    (∀ M : sfRationalConstructibleCategory l B.val X,
      (rationalC l Ω p₀ hl Y F L hFL).map ((q.b B F hBF).hom.app M) ≫
        (q.b F L hFL).hom.app ((rationalC l Ω p₀ hl X B F hBF).obj M) ≫
        (rationalP l L.val j p d (s L)).map
          ((sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
            p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app M) =
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
        p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app
          ((rationalP l B.val j p d (s B)).obj M) ≫
        (q.b B L (le_trans hBF hFL)).hom.app M) ∧
    (∀ K : sfRationalConstructibleCategory l B.val Y,
      (rationalC l Ω p₀ hl X F L hFL).map ((q.a B F hBF).hom.app K) ≫
        (q.a F L hFL).hom.app ((rationalC l Ω p₀ hl Y B F hBF).obj K) ≫
        (rationalH l L.val j p d (s L)).map
          ((sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
            p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app K) =
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
        p₀ hl L.val (IntermediateField.inclusion hFL)).hom.app
          ((rationalH l B.val j p d (s B)).obj K) ≫
        (q.a B L (le_trans hBF hFL)).hom.app K)
```

```lean
def IntegralIdentity : Prop :=
  ∀ B : Padic.FiniteCoefficientFields l Ω,
    (∀ M : sfIntegralConstructibleCategory l B.val X,
      (c.b B B (le_refl B)).hom.app M =
        (sfIntegralScalarUnit l B.val Y p₀ hl).hom.app ((P l B.val j p d (s B)).obj M) ≫
          (P l B.val j p d (s B)).map ((sfIntegralScalarUnit l B.val X p₀ hl).inv.app M)) ∧
    (∀ K : sfIntegralConstructibleCategory l B.val Y,
      (c.a B B (le_refl B)).hom.app K =
        (sfIntegralScalarUnit l B.val X p₀ hl).hom.app ((H l B.val j p d (s B)).obj K) ≫
          (H l B.val j p d (s B)).map ((sfIntegralScalarUnit l B.val Y p₀ hl).inv.app K))
```

```lean
def RationalIdentity (q : RationalComparisons l Ω p₀ hl j p d s r c) : Prop :=
  ∀ B : Padic.FiniteCoefficientFields l Ω,
    (∀ M : sfRationalConstructibleCategory l B.val X,
      (q.b B B (le_refl B)).hom.app M =
        (sfRationalScalarUnit l B.val Y p₀ hl).hom.app
          ((rationalP l B.val j p d (s B)).obj M) ≫
        (rationalP l B.val j p d (s B)).map
          ((sfRationalScalarUnit l B.val X p₀ hl).inv.app M)) ∧
    (∀ K : sfRationalConstructibleCategory l B.val Y,
      (q.a B B (le_refl B)).hom.app K =
        (sfRationalScalarUnit l B.val X p₀ hl).hom.app
          ((rationalH l B.val j p d (s B)).obj K) ≫
        (rationalH l B.val j p d (s B)).map
          ((sfRationalScalarUnit l B.val Y p₀ hl).inv.app K))
```

## New

```lean
/-- Compatibility of two adjunction units with a pair of comparison isomorphisms.
Source: field-extension proof, unit equation
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def UnitComparisonLaw {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (CX : C ⥤ C') (CY : D ⥤ D')
    (b : F ⋙ CY ≅ CX ⋙ F') (c : G ⋙ CX ≅ CY ⋙ G') : Prop :=
  ∀ M : C, CX.map (a.unit.app M) ≫ c.hom.app (F.obj M) ≫ G'.map (b.hom.app M) =
    a'.unit.app (CX.obj M)

/-- Compatibility of two adjunction counits with a pair of comparison isomorphisms.
Source: field-extension proof, counit equation
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def CounitComparisonLaw {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F' ⊣ G') (CX : C ⥤ C') (CY : D ⥤ D')
    (b : F ⋙ CY ≅ CX ⋙ F') (c : G ⋙ CX ≅ CY ⋙ G') : Prop :=
  ∀ K : D, b.hom.app (G.obj K) ≫ F'.map (c.hom.app K) ≫ a'.counit.app (CY.obj K) =
    CY.map (a.counit.app K)

/-- The component equation for coefficient comparisons over a triple of fields.
Source: field-extension proof, composition equation
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def CoefficientCocycleLaw {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    (CX₀₁ : C₀ ⥤ C₁) (CX₁₂ : C₁ ⥤ C₂) (CX₀₂ : C₀ ⥤ C₂)
    (CY₀₁ : D₀ ⥤ D₁) (CY₁₂ : D₁ ⥤ D₂) (CY₀₂ : D₀ ⥤ D₂)
    (b₀₁ : T₀ ⋙ CY₀₁ ≅ CX₀₁ ⋙ T₁) (b₁₂ : T₁ ⋙ CY₁₂ ≅ CX₁₂ ⋙ T₂)
    (b₀₂ : T₀ ⋙ CY₀₂ ≅ CX₀₂ ⋙ T₂)
    (cX : CX₀₁ ⋙ CX₁₂ ≅ CX₀₂) (cY : CY₀₁ ⋙ CY₁₂ ≅ CY₀₂) : Prop :=
  ∀ M : C₀, CY₁₂.map (b₀₁.hom.app M) ≫ b₁₂.hom.app (CX₀₁.obj M) ≫
      T₂.map (cX.hom.app M) = cY.hom.app (T₀.obj M) ≫ b₀₂.hom.app M

/-- Identity normalization under the specified coefficient unitors.
Source: field-extension proof, identity normalization
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def CoefficientIdentityLaw {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) (CX : C ⥤ C) (CY : D ⥤ D) (b : T ⋙ CY ≅ CX ⋙ T)
    (uX : CX ≅ 𝟭 C) (uY : CY ≅ 𝟭 D) : Prop :=
  ∀ M : C, b.hom.app M = uY.hom.app (T.obj M) ≫ T.map (uX.inv.app M)
```

```lean
/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralForwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    P l B.val j p d (s B) ⋙ integralC l Ω p₀ hl Y B F h ≅
      integralC l Ω p₀ hl X B F h ⋙ P l F.val j p d (s F)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralBackwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    H l B.val j p d (s B) ⋙ integralC l Ω p₀ hl X B F h ≅
      integralC l Ω p₀ hl Y B F h ⋙ H l F.val j p d (s F)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralUnitCompatibility (b : IntegralForwardComparisons l Ω p₀ hl j p d s)
    (a : IntegralBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      UnitComparisonLaw (adjunction l B.val j p d (s B)) (adjunction l F.val j p d (s F))
        (integralC l Ω p₀ hl X B F h) (integralC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- Named component of the integral comparison specification.
Source: the unchanged comparison equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralCounitCompatibility (b : IntegralForwardComparisons l Ω p₀ hl j p d s)
    (a : IntegralBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      CounitComparisonLaw (adjunction l B.val j p d (s B)) (adjunction l F.val j p d (s F))
        (integralC l Ω p₀ hl X B F h) (integralC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- Exactly the two given integral natural isomorphisms and the two integral adjunction
comparison equations. No comparison is chosen or assumed invertible after localization.
Source: field-extension proof, coefficient comparisons
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev IntegralComparisons := AdjunctionComparisonsData
  (IntegralForwardComparisons l Ω p₀ hl j p d s)
  (IntegralBackwardComparisons l Ω p₀ hl j p d s)
  (IntegralUnitCompatibility l Ω p₀ hl j p d s)
  (IntegralCounitCompatibility l Ω p₀ hl j p d s)

variable (r : ∀ B : Padic.FiniteCoefficientFields l Ω, Raw l B.val j p d (s B))
  (c : IntegralComparisons l Ω p₀ hl j p d s)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalForwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalP l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl Y B F h ≅
      rationalC l Ω p₀ hl X B F h ⋙ rationalP l F.val j p d (s F)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalBackwardComparisons :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalH l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl X B F h ≅
      rationalC l Ω p₀ hl Y B F h ⋙ rationalH l F.val j p d (s F)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalForwardHomLaw (b : RationalForwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).hom.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).hom.app M))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalForwardInvLaw (b : RationalForwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).inv.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).inv.app M))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalBackwardHomLaw (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).hom.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).hom.app K))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalBackwardInvLaw (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).inv.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).inv.app K))

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalUnitCompatibility (b : RationalForwardComparisons l Ω p₀ hl j p d s)
    (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      UnitComparisonLaw (r B).adjunction (r F).adjunction
        (rationalC l Ω p₀ hl X B F h) (rationalC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- Named component of the rational comparison specification.
Source: the unchanged localized component and adjunction equations
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalCounitCompatibility (b : RationalForwardComparisons l Ω p₀ hl j p d s)
    (a : RationalBackwardComparisons l Ω p₀ hl j p d s) : Prop :=
  ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
      CounitComparisonLaw (r B).adjunction (r F).adjunction
        (rationalC l Ω p₀ hl X B F h) (rationalC l Ω p₀ hl Y B F h)
        (b B F h) (a B F h)

/-- The rational natural isomorphisms, with exactly the localized integral components,
the localized inverse components and both rational adjunction comparison equations.
HEq only transports the published coefficient functor's specified object equality.
Source: field-extension proof, raw localization of comparisons
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
abbrev RationalComparisons := LocalizedComparisonsData
  (RationalForwardComparisons l Ω p₀ hl j p d s)
  (RationalBackwardComparisons l Ω p₀ hl j p d s)
  (RationalForwardHomLaw l Ω p₀ hl j p d s c)
  (RationalForwardInvLaw l Ω p₀ hl j p d s c)
  (RationalBackwardHomLaw l Ω p₀ hl j p d s c)
  (RationalBackwardInvLaw l Ω p₀ hl j p d s c)
  (RationalUnitCompatibility l Ω p₀ hl j p d s r)
  (RationalCounitCompatibility l Ω p₀ hl j p d s r)

/-- The integral coefficient cocycles, with the actual completed-extension associators.
Source: field-extension proof, composition sentence
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralCocycles : Prop :=
  ∀ (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L),
    CoefficientCocycleLaw
      (P l B.val j p d (s B)) (P l F.val j p d (s F))
      (P l L.val j p d (s L))
      (integralC l Ω p₀ hl X B F hBF) (integralC l Ω p₀ hl X F L hFL)
      (integralC l Ω p₀ hl X B L (le_trans hBF hFL))
      (integralC l Ω p₀ hl Y B F hBF) (integralC l Ω p₀ hl Y F L hFL)
      (integralC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (c.b B F hBF) (c.b F L hFL) (c.b B L (le_trans hBF hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
        p₀ hl L.val (IntermediateField.inclusion hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
        p₀ hl L.val (IntermediateField.inclusion hFL)) ∧
    CoefficientCocycleLaw
      (H l B.val j p d (s B)) (H l F.val j p d (s F))
      (H l L.val j p d (s L))
      (integralC l Ω p₀ hl Y B F hBF) (integralC l Ω p₀ hl Y F L hFL)
      (integralC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (integralC l Ω p₀ hl X B F hBF) (integralC l Ω p₀ hl X F L hFL)
      (integralC l Ω p₀ hl X B L (le_trans hBF hFL))
      (c.a B F hBF) (c.a F L hFL) (c.a B L (le_trans hBF hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
        p₀ hl L.val (IntermediateField.inclusion hFL))
      (sfIntegralScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
        p₀ hl L.val (IntermediateField.inclusion hFL))

/-- The same cocycles in raw rational categories, using the published rational associators.
Source: field-extension proof, invert ell in the composition identities
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalCocycles (q : RationalComparisons l Ω p₀ hl j p d s r c) : Prop :=
  ∀ (B F L : Padic.FiniteCoefficientFields l Ω) (hBF : B ≤ F) (hFL : F ≤ L),
    CoefficientCocycleLaw
      (rationalP l B.val j p d (s B)) (rationalP l F.val j p d (s F))
      (rationalP l L.val j p d (s L))
      (rationalC l Ω p₀ hl X B F hBF) (rationalC l Ω p₀ hl X F L hFL)
      (rationalC l Ω p₀ hl X B L (le_trans hBF hFL))
      (rationalC l Ω p₀ hl Y B F hBF) (rationalC l Ω p₀ hl Y F L hFL)
      (rationalC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (q.b B F hBF) (q.b F L hFL) (q.b B L (le_trans hBF hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
        p₀ hl L.val (IntermediateField.inclusion hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
        p₀ hl L.val (IntermediateField.inclusion hFL)) ∧
    CoefficientCocycleLaw
      (rationalH l B.val j p d (s B)) (rationalH l F.val j p d (s F))
      (rationalH l L.val j p d (s L))
      (rationalC l Ω p₀ hl Y B F hBF) (rationalC l Ω p₀ hl Y F L hFL)
      (rationalC l Ω p₀ hl Y B L (le_trans hBF hFL))
      (rationalC l Ω p₀ hl X B F hBF) (rationalC l Ω p₀ hl X F L hFL)
      (rationalC l Ω p₀ hl X B L (le_trans hBF hFL))
      (q.a B F hBF) (q.a F L hFL) (q.a B L (le_trans hBF hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) Y
        p₀ hl L.val (IntermediateField.inclusion hFL))
      (sfRationalScalarComp l B.val F.val (IntermediateField.inclusion hBF) X
        p₀ hl L.val (IntermediateField.inclusion hFL))

/-- Identity comparisons under the actual completed coefficient-extension unitors.
Source: field-extension proof, identity normalization
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def IntegralIdentity : Prop :=
  ∀ B : Padic.FiniteCoefficientFields l Ω,
    CoefficientIdentityLaw (P l B.val j p d (s B))
      (integralC l Ω p₀ hl X B B (le_refl B))
      (integralC l Ω p₀ hl Y B B (le_refl B)) (c.b B B (le_refl B))
      (sfIntegralScalarUnit l B.val X p₀ hl) (sfIntegralScalarUnit l B.val Y p₀ hl) ∧
    CoefficientIdentityLaw (H l B.val j p d (s B))
      (integralC l Ω p₀ hl Y B B (le_refl B))
      (integralC l Ω p₀ hl X B B (le_refl B)) (c.a B B (le_refl B))
      (sfIntegralScalarUnit l B.val Y p₀ hl) (sfIntegralScalarUnit l B.val X p₀ hl)

/-- Identity normalization with the actual rational coefficient-extension unitors.
Source: field-extension proof, raw identity normalization
(blueprint: lem-pur-rationalized-smooth-adjunction-diagrams). -/
def RationalIdentity (q : RationalComparisons l Ω p₀ hl j p d s r c) : Prop :=
  ∀ B : Padic.FiniteCoefficientFields l Ω,
    CoefficientIdentityLaw (rationalP l B.val j p d (s B))
      (rationalC l Ω p₀ hl X B B (le_refl B))
      (rationalC l Ω p₀ hl Y B B (le_refl B)) (q.b B B (le_refl B))
      (sfRationalScalarUnit l B.val X p₀ hl) (sfRationalScalarUnit l B.val Y p₀ hl) ∧
    CoefficientIdentityLaw (rationalH l B.val j p d (s B))
      (rationalC l Ω p₀ hl Y B B (le_refl B))
      (rationalC l Ω p₀ hl X B B (le_refl B)) (q.a B B (le_refl B))
      (sfRationalScalarUnit l B.val Y p₀ hl) (sfRationalScalarUnit l B.val X p₀ hl)
```

## Users

The downstream searches for IntegralComparisons and RationalCocycles found no
importing modules. The module itself has no downstream importers; unrelated namespaces reuse
some of these short names but do not refer to these definitions. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | S5 | Same equations, represented through generic predicates; coefficient proof consumes them. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | Add proved API equations only; all existing declarations and users are unchanged. |

The additional public object and tensor-map equations in
Sheaf.Paper.SfRationalizationKaroubi are proved API lemmas only; they change no
existing definition, signature, attribute, or import. Its existing users require
no adaptation.

## Status

landed 20261026T071007-L-3744196 2026-10-26 (merge of deliver/S5/Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams)

Private proof API: `LiftData` records the specified object and morphism equations
for a functor commuting with localization. Its proved composition rule and four
abstract diagram-transport theorems keep intermediate-field coercions and derived
category constructions out of the component calculations. Concrete proved
`localizedLift` and `coefficientLift` lemmas instantiate this API. These helpers
occur only in theorem proofs, have no holes, and add no public signatures or
mathematical assumptions.

Local proof-context irreducibility also keeps `instCategoryDerivedCategory`,
`Padic.coefficientExtensionIntegers`, `sfIntegralConstructibleLinear`,
`sfIntegralCoefficientLinear` and `DerivedCategory.instPreadditive` folded.
These are local elaboration settings;
the declarations and their exported attributes are unchanged.

Proved heterogeneous map/unit/counit APIs let `localized` remain locally
irreducible in the coefficient helper and comparison-proof sections. The section
scopes restore its original status before the condensed-realization proof.
`raw_exists` specializes a private generic constructor for the existing
`LocalizedAdjunctionData`, retaining every original field and formula.

Coefficient inclusions now give explicit source and target intermediate fields.
These are the same canonical `IntermediateField.inclusion` maps, with their
implicit field arguments written out to avoid recovering them from order proofs.

The coefficient section also folds the uniformizer and constructibility predicate.
The coherence helpers and comparison proof locally fold the localization and
full-subcategory category, preadditive and linear instances. Explicit category
arguments in transport applications avoid reconstructing this data from Hom
types. These changes affect proof elaboration only and end before the original
condensed-realization proof.

The final assembly proof locally folds `integralC` and `rationalC`; their exported
abbreviation status and values are unchanged. The instance-search bound decreases
from 4096 to 512; all declarations type-check with this smaller search bound.
Profiling settings have been removed from the delivered source.

Proof elaboration is sequential (`Elab.async false`). The coefficient proof
explicitly destructs its existing algebraic-closure instance so that the original
anonymous instance binder is retained without an unused-section-variable warning.
No linter or transparency check is disabled.
