# WeilConjectures.RationalizedSmoothAdjunction.Raw, IntegralComparisons, RationalComparisons

## Reason

The completed proof must compile within 60 seconds. A traced compile identifies
these scheme- and coefficient-indexed record declarations as major costs.
The trace attributes about 7.8 seconds to `Raw`'s kernel check, 5.7 seconds to
`IntegralComparisons`' kernel check, and further substantial time to their
recursors and no-confusion machinery. The `RationalComparisons` command is also
expensive. Rechecking generic record machinery at these full expressions is
unnecessary. Specialize generic records with exactly the same fields instead.
The generic records stay in this same module, so this does not split the file
or move its proof to evade the compile limit.

Every mathematical field and equation is preserved. In `Raw`, the original
localization functor maps an integral arrow to its tensor with one, so the new
unit and counit right sides are definitionally the old right sides. All other
`Raw` fields substitute the identical categories, functors, scalar and integral
adjunction. For both comparison records, the old field types are copied
verbatim as the generic records' type and predicate arguments. In particular
all four rational HEq formulas and both adjunction equations are retained.
No data are supplied by arbitrary existence choices. No target statement,
coefficient construction, endpoint or compatibility condition is weakened.

## Old

Within the existing sections and their unchanged parameters:

```lean
structure Raw where
  adjunction : rationalP l E j p d s ⊣ rationalH l E j p d s
  hom_tmul : ∀ (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y)
    (h : (P l E j p d s).obj M ⟶ K)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    adjunction.homEquiv ⟨M⟩ ⟨K⟩ (a ⊗ₜ h) =
      a ⊗ₜ (RationalizedSmoothAdjunction.adjunction l E j p d s).homEquiv M K h
  inv_tmul : ∀ (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y)
    (h : M ⟶ (H l E j p d s).obj K)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    (adjunction.homEquiv ⟨M⟩ ⟨K⟩).symm (a ⊗ₜ h) =
      a ⊗ₜ ((RationalizedSmoothAdjunction.adjunction l E j p d s).homEquiv M K).symm h
  hom_add : ∀ (M : sfRationalConstructibleCategory l E X)
    (K : sfRationalConstructibleCategory l E Y)
    (h h' : (rationalP l E j p d s).obj M ⟶ K),
    adjunction.homEquiv M K (h + h') = adjunction.homEquiv M K h +
      adjunction.homEquiv M K h'
  hom_smul : ∀ (M : sfRationalConstructibleCategory l E X)
    (K : sfRationalConstructibleCategory l E Y)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (h : (rationalP l E j p d s).obj M ⟶ K),
    adjunction.homEquiv M K (a • h) = a • adjunction.homEquiv M K h
  unit : ∀ M : sfIntegralConstructibleCategory l E X,
    adjunction.unit.app ⟨M⟩ = (sfRationalConstructibleLocalization l E X).map
      ((RationalizedSmoothAdjunction.adjunction l E j p d s).unit.app M)
  counit : ∀ K : sfIntegralConstructibleCategory l E Y,
    adjunction.counit.app ⟨K⟩ = (sfRationalConstructibleLocalization l E Y).map
      ((RationalizedSmoothAdjunction.adjunction l E j p d s).counit.app K)

structure IntegralComparisons where
  b : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    P l B.val j p d (s B) ⋙ integralC l Ω p₀ hl Y B F h ≅
      integralC l Ω p₀ hl X B F h ⋙ P l F.val j p d (s F)
  a : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    H l B.val j p d (s B) ⋙ integralC l Ω p₀ hl X B F h ≅
      integralC l Ω p₀ hl Y B F h ⋙ H l F.val j p d (s F)
  unit : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    (integralC l Ω p₀ hl X B F h).map ((adjunction l B.val j p d (s B)).unit.app M) ≫
      (a B F h).hom.app ((P l B.val j p d (s B)).obj M) ≫
      (H l F.val j p d (s F)).map ((b B F h).hom.app M) =
        (adjunction l F.val j p d (s F)).unit.app
          ((integralC l Ω p₀ hl X B F h).obj M)
  counit : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    (b B F h).hom.app ((H l B.val j p d (s B)).obj K) ≫
      (P l F.val j p d (s F)).map ((a B F h).hom.app K) ≫
      (adjunction l F.val j p d (s F)).counit.app
        ((integralC l Ω p₀ hl Y B F h).obj K) =
      (integralC l Ω p₀ hl Y B F h).map ((adjunction l B.val j p d (s B)).counit.app K)

structure RationalComparisons where
  b : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalP l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl Y B F h ≅
      rationalC l Ω p₀ hl X B F h ⋙ rationalP l F.val j p d (s F)
  a : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F),
    rationalH l B.val j p d (s B) ⋙ rationalC l Ω p₀ hl X B F h ≅
      rationalC l Ω p₀ hl Y B F h ⋙ rationalH l F.val j p d (s F)
  b_hom : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).hom.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).hom.app M))
  b_inv : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfIntegralConstructibleCategory l B.val X),
    HEq ((b B F h).inv.app ⟨M⟩)
      ((sfRationalConstructibleLocalization l F.val Y).map ((c.b B F h).inv.app M))
  a_hom : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).hom.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).hom.app K))
  a_inv : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfIntegralConstructibleCategory l B.val Y),
    HEq ((a B F h).inv.app ⟨K⟩)
      ((sfRationalConstructibleLocalization l F.val X).map ((c.a B F h).inv.app K))
  unit : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (M : sfRationalConstructibleCategory l B.val X),
    (rationalC l Ω p₀ hl X B F h).map ((r B).adjunction.unit.app M) ≫
      (a B F h).hom.app ((rationalP l B.val j p d (s B)).obj M) ≫
      (rationalH l F.val j p d (s F)).map ((b B F h).hom.app M) =
        (r F).adjunction.unit.app ((rationalC l Ω p₀ hl X B F h).obj M)
  counit : ∀ (B F : Padic.FiniteCoefficientFields l Ω) (h : B ≤ F)
    (K : sfRationalConstructibleCategory l B.val Y),
    (b B F h).hom.app ((rationalH l B.val j p d (s B)).obj K) ≫
      (rationalP l F.val j p d (s F)).map ((a B F h).hom.app K) ≫
      (r F).adjunction.counit.app ((rationalC l Ω p₀ hl Y B F h).obj K) =
        (rationalC l Ω p₀ hl Y B F h).map ((r B).adjunction.counit.app K)
```

## New

Within those same sections and parameters:

```lean
structure LocalizedAdjunctionData {R : Type r} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
    (t : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (a : F ⊣ G) where
  adjunction : localized t F ⊣ localized t G
  hom_tmul : ∀ (M : C) (K : D) (f : F.obj M ⟶ K) (b : Localization.Away t),
    adjunction.homEquiv ⟨M⟩ ⟨K⟩ (b ⊗ₜ[R] f) = b ⊗ₜ[R] a.homEquiv M K f
  inv_tmul : ∀ (M : C) (K : D) (f : M ⟶ G.obj K) (b : Localization.Away t),
    (adjunction.homEquiv ⟨M⟩ ⟨K⟩).symm (b ⊗ₜ[R] f) =
      b ⊗ₜ[R] (a.homEquiv M K).symm f
  hom_add : ∀ (M : ScalarLocalization R C t) (K : ScalarLocalization R D t)
    (f g : (localized t F).obj M ⟶ K),
    adjunction.homEquiv M K (f + g) = adjunction.homEquiv M K f + adjunction.homEquiv M K g
  hom_smul : ∀ (M : ScalarLocalization R C t) (K : ScalarLocalization R D t)
    (b : Localization.Away t) (f : (localized t F).obj M ⟶ K),
    adjunction.homEquiv M K (b • f) = b • adjunction.homEquiv M K f
  unit : ∀ M : C, adjunction.unit.app ⟨M⟩ = 1 ⊗ₜ[R] a.unit.app M
  counit : ∀ K : D, adjunction.counit.app ⟨K⟩ = 1 ⊗ₜ[R] a.counit.app K

abbrev Raw := LocalizedAdjunctionData (Padic.coefficientExtensionUniformizer l E)
  (P l E j p d s) (H l E j p d s) (adjunction l E j p d s)

structure AdjunctionComparisonsData (B : Type r) (A : Type v)
    (unitLaw counitLaw : B → A → Prop) where
  b : B
  a : A
  unit : unitLaw b a
  counit : counitLaw b a

structure LocalizedComparisonsData (B : Type r) (A : Type v)
    (bHom bInv : B → Prop) (aHom aInv : A → Prop)
    (unitLaw counitLaw : B → A → Prop) where
  b : B
  a : A
  b_hom : bHom b
  b_inv : bInv b
  a_hom : aHom a
  a_inv : aInv a
  unit : unitLaw b a
  counit : counitLaw b a

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

The three original names are now abbreviations of generic records. Dot field
access and record construction have the same fields. Their former qualified
projection names, constructors, recursors and no-confusion helpers are replaced
by those of the generic records; no importing source uses those old names.
All theorem statements mentioning the records retain their exact source text.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | J1 | Same field access and record construction; six theorem proofs added. |

The source-only `tools/downstream.py` check reports zero downstream modules and
uses only in the item itself. A source search also finds no qualified uses of
the old generated auxiliary declarations. No other module is adapted. This
does not withdraw the item or any of its DAG dependencies.

## Status

landed 20261026T001840-L-36058 2026-10-26 (merge of deliver/J1/Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams)
