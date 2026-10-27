# WeilConjectures.RamifiedScalarSystemTranspose.SystemAdjunction

## Reason

The large record mixes functor and adjunction data with eight dependent coherence
proofs. The main file has exceeded the 60-second compile guard. Package the same
proofs in a Prop record over the same data, so using a data field does not expand
all eight coherence propositions. This is a representation repair, with no new
assumptions, mathematical equations, or holes. It stays within the item's module.

## Old

```lean
structure SystemAdjunction
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)] where
  support_preserves : ∀ M, domain C τ X M →
    domain C τ Y ((support C τ c).obj M)
  G : (domain C τ Y).FullSubcategory ⥤ (domain C τ X).FullSubcategory
  adjunction : (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
    (fun M ↦ support_preserves M.obj M.property) ⊣ G
  finite : ∀ n : ℕ, AdjointDatum (C n) c
  left : ∀ n : ℕ,
    (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
      (fun M ↦ support_preserves M.obj M.property) ⋙ evaluation C τ Y n ≅
        evaluation C τ X n ⋙ restrict (lower (C n) c) (finite n).lower_preserves
  /-- No twist of the support evaluation is allowed: this is the specified geometric map. -/
  left_canonical : ∀ (n : ℕ) (M : (domain C τ X).FullSubcategory),
    ((left n).hom.app M).hom = (canonicalSupportEvaluation C τ c n).hom.app M.obj
  right : ∀ n : ℕ, G ⋙ evaluation C τ X n ≅
    evaluation C τ Y n ⋙ restrict (upper (C n) c) (finite n).upper_preserves
  unit : ∀ (n : ℕ) (M : (domain C τ X).FullSubcategory),
    (evaluation C τ X n).map (adjunction.unit.app M) ≫
      (right n).hom.app _ ≫
        (restrict (upper (C n) c) (finite n).upper_preserves).map ((left n).hom.app M) =
      (finite n).adjunction.unit.app ((evaluation C τ X n).obj M)
  counit : ∀ (n : ℕ) (N : (domain C τ Y).FullSubcategory),
    (left n).hom.app (G.obj N) ≫
      (restrict (lower (C n) c) (finite n).lower_preserves).map ((right n).hom.app N) ≫
        (finite n).adjunction.counit.app ((evaluation C τ Y n).obj N) =
      (evaluation C τ Y n).map (adjunction.counit.app N)

  /-- The specified finite exceptional quotient comparisons, at the actual exponents. -/
  quotient : ∀ {m n : ℕ} (h : n ≤ m),
    Change (quotientMap C τ h).hom c (finite m) (finite n)
  /-- Evaluation of the actual exceptional system transition is that quotient mate. -/
  exceptionalTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (N : (domain C τ Y).FullSubcategory),
    red C τ X h (G.obj N).obj ≫ ((right n).hom.app N).hom =
      (tensor (quotientMap C τ h).hom X).map (((right m).hom.app N).hom) ≫
        (quotient h).mate.hom.app ((evaluation C τ Y m).obj N) ≫
        (upper (C n) c).map (red C τ Y h N.obj)
  /-- The corresponding compact-support transition, with the same finite comparison. -/
  supportTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : (domain C τ X).FullSubcategory),
    red C τ Y h
        (((domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
          (fun K ↦ support_preserves K.obj K.property)).obj M).obj ≫
        ((left n).hom.app M).hom =
      (tensor (quotientMap C τ h).hom Y).map (((left m).hom.app M).hom) ≫
        (quotient h).projection.hom.app ((evaluation C τ X m).obj M) ≫
        (lower (C n) c).map (red C τ X h M.obj)
  /-- The compact-support quotient cocycle uses those same projection maps. -/
  projection_comp : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (M : (ctf (C r) X).FullSubcategory),
    (tensor (quotientMap C τ k).hom Y).map ((quotient h).projection.hom.app M) ≫
        (quotient k).projection.hom.app
          ⟨(tensor (quotientMap C τ h).hom X).obj M.obj,
            (quotient h).tensor_preserves_X M.obj M.property⟩ ≫
        (lower (C n) c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
            (quotientMap C τ h).hom (quotientMap C τ k).hom
            (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app M.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
          (quotientMap C τ h).hom (quotientMap C τ k).hom
          (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app
            ((lower (C r) c).obj M.obj) ≫
        (quotient (k.trans h)).projection.hom.app M
  /-- The finite exceptional quotient cocycle, including its tensor reassociation. -/
  quotient_comp : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (N : (ctf (C r) Y).FullSubcategory),
    (tensor (quotientMap C τ k).hom X).map ((quotient h).mate.hom.app N) ≫
        (quotient k).mate.hom.app
          ⟨(tensor (quotientMap C τ h).hom Y).obj N.obj,
            (quotient h).tensor_preserves_Y N.obj N.property⟩ ≫
        (upper (C n) c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
            (quotientMap C τ h).hom (quotientMap C τ k).hom
            (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app N.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
          (quotientMap C τ h).hom (quotientMap C τ k).hom
          (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app
            ((upper (C r) c).obj N.obj) ≫
        (quotient (k.trans h)).mate.hom.app N

  /-- The equal-index quotient mate is the canonical scalar-unit identification. -/
  quotient_id : ∀ (n : ℕ) (N : (ctf (C n) Y).FullSubcategory),
    (quotient (le_refl n)).mate.hom.app N ≫
        (upper (C n) c).map
          ((ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
            (quotientMap C τ (le_refl n)).hom (quotientMap_id C τ n)).hom.app N.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        (quotientMap C τ (le_refl n)).hom (quotientMap_id C τ n)).hom.app
          ((upper (C n) c).obj N.obj)
```

## New

```lean
/-- Cache the existing category structure on the ordinary derived systems.
Source: Zheng 4.1 and the canonical localization category
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
@[instance_reducible]
def systemCategory (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (W : Scheme.{u}) : Category.{u + 2} (Derived C τ W) := inferInstance

attribute [local instance] systemCategory

structure SystemAdjunctionData
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)] where
  support_preserves : ∀ M, domain C τ X M →
    domain C τ Y ((support C τ c).obj M)
  G : (domain C τ Y).FullSubcategory ⥤ (domain C τ X).FullSubcategory
  adjunction : (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
    (fun M ↦ support_preserves M.obj M.property) ⊣ G
  finite : ∀ n : ℕ, AdjointDatum (C n) c
  left : ∀ n : ℕ,
    (domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
      (fun M ↦ support_preserves M.obj M.property) ⋙ evaluation C τ Y n ≅
        evaluation C τ X n ⋙ restrict (lower (C n) c) (finite n).lower_preserves
  right : ∀ n : ℕ, G ⋙ evaluation C τ X n ≅
    evaluation C τ Y n ⋙ restrict (upper (C n) c) (finite n).upper_preserves
  quotient : ∀ {m n : ℕ} (h : n ≤ m),
    Change (quotientMap C τ h).hom c (finite m) (finite n)

/-- The original eight coherence equations, separated from the adjunction data.
Source: Zheng 4.10; the stipulated finite adjunction and quotient coherences
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
structure SystemAdjunctionLaws
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)]
    (d : SystemAdjunctionData C τ c) : Prop where
  left_canonical : ∀ (n : ℕ) (M : (domain C τ X).FullSubcategory),
    ((d.left n).hom.app M).hom = (canonicalSupportEvaluation C τ c n).hom.app M.obj
  unit : ∀ (n : ℕ) (M : (domain C τ X).FullSubcategory),
    (evaluation C τ X n).map (d.adjunction.unit.app M) ≫
      (d.right n).hom.app _ ≫
        (restrict (upper (C n) c) (d.finite n).upper_preserves).map ((d.left n).hom.app M) =
      (d.finite n).adjunction.unit.app ((evaluation C τ X n).obj M)
  counit : ∀ (n : ℕ) (N : (domain C τ Y).FullSubcategory),
    (d.left n).hom.app (d.G.obj N) ≫
      (restrict (lower (C n) c) (d.finite n).lower_preserves).map ((d.right n).hom.app N) ≫
        (d.finite n).adjunction.counit.app ((evaluation C τ Y n).obj N) =
      (evaluation C τ Y n).map (d.adjunction.counit.app N)
  exceptionalTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (N : (domain C τ Y).FullSubcategory),
    red C τ X h (d.G.obj N).obj ≫ ((d.right n).hom.app N).hom =
      (tensor (quotientMap C τ h).hom X).map (((d.right m).hom.app N).hom) ≫
        (d.quotient h).mate.hom.app ((evaluation C τ Y m).obj N) ≫
        (upper (C n) c).map (red C τ Y h N.obj)
  supportTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : (domain C τ X).FullSubcategory),
    red C τ Y h
        (((domain C τ Y).lift ((domain C τ X).ι ⋙ support C τ c)
          (fun K ↦ d.support_preserves K.obj K.property)).obj M).obj ≫
        ((d.left n).hom.app M).hom =
      (tensor (quotientMap C τ h).hom Y).map (((d.left m).hom.app M).hom) ≫
        (d.quotient h).projection.hom.app ((evaluation C τ X m).obj M) ≫
        (lower (C n) c).map (red C τ X h M.obj)
  projection_comp : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (M : (ctf (C r) X).FullSubcategory),
    (tensor (quotientMap C τ k).hom Y).map ((d.quotient h).projection.hom.app M) ≫
        (d.quotient k).projection.hom.app
          ⟨(tensor (quotientMap C τ h).hom X).obj M.obj,
            (d.quotient h).tensor_preserves_X M.obj M.property⟩ ≫
        (lower (C n) c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
            (quotientMap C τ h).hom (quotientMap C τ k).hom
            (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app M.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
          (quotientMap C τ h).hom (quotientMap C τ k).hom
          (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app
            ((lower (C r) c).obj M.obj) ≫
        (d.quotient (k.trans h)).projection.hom.app M
  quotient_comp : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
    (N : (ctf (C r) Y).FullSubcategory),
    (tensor (quotientMap C τ k).hom X).map ((d.quotient h).mate.hom.app N) ≫
        (d.quotient k).mate.hom.app
          ⟨(tensor (quotientMap C τ h).hom Y).obj N.obj,
            (d.quotient h).tensor_preserves_Y N.obj N.property⟩ ≫
        (upper (C n) c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
            (quotientMap C τ h).hom (quotientMap C τ k).hom
            (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app N.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
          (quotientMap C τ h).hom (quotientMap C τ k).hom
          (quotientMap C τ (k.trans h)).hom (quotientMap_comp C τ h k)).hom.app
            ((upper (C r) c).obj N.obj) ≫
        (d.quotient (k.trans h)).mate.hom.app N
  quotient_id : ∀ (n : ℕ) (N : (ctf (C n) Y).FullSubcategory),
    (d.quotient (le_refl n)).mate.hom.app N ≫
        (upper (C n) c).map
          ((ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
            (quotientMap C τ (le_refl n)).hom (quotientMap_id C τ n)).hom.app N.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        (quotientMap C τ (le_refl n)).hom (quotientMap_id C τ n)).hom.app
          ((upper (C n) c).obj N.obj)

/-- The stipulated system adjunction, with its unchanged data and coherence laws.
Source: Zheng 4.10; node first paragraph and finite adjunction clauses
(blueprint: lem-coef-ramified-scalar-system-transpose). -/
structure SystemAdjunction
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)] where
  data : SystemAdjunctionData C τ c
  laws : SystemAdjunctionLaws C τ c data
```

The local systemCategory instance is a specialization of the original canonical
category structure. It does not choose a new localization model or universe.
It is checked against the original instance by:

```lean
theorem systemCategory_original (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) (W : Scheme.{u}) :
    systemCategory C τ W =
      (inferInstance : Category.{u + 2} (Derived C τ W)) := by rfl
```

All fifteen original accessor names remain. G, adjunction, finite, left, right and
quotient are reducible abbreviations of the corresponding data projections.
support_preserves and the eight coherence accessors are proved projection aliases.
Their predicates, source and target functors, units, counits and quotient maps are
unchanged. The constructor now takes a data record and one proof package.

The representation check copies Old verbatim as OriginalSystemAdjunction and checks:

```lean
def systemAdjunctionRepresentationEquiv
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) [∀ n : ℕ, Finite (C n)] :
    OriginalSystemAdjunction C τ c ≃ SystemAdjunction C τ c where
  toFun sys :=
    { data :=
        { support_preserves := sys.support_preserves
          G := sys.G
          adjunction := sys.adjunction
          finite := sys.finite
          left := sys.left
          right := sys.right
          quotient := sys.quotient }
      laws :=
        { left_canonical := sys.left_canonical
          unit := sys.unit
          counit := sys.counit
          exceptionalTransition := sys.exceptionalTransition
          supportTransition := sys.supportTransition
          projection_comp := sys.projection_comp
          quotient_comp := sys.quotient_comp
          quotient_id := sys.quotient_id } }
  invFun sys :=
    { support_preserves := sys.support_preserves
      G := sys.G
      adjunction := sys.adjunction
      finite := sys.finite
      left := sys.left
      left_canonical := sys.left_canonical
      right := sys.right
      unit := sys.unit
      counit := sys.counit
      quotient := sys.quotient
      exceptionalTransition := sys.exceptionalTransition
      supportTransition := sys.supportTransition
      projection_comp := sys.projection_comp
      quotient_comp := sys.quotient_comp
      quotient_id := sys.quotient_id }
  left_inv := by intro sys; cases sys; rfl
  right_inv := by intro sys; cases sys; rfl
```

## Users

The downstream.py --uses audit finds no external use of SystemAdjunction.
The one direct importer is listed below. It is tested unchanged against the
new compiled interface. The target statements are unchanged; semantic review
should use the explicit equivalence above to compare the packaged definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | Data and coherence record packaging; same accessor predicates and comparison maps. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Direct importer; does not mention this SystemAdjunction record; no adaptation. |

No adopted WeilConjectures source file is changed.

Validation: the equivalence with the actual exported replacement record compiled in a
temporary verification module against the successful main-module artifact build. The
unchanged direct consumer also compiled against that artifact.

## Status

landed 20261026T022824-L-465056 2026-10-26 (merge of deliver/B4/Sheaf.Paper.RamifiedScalarSystemTranspose)
