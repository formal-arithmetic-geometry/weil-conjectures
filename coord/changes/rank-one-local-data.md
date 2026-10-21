# WeilConjectures.PurityFiniteSetting.RankOne.sectionComplex

## Reason

The support and Kummer proof modules must import the canonical local-calculation
interfaces without importing the theorem that uses them. Move the existing helper
declarations verbatim to `Sheaf.Paper.PurityRankOneLocalData`, publicly reexported
by the original module. No existing public declaration is removed or renamed.

The short-complex constructor previously inferred its third object through the
curried section functor. Specify all three objects explicitly, using the same
evaluation functors as the derived-cohomology statement. This is definitionally
the same short complex: its maps are the same kernel inclusion and restriction.
The reducible presentation lets Lean identify the homology instances when
rewriting the normalized snake boundary. A named proof of the adjacent-degree
relation replaces the anonymous `rfl`; proof irrelevance makes this identical.
No sheaf, cohomology group, boundary sign or target statement changes meaning.
Any target statement using these definitions retains exactly its prior meaning;
the independent statement review can verify the displayed definitional equalities.

## Old

```lean
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

def sectionComplex {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] {V W : C} (j : W ⟶ V)
    (I : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).app I)
    ((NatTrans.mapHomologicalComplex
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).app I)
    (by ext n : 1; exact kernel.condition ((I.X n).obj.map j.op))

def IsBoundary {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F) :
    Prop :=
  ∀ I : InjectiveResolution F, ∃ hI : (sectionComplex J A j I.cocomplex).ShortExact,
    δ = (I.isoRightDerivedObj (sections J A W) 1).hom ≫
      hI.δ 1 2 rfl ≫
      (I.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv

```

## New

```lean
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

/-- Curried evaluation has the same additive structure as the explicit section functor.
Source: functor composition and pointwise addition
(blueprint: def-pur-rank-one-local-data). -/
instance sheafSections_obj_additive
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :
    ((sheafSections J (ModuleCat.{u + 1} A)).obj (op W)).Additive :=
  inferInstanceAs ((sections J A W).Additive)

/-- Curried evaluation preserves finite limits, as explicit evaluation does.
Source: limits of sheaves and pointwise evaluation
(blueprint: def-pur-rank-one-local-data). -/
instance sheafSections_obj_preservesFiniteLimits
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :
    PreservesFiniteLimits ((sheafSections J (ModuleCat.{u + 1} A)).obj (op W)) :=
  inferInstanceAs (PreservesFiniteLimits (sections J A W))

@[reducible] def sectionComplex {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] {V W : C} (j : W ⟶ V)
    (I : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℕ) :=
  { X₁ := ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
      (.up ℕ)).obj I
    X₂ := ((sections J A V).mapHomologicalComplex (.up ℕ)).obj I
    X₃ := ((sections J A W).mapHomologicalComplex (.up ℕ)).obj I
    f := ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).app I)
    g := ((NatTrans.mapHomologicalComplex
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).app I)
    zero := by ext n : 1; exact kernel.condition ((I.X n).obj.map j.op) }

/-- The adjacent nonnegative support degrees, used to keep the snake-boundary
index proof stable under rewriting. Source: the support sequence, Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
theorem support_degree_relation : (ComplexShape.up ℕ).Rel 1 2 := rfl

/-- A support boundary is exactly the snake boundary on injective section complexes,
transported by the canonical resolution comparisons. This characterization rules out
both an arbitrary isomorphism and an arbitrary choice of sign.
Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def IsBoundary {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F) :
    Prop :=
  ∀ I : InjectiveResolution F, ∃ hI : (sectionComplex J A j I.cocomplex).ShortExact,
    δ = (I.isoRightDerivedObj (sections J A W) 1).hom ≫
      hI.δ 1 2 support_degree_relation ≫
      (I.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv
```

All other existing helper signatures and bodies are copied unchanged. Original
public imports remain available through the new public import of the data module;
the support API remains provided by `Sheaf.AlgebraicGeometry.SupportLongExact`.
Unused original proof imports are removed. Two new proved instances,
`sheafSections_obj_additive` and `sheafSections_obj_preservesFiniteLimits`,
expose the existing pointwise evaluation structures to instance synthesis for
curried section functors. Their bodies use `inferInstanceAs` of the explicit
`sections` functor. They add no assumptions and change no evaluation map.

## Users

Rechecked against the current `sheaf-dag` sources for the return of head
`9df0da84a6b`. `tools/downstream.py Sheaf.Paper.PurityRankOneLocalCalculation
--uses sections openImmersion_isOpenImmersion openObject restriction proCoefficient
sectionComplex IsBoundary evaluationRepresented evaluationExt kummerClass
comparisonSections comparisonCohomology constantUnit` reports 55 downstream
modules. Its whole-word textual matches include the three consumers below as
well as the item. The new modules below belong to this same delivery.

Read each reported consumer: `restriction` in `LocalizedFlagProduct` is the
locally bound input of `LocalizedFlagForgetCharacterization`; `sections` in
`LocalizedTopChern` and `VectorBundleThomClass` denotes global sections of
scheme modules. These matches do not refer to the rank-one declarations.
Nevertheless all three are listed explicitly for the landing's conservative
consumer check. No consumer statement, definition or proof requires adaptation;
the relocated rank-one interfaces retain their names and remain publicly
available through the original module. No claim lock for any of these three
modules is present in the current claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurityRankOneLocalCalculation | G6 | Public data import; prove the unchanged theorem. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Textual `restriction` match is a local binder; no semantic effect or adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Textual `sections` matches are scheme-module sections; no semantic effect or adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Textual `sections` matches are scheme-module sections; no semantic effect or adaptation. |
| Sheaf.Paper.PurityRankOneLocalData | new, G6 | Canonical definitions relocated here. |
| Sheaf.Paper.RankOneClassicalSupportComparison | new, G6 | Uses the normalized section complexes. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | new, G6 | Uses the unchanged evaluation and twist. |
| Sheaf.Paper.RankOneKummerMonomial | new, G6 | Uses the unchanged coefficient Kummer class. |
| Sheaf.Paper.RankOneKummerGenerator | new, G6 | Uses the unchanged coefficient Kummer class. |

## Status

landed 20261021T225136-L-3779193 2026-10-21 (merge of deliver/G6/Sheaf.Paper.PurityRankOneLocalCalculation)
