# Cached coefficient composition and square predicate

## Reason

The inherited attempt timed out when taking components of the concrete square
comparison. The ambient API now fixes the cached functors in its composition signature
and gives the same three maps objectwise. The final categorical square argument also
needed a general square predicate: a direct instantiation of its component formula
spent over 27 seconds and 100000 heartbeats in the kernel before failing, even with an
abstract realization family. FunctorComparisonSquare lets the categorical argument be
checked before substituting derived functors. CoefficientPullbackSquare specializes
that predicate to its original exact equation. No public signature changes.
The API module is unclaimed; no other existing module is adapted.

## Old

```lean
/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[no_expose, irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' f

/-- Component equation for the cached square, without reducing its morphism projections. -/
theorem coefficientAmbientSquare_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (coefficientAmbientSquare Λ sq).app K =
      ((leftDerivedUpperStarComp Λ f' g).app K).symm ≪≫
        (eqToIso (by rw [← sq.w]) :
          L(((f' ≫ g))^*⟦Λ⟧) ≅ L(((g' ≫ f))^*⟦Λ⟧)).app K ≪≫
        (leftDerivedUpperStarComp Λ g' f).app K := by
  unfold coefficientAmbientSquare
  rw [NatIso.trans_app, NatIso.trans_app]
  change ((leftDerivedUpperStarComp Λ f' g).app K).symm ≪≫ _ ≪≫ _ = _
  rfl

/-- Square coherence for a specified family of inverse-image comparisons. -/
def CoefficientPullbackSquare (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)))
    (pullback : CoefficientPullbackFamily B Λ F) : Prop :=
  ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
      (K : FiniteDiscreteEtalePlus B Y),
    (F X').map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app K) ≫
      (pullback g').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj K) ≫
      (coefficientDerivedUpperStar Λ g').map
        ((pullback f).hom.app K) =
    (pullback f').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar Λ f').map
        ((pullback g).hom.app K) ≫
      (coefficientAmbientSquare Λ sq).hom.app
        ((F Y).obj K)
```

## New

```lean
/-- Composition of derived pullbacks, with the cached functors in its signature. -/
noncomputable def coefficientDerivedUpperStarComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    coefficientDerivedUpperStar Λ (f ≫ g) ≅
      coefficientDerivedUpperStar Λ g ⋙ coefficientDerivedUpperStar Λ f :=
  leftDerivedUpperStarComp Λ f g

/-- Compose three natural isomorphisms through their objectwise components. -/
noncomputable def coefficientIsoTransThree
    {C D : Type*} [Category C] [Category D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) : F₀ ≅ F₃ :=
  NatIso.ofComponents (fun N ↦ a.app N ≪≫ b.app N ≪≫ c.app N) (by
    intro N M k
    simp only [Iso.trans_hom, Iso.app, Category.assoc]
    rw [a.hom.naturality_assoc, b.hom.naturality_assoc, c.hom.naturality])

/-- Components of the objectwise composite. -/
theorem coefficientIsoTransThree_hom_app
    {C D : Type*} [Category C] [Category D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (N : C) :
    (coefficientIsoTransThree a b c).hom.app N =
      a.hom.app N ≫ b.hom.app N ≫ c.hom.app N := by
  rfl

/-- The objectwise composite is the usual composite of natural isomorphisms. -/
theorem coefficientIsoTransThree_eq
    {C D : Type*} [Category C] [Category D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) :
    coefficientIsoTransThree a b c = a ≪≫ b ≪≫ c := by
  ext N
  rfl

/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[no_expose, irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
    (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
    (coefficientDerivedUpperStarComp Λ g' f)

/-- Equation for the objectwise construction of the cached ambient square. -/
theorem coefficientAmbientSquare_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientAmbientSquare Λ sq =
      coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
        (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
        (coefficientDerivedUpperStarComp Λ g' f) := by
  unfold coefficientAmbientSquare
  rfl

/-- Component equation for the cached square, without reducing its morphism projections. -/
theorem coefficientAmbientSquare_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (coefficientAmbientSquare Λ sq).app K =
      ((leftDerivedUpperStarComp Λ f' g).app K).symm ≪≫
        (eqToIso (by rw [← sq.w]) :
          L(((f' ≫ g))^*⟦Λ⟧) ≅ L(((g' ≫ f))^*⟦Λ⟧)).app K ≪≫
        (leftDerivedUpperStarComp Λ g' f).app K := by
  unfold coefficientAmbientSquare
  rw [coefficientIsoTransThree_eq, NatIso.trans_app, NatIso.trans_app]
  change ((leftDerivedUpperStarComp Λ f' g).app K).symm ≪≫ _ ≪≫ _ = _
  rfl

/-- The component formula for the ambient square comparison. -/
theorem coefficientAmbientSquare_hom_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (coefficientAmbientSquare Λ sq).hom.app N =
      (coefficientDerivedUpperStarComp Λ f' g).inv.app N ≫
        (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm)).hom.app N ≫
        (coefficientDerivedUpperStarComp Λ g' f).hom.app N := by
  unfold coefficientAmbientSquare
  exact coefficientIsoTransThree_hom_app
    (coefficientDerivedUpperStarComp Λ f' g).symm
    (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
    (coefficientDerivedUpperStarComp Λ g' f) N

/-- Square coherence for functor comparisons between two families of categories. -/
def FunctorComparisonSquare
    {K : Type*} [Category K] {C D : K → Type*}
    [∀ X, Category (C X)] [∀ X, Category (D X)]
    (E : ∀ {X Y : K}, (X ⟶ Y) → C Y ⥤ C X)
    (I : ∀ {X Y : K}, (X ⟶ Y) → D Y ⥤ D X)
    (F : ∀ X, C X ⥤ D X)
    (p : ∀ {X Y : K} (f : X ⟶ Y), E f ⋙ F X ≅ F Y ⋙ I f)
    (θ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X}, CommSq g' f' f g → (E g ⋙ E f' ≅ E f ⋙ E g'))
    (φ : ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X}, CommSq g' f' f g → (I g ⋙ I f' ≅ I f ⋙ I g')) : Prop :=
  ∀ {X Y X' Y' : K} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (N : C Y),
    (F X').map ((θ sq).hom.app N) ≫ (p g').hom.app ((E f).obj N) ≫
      (I g').map ((p f).hom.app N) =
    (p f').hom.app ((E g).obj N) ≫ (I f').map ((p g).hom.app N) ≫
      (φ sq).hom.app ((F Y).obj N)

/-- Square coherence for a specified family of inverse-image comparisons. -/
def CoefficientPullbackSquare (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)))
    (pullback : CoefficientPullbackFamily B Λ F) : Prop :=
  @FunctorComparisonSquare Scheme.{u} _
    (fun T ↦ FiniteDiscreteEtalePlus B T)
    (fun T ↦ DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun {_ _} h ↦
      D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h))
    (fun {_ _} h ↦ coefficientDerivedUpperStar Λ h) F pullback
    (fun {_ _ _ _} {_ _ _ _} sq ↦
      Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq)
    (fun {_ _ _ _} {_ _ _ _} sq ↦ coefficientAmbientSquare Λ sq)
```

coefficientDerivedUpperStarComp is the existing leftDerivedUpperStarComp with cached
source and target functors. coefficientIsoTransThree_eq proves that the objectwise
constructor is the ordinary triple composite. The equality transport is congrArg of
the cached functor; proof irrelevance identifies it with the former rewrite proof.
FunctorComparisonSquare contains exactly the original universally quantified component
equation. Substituting the displayed functor and square families recovers the old
CoefficientPullbackSquare definition by beta reduction; its binders and morphisms are
identical. The generic predicate's displayed equation is checked by Iff.rfl.
The unchanged FiniteDiscreteDerivedCoefficientData consumer compiles against this API.
A concrete Iff.rfl check of the old specialized equation triggers the same expensive
kernel conversion that motivated caching the predicate; the independent reader should
compare the explicit substitution above. These definitions occur in target statements, so the independent statement reader
should confirm the preserved meaning.

## Users

Refreshed against current main on 2026-10-17. The downstream query reports
24 downstream modules. The textual users of coefficientAmbientSquare are the
API itself and Sheaf.Paper.CoefficientExchangeFromComparisons; the latter was missing
from the returned delivery's table. CoefficientPullbackSquare is mentioned by the
API, the assigned square-coherence module and FiniteDiscreteDerivedCoefficientData.
All downstream modules and both other delivered modules are listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Cache composition and generic square predicate; preserve existing no_expose attributes and both equation APIs. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | A4 | Uses coefficientAmbientSquare and coefficientAmbientSquare_app. Preserve the latter signature and triple-component equation; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | B2 | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | B3 | Proved ordinary comparison composition lemma; generic mate proof specializes directly. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Complete square proof through the generic predicate and cached square equation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Unchanged direct consumer; its two square fields retain the same predicate and equation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged target/importer; preserved definition meaning requires independent statement review. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| TargetsCheck | unclaimed | Unchanged target/importer; preserved definition meaning requires independent statement review. |
| WeilConjectures | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged transitive user; identical comparison and square equation, no adaptation. |

No downstream source module is adapted. In particular the independent reader should
compile the unchanged CoefficientExchangeFromComparisons consumer against the new API.
This repair compiled that consumer against both the baseline and the delivered overlay;
both pass with the same pre-existing style warnings.
The existing coefficientDerivedAdjunction_eq and coefficientAmbientSquare_app are retained
with their exact current-main signatures and visibility. The new coefficientAmbientSquare_eq
allows the assigned module to use the cached body without exposing it. The new app proof
rewrites coefficientIsoTransThree_eq and NatIso.trans_app; proof irrelevance identifies
the two equality-transport witnesses. Thus the consumer's existing restricted_square_iso
proof continues to use exactly its original component equation.


The inherited change to WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
is unnecessary with the generic predicate and is removed from this delivery.

## Status

landed 20261017T021559-L-693446 2026-10-17 (merge of deliver/B3/Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence)
