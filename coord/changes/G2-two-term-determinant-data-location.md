# AlgebraicGeometry.TwoTermDeterminantModel and the two-term determinant data

## Reason

The affine construction and descent statements must refer to the model and comparison
definitions without importing their assembly theorem. Move these unchanged definitions
to Sheaf.TraceFormula.TwoTermPerfectDeterminantData. The old module publicly imports it.
Every public name, universe, binder, body and visibility is unchanged. All old public
imports are retained verbatim in the definition module. No adopted source declaration is
modified. The original existence theorem keeps exactly its signature. No target meaning
changes. This is a dependency separation, not a mathematical definition repair.

## Old

In Sheaf.TraceFormula.TwoTermPerfectDeterminant:

```lean
/-- A constant-rank two-term model, allowed on each member of a varying-rank cover.
Source: Stacks, 0FJX and 0FJI (blueprint: lem-trf-two-term-perfect-determinant). -/
structure TwoTermDeterminantModel (X : Scheme.{u}) where
  /-- The term in degree minus one. -/
  neg : X.Modules
  /-- The term in degree zero. -/
  nonneg : X.Modules
  /-- The only nonzero differential. -/
  differential : neg ⟶ nonneg
  /-- The rank in degree minus one. -/
  negRank : ℕ
  /-- The rank in degree zero. -/
  nonnegRank : ℕ
  /-- Local freeness of the negative term. -/
  neg_free : neg.IsFiniteLocallyFreeOfRank negRank
  /-- Local freeness of the degree-zero term. -/
  nonneg_free : nonneg.IsFiniteLocallyFreeOfRank nonnegRank

/-- The actual complex supported in degrees minus one and zero of a two-term model.
Source: Stacks, 0FJI (blueprint: lem-trf-two-term-perfect-determinant). -/
noncomputable def TwoTermDeterminantModel.complex {X : Scheme.{u}}
    (P : TwoTermDeterminantModel X) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  HomologicalComplex.double P.differential
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- The displayed dual-top-exterior tensor top-exterior line of a model.
Source: Stacks, 0FJI (blueprint: lem-trf-two-term-perfect-determinant). -/
noncomputable def TwoTermDeterminantModel.line {X : Scheme.{u}}
    (P : TwoTermDeterminantModel X) : X.Modules :=
  dual (exteriorSheaf P.neg P.negRank) ⊗ exteriorSheaf P.nonneg P.nonnegRank

/-- The contractible model `[E --id--> E]`, including rank zero.
Source: Stacks, 0FJI (blueprint: lem-trf-two-term-perfect-determinant). -/
def TwoTermDeterminantModel.identity {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
    (hE : E.IsFiniteLocallyFreeOfRank n) : TwoTermDeterminantModel X :=
  ⟨E, E, 𝟙 E, n, n, hE, hE⟩

variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Locally two-term finite locally free objects; no global rank or bound on X is imposed.
Source: Stacks, 0FJX (blueprint: lem-trf-two-term-perfect-determinant). -/
def isTwoTermPerfect (X : Scheme.{u}) : ObjectProperty (schemeDerivedCategory X) :=
  fun L ↦ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ P : TwoTermDeterminantModel U.toScheme,
      Nonempty ((derivedPullback U.ι).obj L ≅ DerivedCategory.Q.obj P.complex)

/-- The source groupoid has precisely the required derived objects and derived isomorphisms.
Source: Stacks, 0FJX (blueprint: lem-trf-two-term-perfect-determinant). -/
abbrev TwoTermPerfectCore (X : Scheme.{u}) := Core (isTwoTermPerfect X).FullSubcategory

/-- Read an invertible-module-valued functor on its underlying module.
Source: Stacks, 0FJX (blueprint: lem-trf-two-term-perfect-determinant). -/
def twoTermDeterminantValue {X : Scheme.{u}}
    (F : TwoTermPerfectCore X ⥤ Core X.Modules)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) : X.Modules :=
  (F.obj (Core.mk ⟨L, hL⟩)).of

/-- The comparison between any two presentations is the value on their derived isomorphism.
Source: Stacks, 0FJM and 0FJX (blueprint: lem-trf-two-term-perfect-determinant). -/
noncomputable def twoTermDeterminantIso {X : Scheme.{u}}
    (F : TwoTermPerfectCore X ⥤ Core X.Modules)
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M) :
    twoTermDeterminantValue F L hL ≅ twoTermDeterminantValue F M hM :=
  let x : TwoTermPerfectCore X := Core.mk
    (⟨L, hL⟩ : (isTwoTermPerfect X).FullSubcategory)
  let y : TwoTermPerfectCore X := Core.mk
    (⟨M, hM⟩ : (isTwoTermPerfect X).FullSubcategory)
  let e' : x.of ≅ y.of := by
    change (⟨L, hL⟩ : (isTwoTermPerfect X).FullSubcategory) ≅
      (⟨M, hM⟩ : (isTwoTermPerfect X).FullSubcategory)
    exact (isTwoTermPerfect X).isoMk e
  let f : x ⟶ y := CoreHom.mk e'
  (F.map f).iso

/-- The localization of the actual zero complex.
Source: Stacks, 0FJI (blueprint: lem-trf-two-term-perfect-determinant). -/
noncomputable def twoTermDeterminantZeroObject (X : Scheme.{u}) : schemeDerivedCategory X :=
  DerivedCategory.Q.obj (0 : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)

/-- The ordinary identity comparison is fixed by the tensor-pullback adjunction.
Source: Stacks, 0096 and 0097 (blueprint: lem-trf-two-term-perfect-determinant). -/
noncomputable def twoTermDeterminantPullbackId (X : Scheme.{u}) :
    tensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  tensorPullbackSectionId X

/-- The composition lift from the retained K-flat counits and the section-normalized
ordinary tensor comparison. Only its invertibility is part of the existence theorem below.
Source: Stacks, 0FJY and 0D5S (blueprint: lem-trf-two-term-perfect-determinant). -/
noncomputable def twoTermDeterminantDerivedCompositionLift {X Y Z : Scheme.{u}}
    (h : Z ⟶ Y) (g : Y ⟶ X) :
    derivedPullback g ⋙ derivedPullback h ⟶ derivedPullback (h ≫ g) := by
  letI : ∀ {A B : Scheme.{u}} (k : A ⟶ B), (tensorPullback k).Additive :=
    fun k ↦ by
      rw [← recordedPullbackData_E k]
      exact recordedPullbackData_additive k
  let : (derivedPullback (h ≫ g)).IsLeftDerivedFunctor
      (recordedDerivedPullbackCounit (h ≫ g))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) :=
    recordedDerivedPullbackCounit_universal (h ≫ g)
  exact (derivedPullback (h ≫ g)).leftDerivedLift
    (recordedDerivedPullbackCounit (h ≫ g))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
    (derivedPullback g ⋙ derivedPullback h)
    ((Functor.associator DerivedCategory.Qh (derivedPullback g) (derivedPullback h)).inv ≫
      Functor.whiskerRight (recordedDerivedPullbackCounit g) (derivedPullback h) ≫
      (Functor.associator _ DerivedCategory.Qh (derivedPullback h)).hom ≫
      Functor.whiskerLeft _ (recordedDerivedPullbackCounit h) ≫
      (Functor.associator _ _
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace)))).inv ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (tensorPullbackSectionComp h g).symm
          (ComplexShape.up ℤ)).hom
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))))

/-- Full determinant data. The functors encode both composition and identity laws; all
pullback components use the recorded derived pullback. The derived identity is pinned
by the unit law for the composition comparison with its original K-flat counit.
Source: Stacks, 0FJX, 0FJY, 0FJI and 0FJM
(blueprint: lem-trf-two-term-perfect-determinant). -/
structure TwoTermPerfectDeterminantData where
  /-- The determinant functor for each scheme. -/
  functor : ∀ X : Scheme.{u}, TwoTermPerfectCore X ⥤ Core X.Modules
  /-- Each value is invertible, using the recorded scheme notion. -/
  invertible : ∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L), (twoTermDeterminantValue (functor X) L hL).IsInvertible
  /-- Every two-term finite locally free model belongs to the source. -/
  model_mem : ∀ {X : Scheme.{u}} (P : TwoTermDeterminantModel X),
    isTwoTermPerfect X (DerivedCategory.Q.obj P.complex)
  /-- The canonical comparison to the displayed exterior-power formula. -/
  modelIso : ∀ {X : Scheme.{u}} (P : TwoTermDeterminantModel X),
    twoTermDeterminantValue (functor X) (DerivedCategory.Q.obj P.complex) (model_mem P) ≅
      P.line
  /-- The zero complex is included, also on the empty scheme. -/
  zero_mem : ∀ X : Scheme.{u}, isTwoTermPerfect X (twoTermDeterminantZeroObject X)
  /-- The determinant of the zero complex is the structure sheaf. -/
  zeroIso : ∀ X : Scheme.{u},
    twoTermDeterminantValue (functor X) (twoTermDeterminantZeroObject X) (zero_mem X) ≅
      SheafOfModules.unit X.ringCatSheaf
  /-- For the contractible model the comparison to zero is evaluation, in dual-first order. -/
  acyclic : ∀ (X : Scheme.{u}) (E : X.Modules) (n : ℕ)
    (hE : E.IsFiniteLocallyFreeOfRank n),
    ∃ z : DerivedCategory.Q.obj (TwoTermDeterminantModel.identity E n hE).complex ≅
      twoTermDeterminantZeroObject X,
      (modelIso (TwoTermDeterminantModel.identity E n hE)).inv ≫
        (twoTermDeterminantIso (functor X)
          (model_mem (TwoTermDeterminantModel.identity E n hE)) (zero_mem X) z).hom ≫
        (zeroIso X).hom =
      (β_ (dual (exteriorSheaf E n)) (exteriorSheaf E n)).hom ≫
        dualEvaluation (exteriorSheaf E n)
  /-- Arbitrary derived pullback preserves the source condition. -/
  pullback_mem : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (L : schemeDerivedCategory X),
    isTwoTermPerfect X L → isTwoTermPerfect Y ((derivedPullback g).obj L)
  /-- The natural determinant pullback comparison. -/
  pullbackIso : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L),
    (tensorPullback g).obj (twoTermDeterminantValue (functor X) L hL) ≅
      twoTermDeterminantValue (functor Y) ((derivedPullback g).obj L) (pullback_mem g L hL)
  /-- Naturality for every derived isomorphism. -/
  pullback_naturality : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M),
    (tensorPullback g).map (twoTermDeterminantIso (functor X) hL hM e).hom ≫
        (pullbackIso g M hM).hom =
      (pullbackIso g L hL).hom ≫
        (twoTermDeterminantIso (functor Y) (pullback_mem g L hL) (pullback_mem g M hM)
          ((derivedPullback g).mapIso e)).hom
  /-- The derived identity comparison. -/
  derivedId : ∀ X : Scheme.{u}, derivedPullback (𝟙 X) ≅ 𝟭 (schemeDerivedCategory X)
  /-- Derived composition, with its hom fixed by the normalized counit lift. -/
  derivedComp : ∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X),
    derivedPullback g ⋙ derivedPullback h ≅ derivedPullback (h ≫ g)
  /-- Its forward map is the actual universal lift, so no arbitrary isomorphism is used. -/
  derivedComp_normalization : ∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X),
    (derivedComp h g).hom = twoTermDeterminantDerivedCompositionLift h g
  /-- This unit law fixes the derived identity to the recorded composition comparison. -/
  derivedId_normalization : ∀ X : Scheme.{u},
    Functor.isoWhiskerLeft (derivedPullback (𝟙 X)) (derivedId X) ≪≫
        Functor.rightUnitor (derivedPullback (𝟙 X)) =
      derivedComp (𝟙 X) (𝟙 X) ≪≫
        eqToIso (congrArg (fun f : X ⟶ X ↦ derivedPullback f) (Category.id_comp (𝟙 X)))
  /-- Compatibility with identity pullback. -/
  pullback_id : ∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L),
    (pullbackIso (𝟙 X) L hL).hom ≫
        (twoTermDeterminantIso (functor X) (pullback_mem (𝟙 X) L hL) hL
          ((derivedId X).app L)).hom =
      (twoTermDeterminantPullbackId X).hom.app (twoTermDeterminantValue (functor X) L hL)
  /-- Compatibility with composition, including successive restrictions to opens. -/
  pullback_comp : ∀ {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L),
    (tensorPullbackSectionComp h g).hom.app
        (twoTermDeterminantValue (functor X) L hL) ≫
        (tensorPullback h).map (pullbackIso g L hL).hom ≫
        (pullbackIso h ((derivedPullback g).obj L) (pullback_mem g L hL)).hom ≫
        (twoTermDeterminantIso (functor Z)
          (pullback_mem h ((derivedPullback g).obj L) (pullback_mem g L hL))
          (pullback_mem (h ≫ g) L hL)
          ((derivedComp h g).app L)).hom =
      (pullbackIso (h ≫ g) L hL).hom
```

## New

The exact same declaration block above, byte-for-byte, is now in
`Sheaf.TraceFormula.TwoTermPerfectDeterminantData`. The original module publicly reexports
that module. Its retained theorem is assembled from the Tor-window proof, normalized
recorded coherence, the affine construction, and affine descent.

## Users

`tools/downstream.py Sheaf.TraceFormula.TwoTermPerfectDeterminant` reports zero current
Lean importers. Quarantined parents are preserved: the quarantined
FlatLCICanonicalAdjunction imports the old path, whose entire public interface remains
available. No withdrawal is proposed and no archive is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.TraceFormula.TwoTermPerfectDeterminant | G2 | Publicly reexports the definitions and proves the unchanged assembly theorem from strict subresults. |
| Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction | quarantined; unclaimed | Same old import path and public declarations; no adaptation. |
| Sheaf.TraceFormula.TwoTermPerfectDeterminantData | G2, new | Owns the exact unchanged declaration block. |
| Sheaf.TraceFormula.TwoTermPerfectTorWindow | G2, new | Proves the characterization and model, zero and pullback membership. |
| Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence | G2, new | Proves normalization and coherence using original counits. |
| Sheaf.TraceFormula.AffineTwoTermDeterminantData | G2, new | Defines the affine/cartesian interfaces, using proved membership assertions. |
| Sheaf.TraceFormula.AffineTwoTermDeterminant | G2, new | States the genuine affine good-diagram construction (Stacks 0FJM). |
| Sheaf.TraceFormula.TwoTermDeterminantAffineDescent | G2, new | States the conditional gluing result, with compatible affine model/zero/evaluation families. |

## Status

landed 20261020T233143-L-899803 2026-10-20 (merge of deliver/G2/Sheaf.TraceFormula.TwoTermPerfectDeterminant)
