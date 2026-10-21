# AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.Encoding and companion definitions

## Reason

Restore the current quarantined item and separate its coefficient encoding from three
independent comparison results, without an import cycle. The original module publicly
re-exports all moved declarations and all its original public imports. No definition,
statement, visibility, instance or target meaning changes. No source-library file changes.

## Old

The following code belonged to `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`:

```lean
/-- The already defined continuous condensed coefficient ring.
Source: blueprint coefficient identification
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev coefficient := Profinite.continuousCoefficientRingObj A

/-- The pulled-back internal module category, without boundedness or completion.
Source: blueprint coefficient identification
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev Internal (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (coefficient A) T)

/-- Ordinary modules over the constant commutative ring sheaf, in the scalar universe.
Source: blueprint coefficient identification
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev Ordinary (T : Scheme.{u}) :=
  realizationModules (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- The reconstructed commutative section-ring sheaf of the pulled-back coefficients.
Source: Stacks 00YV, section-action equivalence
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
abbrev sectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)

/-- Constant functions, as a map into the actual continuous condensed sheaf.
Source: blueprint proof step 1, constant-section normalization
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def pointConstants :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (coefficient A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The canonical constant-coefficient map: sheafify constant functions on the point,
then apply the monoidal inverse image and its constant-sheaf comparison.
Source: blueprint proof step 1
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def canonicalAbelianMap (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ condensedRingObj (coefficient A) T :=
  (constantSchemeIso T).hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
    (upperStarFromPoint T).map
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (coefficient A)).symm (pointConstants A))

/-- The intrinsic-to-fixed coefficient functor restricts to constant scalar sections.
The commutative-ring/underlying-ring constant-sheaf comparison is canonical.
Source: blueprint proof step 3, Stacks 03CY
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def fixedRestriction (T : Scheme.{u}) :
    Ordinary A T ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (ULift.{u + 1} A))) ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- Restrict the section-action equivalence along the specified coefficient isomorphism.
Source: blueprint proof step 2, Stacks 00YV
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def sectionEncoding (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T) :
    Internal A T ⥤ Ordinary A T :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
    (condensedRingObj (coefficient A) T)).functor ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)

/-- The two coefficient presentations and their actual section-action functors.
The ring isomorphism is normalized by the canonical constant-function map; the
forward intrinsic functor is precisely section-action followed by scalar restriction.
The fixed scalar encoding likewise restricts along the constant-sheaf unit.
Source: blueprint proof steps 1--3, Stacks 00YV and 03CY
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
structure Encoding (T : Scheme.{u}) where
  ringIso : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T
  normalization : ∀ (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A),
    ringIso.hom.hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    (canonicalAbelianMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)
  ordinary : Internal A T ≌ Ordinary A T
  ordinary_functor : ordinary.functor = sectionEncoding A T ringIso
  fixed : Ordinary A T ≌
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))
  fixed_functor : fixed.functor = fixedRestriction A T
  [ordinaryAdditive : ordinary.functor.Additive]
  [ordinaryInverseAdditive : ordinary.inverse.Additive]
  [fixedAdditive : fixed.functor.Additive]
  [fixedInverseAdditive : fixed.inverse.Additive]

attribute [instance] Encoding.ordinaryAdditive Encoding.ordinaryInverseAdditive
  Encoding.fixedAdditive Encoding.fixedInverseAdditive

/-- Termwise extension of the specified intrinsic equivalence to unbounded derived categories.
Source: blueprint proof step 4, Stacks 015F
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def Encoding.ordinaryDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌ Scheme.proEtaleDerivedCategory T A :=
  letI := HasDerivedCategory.standard (Ordinary A T)
  e.ordinary.mapDerivedCategory

/-- Termwise extension to fixed scalar sheaves, using the same intrinsic equivalence.
Source: blueprint proof steps 3--4, Stacks 015F
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def Encoding.fixedDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  (e.ordinary.trans e.fixed).mapDerivedCategory

/-- The canonical shift comparison on the actual termwise derived functor.
Source: blueprint proof step 4 and Stacks 015F
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
instance Encoding.fixedDerivedShift {T : Scheme.{u}} (e : Encoding A T) :
    e.fixedDerived.functor.CommShift ℤ := by
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  change (e.ordinary.trans e.fixed).functor.mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The ordinary finite constant local models: on each member of one pro-etale cover
there is a constant finite module. Over a finite ring, finite modules are precisely
finitely presented modules. This is the ordinary side of the source's local-model clause.
Source: blueprint proof step 9 and sk-def-sfb-constructible, clause 1
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryLocalModel (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : C.I₀,
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C.f i)).obj M ≅
        (constantSheaf (Scheme.ProEt.topology (C.X i))
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)

/-- The ordinary finite stratification condition in the same scalar presentation.
Source: sk-def-sfb-constructible, clause 2, and blueprint proof step 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryStratified (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ S : Scheme.Stratification T, ∀ a : Fin S.n,
    ordinaryLocalModel A (S.domain a)
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion a)).obj M)

open Classical in
/-- Qcqs schemes use finite constructible stratifications; otherwise use every affine open.
Source: sk-def-sfb-constructible, clause 2, and blueprint proof step 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryConstructible (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  if CompactSpace T ∧ QuasiSeparatedSpace T then ordinaryStratified A T M
  else ∀ U : T.Opens, IsAffineOpen U → ordinaryStratified A U.toScheme
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U.ι).obj M)

/-- The ordinary bounded constructible predicate in the fixed scalar presentation.
Source: sk-def-sfb-constructible, final paragraph, and blueprint proof step 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryBoundedConstructible (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    ordinaryConstructible A T ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The ordinary bounded constructible finite-Tor predicate, without a fixed Tor bound.
Source: sk-def-sfb-constructible, final paragraph, and blueprint proof steps 7 and 9
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence). -/
def ordinaryCtf (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  ordinaryBoundedConstructible A T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K
```

## New

The same code belongs to `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`, which the original
module publicly imports. Only the documentation's blueprint attachment IDs change:

```lean
/-- The already defined continuous condensed coefficient ring.
Source: blueprint coefficient identification
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
abbrev coefficient := Profinite.continuousCoefficientRingObj A

/-- The pulled-back internal module category, without boundedness or completion.
Source: blueprint coefficient identification
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
abbrev Internal (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (coefficient A) T)

/-- Ordinary modules over the constant commutative ring sheaf, in the scalar universe.
Source: blueprint coefficient identification
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
abbrev Ordinary (T : Scheme.{u}) :=
  realizationModules (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- The reconstructed commutative section-ring sheaf of the pulled-back coefficients.
Source: Stacks 00YV, section-action equivalence
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
abbrev sectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)

/-- Constant functions, as a map into the actual continuous condensed sheaf.
Source: blueprint proof step 1, constant-section normalization
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def pointConstants :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (coefficient A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The canonical constant-coefficient map: sheafify constant functions on the point,
then apply the monoidal inverse image and its constant-sheaf comparison.
Source: blueprint proof step 1
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def canonicalAbelianMap (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ condensedRingObj (coefficient A) T :=
  (constantSchemeIso T).hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
    (upperStarFromPoint T).map
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (coefficient A)).symm (pointConstants A))

/-- The intrinsic-to-fixed coefficient functor restricts to constant scalar sections.
The commutative-ring/underlying-ring constant-sheaf comparison is canonical.
Source: blueprint proof step 3, Stacks 03CY
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def fixedRestriction (T : Scheme.{u}) :
    Ordinary A T ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (ULift.{u + 1} A))) ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- Restrict the section-action equivalence along the specified coefficient isomorphism.
Source: blueprint proof step 2, Stacks 00YV
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def sectionEncoding (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T) :
    Internal A T ⥤ Ordinary A T :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
    (condensedRingObj (coefficient A) T)).functor ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)

/-- The two coefficient presentations and their actual section-action functors.
The ring isomorphism is normalized by the canonical constant-function map; the
forward intrinsic functor is precisely section-action followed by scalar restriction.
The fixed scalar encoding likewise restricts along the constant-sheaf unit.
Source: blueprint proof steps 1--3, Stacks 00YV and 03CY
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
structure Encoding (T : Scheme.{u}) where
  ringIso : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T
  normalization : ∀ (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A),
    ringIso.hom.hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    (canonicalAbelianMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)
  ordinary : Internal A T ≌ Ordinary A T
  ordinary_functor : ordinary.functor = sectionEncoding A T ringIso
  fixed : Ordinary A T ≌
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))
  fixed_functor : fixed.functor = fixedRestriction A T
  [ordinaryAdditive : ordinary.functor.Additive]
  [ordinaryInverseAdditive : ordinary.inverse.Additive]
  [fixedAdditive : fixed.functor.Additive]
  [fixedInverseAdditive : fixed.inverse.Additive]

attribute [instance] Encoding.ordinaryAdditive Encoding.ordinaryInverseAdditive
  Encoding.fixedAdditive Encoding.fixedInverseAdditive

/-- Termwise extension of the specified intrinsic equivalence to unbounded derived categories.
Source: blueprint proof step 4, Stacks 015F
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def Encoding.ordinaryDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌ Scheme.proEtaleDerivedCategory T A :=
  letI := HasDerivedCategory.standard (Ordinary A T)
  e.ordinary.mapDerivedCategory

/-- Termwise extension to fixed scalar sheaves, using the same intrinsic equivalence.
Source: blueprint proof steps 3--4, Stacks 015F
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def Encoding.fixedDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  (e.ordinary.trans e.fixed).mapDerivedCategory

/-- The canonical shift comparison on the actual termwise derived functor.
Source: blueprint proof step 4 and Stacks 015F
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
instance Encoding.fixedDerivedShift {T : Scheme.{u}} (e : Encoding A T) :
    e.fixedDerived.functor.CommShift ℤ := by
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  change (e.ordinary.trans e.fixed).functor.mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The ordinary finite constant local models: on each member of one pro-etale cover
there is a constant finite module. Over a finite ring, finite modules are precisely
finitely presented modules. This is the ordinary side of the source's local-model clause.
Source: blueprint proof step 9 and sk-def-sfb-constructible, clause 1
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryLocalModel (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : C.I₀,
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C.f i)).obj M ≅
        (constantSheaf (Scheme.ProEt.topology (C.X i))
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)

/-- The ordinary finite stratification condition in the same scalar presentation.
Source: sk-def-sfb-constructible, clause 2, and blueprint proof step 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryStratified (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ S : Scheme.Stratification T, ∀ a : Fin S.n,
    ordinaryLocalModel A (S.domain a)
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion a)).obj M)

open Classical in
/-- Qcqs schemes use finite constructible stratifications; otherwise use every affine open.
Source: sk-def-sfb-constructible, clause 2, and blueprint proof step 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryConstructible (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  if CompactSpace T ∧ QuasiSeparatedSpace T then ordinaryStratified A T M
  else ∀ U : T.Opens, IsAffineOpen U → ordinaryStratified A U.toScheme
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U.ι).obj M)

/-- The ordinary bounded constructible predicate in the fixed scalar presentation.
Source: sk-def-sfb-constructible, final paragraph, and blueprint proof step 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryBoundedConstructible (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    ordinaryConstructible A T ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The ordinary bounded constructible finite-Tor predicate, without a fixed Tor bound.
Source: sk-def-sfb-constructible, final paragraph, and blueprint proof steps 7 and 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryCtf (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  ordinaryBoundedConstructible A T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K
```

The original theorem remains in its original module, with its signature verbatim.
Its proof constructs the normalized encoding and combines three proper source components,
then proves finite-Tor and localizing-closure transport.

## Users

`tools/downstream.py --allow-missing --uses ...Encoding` reports zero live importers or uses.
The item is quarantined. The live/quarantined scan and the preflight name scan give
the following users or lexical candidates. No consumer needs a source adaptation:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | K1 | Restored; same statement and publicly re-exported API. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed; quarantined | Same original import and API; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed; quarantined | Same original import and API; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Lexical `coefficient` hit is the unrelated reduction structure projection; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Lexical `Ordinary` hit is the Kunneth.Ordinary import; no adaptation. |
| WeilConjectures | maintainer root; unclaimed | Lexical `Internal` and `Ordinary` hits are unrelated import suffixes; no adaptation. |

The three lexical candidates contain no `FiniteDiscreteOrdinary` reference; the root
imports `Mathlib.Algebra.DirectSum.Internal` and `Etale.Derived.Kunneth.Ordinary`.
They are included explicitly because the preflight consumer gate requests them.
The quarantined consumers and their nodes remain. No target statement review is reopened:
all public definition bodies and theorem signatures are unchanged.

## Status

landed 20261021T061419-L-1771997 2026-10-21 (merge of deliver/K1/Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence)
