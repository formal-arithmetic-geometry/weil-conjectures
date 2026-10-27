# IntegralPullbackStrictRoos normalization assembly

## Reason

The existing chain-representative, resolving-counit and augmentation-localization
statements publicly import the parent solely for its concrete definitions. Using them
to prove the parent forms an import cycle. Move the definitions into an earlier data
module and publicly reexport them. The three unclaimed statement modules change only
their public import; all names, signatures, proofs and constructions are preserved.
The definition-interface changes reopen the meaning review for targets that reach
them. No target signature or mathematical meaning changes. Two new lemmas isolate finite
augmentation compatibility and scalar localization. The existing derived-unit theorem
and its recently landed proof remain untouched.

Compilation exposed expensive unfolding of roosF into the shifted mapping cone.
Local reducibility controls keep the Roos functor closed while elaborating the
coordinate predicates. These are local to the file, not changes to exported
attributes. Explicit zero-map type annotations in the augmentation
predicate fix the biproduct objects before elaboration; they change no term.
The productMap abbreviation is made an irreducible definition, with the same body
and an explicit morphism type. This prevents the cone predicates from expanding
its composed product construction during type inference. The normalization
predicates and underlying maps retain exactly their meanings.

## Old

The declarations below lived in Sheaf.Paper.IntegralPullbackStrictRoosNormalization.
IntegralRoosChainRepresentatives, IntegralRoosResolvingCounits and
IntegralRoosAugmentationLocalization each had the public import:

```lean
public import Sheaf.Paper.IntegralPullbackStrictRoosNormalization
```

The relocated declarations, verbatim:

```lean
/-- The actual small pro-etale site, retaining its distinct object and morphism universes.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance (priority := 3000) siteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _

/-- The existing uniformizer-adic datum of the finite extension, with its harmless size lift.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev datum : AdicCoefficientDatum (PbcIntegralRing l E) := pbcIntegralDatum l E
/-- Completed coefficients presented by their canonical finite quotient limit. The existing
ImmersionCompletedPullback.completedRingIso identifies this presentation with the pulled
continuous integral coefficients, preserving every finite projection.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev R (T : Scheme.{u}) : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  (datum l E).completedRing T
/-- The existing constant coefficient ring sheaf, in the same size convention as R.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev C (T : Scheme.{u}) : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  exchangeConstantRing T (PbcIntegralRing l E)
/-- The ambient module category over completed coefficients; no completeness is imposed.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev ModR (T : Scheme.{u}) := reductionModules T (R l E T)
/-- The distinct ambient category of modules over constant coefficients.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev ModC (T : Scheme.{u}) := reductionModules T (C l E T)
/-- Restriction along the existing constant-function coefficient map.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev res (T : Scheme.{u}) := PulledReduction.res (datum l E) T
/-- The existing strict completed-coefficient quotient tower, including quotient transitions.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev redR (T : Scheme.{u}) := completedReductionModuleTowerFunctor T (datum l E)
/-- The existing strict constant-coefficient quotient tower, including quotient transitions.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev redC (T : Scheme.{u}) := OrderedExchange.reductionModule (datum l E) T

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
/-- The actual ringed-site module inverse image for completed coefficients.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev pullR := completedModulePullback g (datum l E)
/-- The actual constant-coefficient module inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev pullC := PulledReduction.pull (A := PbcIntegralRing l E) g
/-- Levelwise completed-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerPullR := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pullR l E g)
/-- Levelwise constant-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerPullC := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pullC l E g)
/-- Levelwise restriction of scalars on strict diagrams.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerRes (T : Scheme.{u}) := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (res l E T)
/-- The pulled quotient tower, with index n denoting the positive quotient n+1.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev T := redR l E Y ⋙ towerPullR l E g
/-- The quotient tower of the ordinary pulled complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev U := pullR l E g ⋙ redR l E X
/-- The constant-coefficient inverse image of the restricted quotient tower.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev V := res l E Y ⋙ redC l E Y ⋙ towerPullC l E g
/-- All integer-indexed cochain complexes of completed-coefficient modules.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev complexesR (W : Scheme.{u}) := CochainComplex (ModR l E W) ℤ
/-- All integer-indexed cochain complexes of constant-coefficient modules.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev complexesC (W : Scheme.{u}) := CochainComplex (ModC l E W) ℤ
/-- The existing additivity instance for module inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance pullR_additive : (pullR l E g).Additive :=
  completedModulePullback_additive g (datum l E)
/-- The existing additivity instance for the strict reduction functor.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance redR_additive (W : Scheme.{u}) : (redR l E W).Additive :=
  completedReductionModuleTowerFunctor_additive W (datum l E)
/-- Zero preservation obtained from the existing additive reduction functor.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance redR_zero (W : Scheme.{u}) :
    (completedReductionModuleTowerFunctor W (datum l E)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _
/-- Additivity of the composite giving the tower U.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance U_additive : (U l E g).Additive where
  map_add {_M _N} {a b} := (congrArg (redR l E X).map
    ((pullR l E g).map_add (f := a) (g := b))).trans ((redR l E X).map_add)

/-- Zero preservation of U, without unfolding the chosen derived-category structures.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance U_zero : (U l E g).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- Apply the tower T degree by degree to a cochain complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxT := (T l E g).mapHomologicalComplex (.up ℤ)
/-- Apply the tower U degree by degree to a cochain complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxU := (U l E g).mapHomologicalComplex (.up ℤ)
/-- Apply the tower V degree by degree to a cochain complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxV := (V l E g).mapHomologicalComplex (.up ℤ)
/-- Degreewise completed-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxPullR := (pullR l E g).mapHomologicalComplex (.up ℤ)
/-- Degreewise constant-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxPullC := (pullC l E g).mapHomologicalComplex (.up ℤ)
/-- Degreewise scalar restriction.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxRes (W : Scheme.{u}) := (res l E W).mapHomologicalComplex (.up ℤ)
/-- The conjunction of the recorded K-flat predicate and flatness of every term over R.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev GoodR (W : Scheme.{u}) (P : complexesR l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R l E W) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} 
      (J := ProEt.topology W) (R := R l E W) (P.X i)
/-- The same resolving class over the constant ring C, using the recorded predicates.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev GoodC (W : Scheme.{u}) (P : complexesC l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := C l E W) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} 
      (J := ProEt.topology W) (R := C l E W) (P.X i)

/-- The natural chain isomorphism induced by the normalized coefficient-square map d.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev dComplex
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g) :=
  NatIso.mapHomologicalComplex d (.up ℤ)

/-- The evaluated strict theta comparison on one positive quotient complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev levelMap
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (P : complexesR l E Y) (n : ℕ) :=
  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)).app (op n)

/-- The product of theta level maps after the canonical product comparison for restriction.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev productMap
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (P : complexesR l E Y) :=
  piComparison (cxRes l E X)
      (fun n : ℕ ↦ ((cxT l E g).obj P).asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ levelMap l E g e P n)

/-- The actual quotient augmentation of T: apply inverse image to the existing quotient unit. Its
chain condition is the naturality equation of that unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def bT (P : complexesR l E Y) (n : ℕ) :
    (cxPullR l E g).obj P ⟶ ((cxT l E g).obj P).asFunctor.obj (op n) where
  f i := (pullR l E g).map
    (((completedReductionModuleUnit (datum l E) Y).app (P.X i)).app (op n))
  comm' i j _ := by
    dsimp only [cxT, cxPullR, cxV, cxPullC, cxRes, T, V, towerPullR, towerPullC,
      Functor.mapHomologicalComplex, HomologicalComplex.asFunctor, Functor.comp,
      Functor.whiskeringRight, Functor.whiskerRight_app]
    simpa only [NatTrans.comp_app, Functor.map_comp, Functor.const_map_app,
      Functor.const_obj_obj, completedTowerConstant, Functor.whiskerRight_app,
      cxRes, Functor.mapHomologicalComplex] using congrArg
      (fun a ↦ (pullR l E g).map (a.app (op n)))
      ((completedReductionModuleUnit (datum l E) Y).naturality (P.d i j)).symm


/-- The actual quotient augmentation of U, evaluated on the ordinary pulled complex. Its chain
condition is the naturality equation of the existing quotient unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def bU (P : complexesR l E Y) (n : ℕ) :
    (cxPullR l E g).obj P ⟶ ((cxU l E g).obj P).asFunctor.obj (op n) where
  f i := ((completedReductionModuleUnit (datum l E) X).app
    (((cxPullR l E g).obj P).X i)).app (op n)
  comm' i j _ := congrArg (fun a ↦ a.app (op n))
    ((completedReductionModuleUnit (datum l E) X).naturality
      (((cxPullR l E g).obj P).d i j)).symm


/-- The actual constant-coefficient quotient augmentation of V, followed by inverse image. Its chain
condition is the naturality equation of the existing constant quotient unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def bV (P : complexesR l E Y) (n : ℕ) :
    (cxPullC l E g).obj ((cxRes l E Y).obj P) ⟶
      ((cxV l E g).obj P).asFunctor.obj (op n) where
  f i := (pullC l E g).map
    (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
      (((cxRes l E Y).obj P).X i)).app (op n))
  comm' i j _ := by
    dsimp only [cxT, cxPullR, cxV, cxPullC, cxRes, T, V, towerPullR, towerPullC,
      Functor.mapHomologicalComplex, HomologicalComplex.asFunctor, Functor.comp,
      Functor.whiskeringRight, Functor.whiskerRight_app]
    simpa only [NatTrans.comp_app, Functor.map_comp, Functor.const_map_app,
      Functor.const_obj_obj, completedTowerConstant, Functor.whiskerRight_app,
      cxRes, Functor.mapHomologicalComplex] using congrArg
      (fun a ↦ (pullC l E g).map (a.app (op n)))
      ((OrderedExchange.ordinaryAugmentation (datum l E) Y).naturality
        ((res l E Y).map (P.d i j))).symm


/-- The strict complex comparison induced degreewise by lambda.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev lamComplex (a : T l E g ≅ U l E g) :=
  letI : (U l E g).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  NatIso.mapHomologicalComplex a (.up ℤ)

/-- The actual shifted-cone map of lambda. The existing roosF_map_χ equation gives the product of
the level maps in both cone coordinates.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev Lmap (a : T l E g ≅ U l E g) (P : complexesR l E Y) :=
  roosF.mapIso ((lamComplex l E g a).app P)

/-- Strict tower complexes in the indicated ambient module category.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerComplexes (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  CochainComplex (ℕᵒᵖ ⥤ reductionModules W B) ℤ

/-- The type of comparisons from the existing strict Roos functor to total derived limit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev kappaType (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  (roosF (A := reductionModules W B)) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ completedRlim W B

/-- The type of ordinary-limit inclusions into the actual strict Roos cone.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev inclusionType (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  (completedTowerLimit W B).mapHomologicalComplex (.up ℤ) ⟶
    (roosF (A := reductionModules W B))

/-- The compatible-family map to the degreewise product, with the canonical evaluation-product
comparison inserted explicitly.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def limitProduct (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (I : towerComplexes W B) (q : ℤ) :
    limit (I.X q) ⟶ (roosP I).X q :=
  Limits.Pi.lift (fun n : ℕ ↦ limit.π (I.X q) (op n)) ≫
    inv (piComparison (HomologicalComplex.eval _ _ q)
      (fun n : ℕ ↦ I.asFunctor.obj (op n)))

/-- The ordinary-limit inclusion has coordinates (0,z), and its image followed by kappa is exactly
the existing universal total-right-derived-limit unit. This fixes the K-injective comparison and
its extension to all strict tower complexes.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsUnitNormalized (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (κ : kappaType W B) (j : inclusionType W B) : Prop :=
  (∀ (I : towerComplexes W B) (p : ℤ),
    (j.app I).f (p + 1) ≫ (roosχ I p).hom =
      biprod.lift 0 (limitProduct W B I (p + 1))) ∧
  ∀ I : towerComplexes W B,
    DerivedCategory.Q.map (j.app I) ≫ κ.hom.app I = OrderedExchange.limitComplexUnit W B I

/-- The existing quotient-completion unit over completed coefficients: the
constant-tower/derived-limit unit followed by derived limit of the quotient augmentation.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def unitR (W : Scheme.{u}) (K : reductionDerivedCategory W (R l E W)) :=
  (completedConstantRlimUnit (datum l E) W).app K ≫
    (completedRlim W (R l E W)).map ((completedReductionTowerUnit (datum l E) W).app K)

/-- The specified comparison V to the quotient tower of constant inverse image. It is theta inverse,
then restricted lambda, inverse finite coefficient comparison, and d. Every factor is the
recorded canonical natural isomorphism.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def constantTowerIso
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g) :
    V l E g ≅ (res l E Y ⋙ pullC l E g) ⋙ redC l E X :=
  e.symm ≪≫ Functor.isoWhiskerRight a (towerRes l E X) ≪≫
    Functor.isoWhiskerLeft (pullR l E g) (OrderedExchange.ordinaryRho (datum l E) X).symm ≪≫
    Functor.isoWhiskerRight d (redC l E X)

/-- The canonical comparison from the derived pulled reduction tower to the strict representative T,
using the two existing universal counits.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def towerCounit (P : complexesR l E Y) :=
  (completedTowerPullback g (datum l E)).map
      (completedReductionTowerComplexCounit Y (datum l E) P) ≫
    completedTowerPullbackComplexCounit g (datum l E)
      ((completedReductionComplexTowerFunctor Y (datum l E)).obj P)


/-- The balanced-generator formula for lambda, with the finite scalar transported by its canonical
coefficient identification.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsLambdaNormalized (a : T l E g ≅ U l E g) : Prop :=
  ∀ (M : ModR l E Y) (n : ℕ) (Z : Y.ProEtᵒᵖ)
    (s : ((datum l E).finiteRing Y n).obj.obj Z) (x : M.val.obj Z),
    ((a.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj Z)
      (PulledReduction.insertion (datum l E) g
        ((completedReductionLevel Y (datum l E) n).obj M) Z
        (reductionTensorSection Y ((datum l E).projection Y n) M Z s x)) =
      reductionTensorSection X ((datum l E).projection X n) ((pullR l E g).obj M)
        ((proEtaleBaseChange g).op.obj Z)
        ((proEtaleRingDirectImageMap g ((datum l E).finiteRing Y n)
          ((datum l E).finiteRing X n) ((datum l E).finiteRingIso g n)).hom.app Z s)
        (PulledReduction.insertion (datum l E) g M Z x)

/-- The type of augmented Roos maps for T.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev alphaTType := ∀ P : complexesR l E Y,
  (cxPullR l E g).obj P ⟶ roosF.obj ((cxT l E g).obj P)
/-- The type of augmented Roos maps for U.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev alphaUType := ∀ P : complexesR l E Y,
  (cxPullR l E g).obj P ⟶ roosF.obj ((cxU l E g).obj P)
/-- The type of augmented Roos maps for V, in the constant-coefficient category.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev alphaVType := ∀ P : complexesR l E Y,
  (cxPullC l E g).obj ((cxRes l E Y).obj P) ⟶ roosF.obj ((cxV l E g).obj P)
/-- The type of scalar-restriction Roos comparisons, retaining both ambient categories.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev EType := ∀ P : complexesR l E Y,
  (cxRes l E X).obj (roosF.obj ((cxT l E g).obj P)) ≅ roosF.obj ((cxV l E g).obj P)

/-- Each augmentation is the actual cone lift with coordinates (0,b), where b is its existing strict
quotient augmentation.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsAugmentationNormalized (αT : alphaTType l E g) (αU : alphaUType l E g)
    (αV : alphaVType l E g) : Prop :=
  (∀ (P : complexesR l E Y) (p : ℤ),
    (αT P).f (p + 1) ≫ (roosχ ((cxT l E g).obj P) p).hom =
      biprod.lift 0 ((Limits.Pi.lift (bT l E g P)).f (p + 1))) ∧
  (∀ (P : complexesR l E Y) (p : ℤ),
    (αU P).f (p + 1) ≫ (roosχ ((cxU l E g).obj P) p).hom =
      biprod.lift 0 ((Limits.Pi.lift (bU l E g P)).f (p + 1))) ∧
  ∀ (P : complexesR l E Y) (p : ℤ),
    (αV P).f (p + 1) ≫ (roosχ ((cxV l E g).obj P) p).hom =
      biprod.lift 0 ((Limits.Pi.lift (bV l E g P)).f (p + 1))

/-- The E comparison is the product of the stated theta maps on both cone coordinates, and commutes
with all chain maps in P.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsENormalized (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (ε : EType l E g) : Prop :=
  (∀ (P : complexesR l E Y) (p : ℤ),
    (ε P).hom.f (p + 1) ≫ (roosχ ((cxV l E g).obj P) p).hom =
      (res l E X).map (roosχ ((cxT l E g).obj P) p).hom ≫
        Functor.biprodComparison (res l E X)
          ((roosP ((cxT l E g).obj P)).X p)
          ((roosP ((cxT l E g).obj P)).X (p + 1)) ≫
        biprod.map ((productMap l E g e P).f p)
          ((productMap l E g e P).f (p + 1))) ∧
  ∀ (P P' : complexesR l E Y) (a : P ⟶ P'),
    (cxRes l E X).map (roosF.map ((cxT l E g).map a)) ≫ (ε P').hom =
      (ε P).hom ≫ roosF.map ((cxV l E g).map a)


/-- Localization of L is derived limit of lambda. Localization of E is the canonical
restriction/derived-limit comparison followed by derived limit of theta. The last two equations
identify alphaU with the quotient-completion unit and alphaT with the existing
completed-pullback unit, through the canonical representative counits.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsLocalized (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (ε : EType l E g) (αT : alphaTType l E g) (αU : alphaUType l E g)
    (κR : kappaType X (R l E X)) (κC : kappaType X (C l E X)) : Prop :=
  (∀ P : complexesR l E Y,
    DerivedCategory.Q.map (Lmap l E g a P).hom ≫ κR.hom.app ((cxU l E g).obj P) =
      κR.hom.app ((cxT l E g).obj P) ≫
        (completedRlim X (R l E X)).map
          (DerivedCategory.Q.map ((lamComplex l E g a).hom.app P))) ∧
  (∀ P : complexesR l E Y,
    (res l E X).mapDerivedCategory.map (κR.hom.app ((cxT l E g).obj P)) ≫
        (OrderedExchange.lambda (datum l E) X).hom.app
          (DerivedCategory.Q.obj ((cxT l E g).obj P)) ≫
        (completedRlim X (C l E X)).map
          ((towerRes l E X).mapDerivedCategoryFactors.hom.app ((cxT l E g).obj P)) ≫
        (completedRlim X (C l E X)).map
          (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) =
      (res l E X).mapDerivedCategoryFactors.hom.app
          (roosF.obj ((cxT l E g).obj P)) ≫
        DerivedCategory.Q.map (ε P).hom ≫ κC.hom.app ((cxV l E g).obj P)) ∧
  (∀ (P : complexesR l E Y), GoodR l E Y P →
    DerivedCategory.Q.map (αU P) ≫ κR.hom.app ((cxU l E g).obj P) =
      unitR l E X (DerivedCategory.Q.obj ((cxPullR l E g).obj P)) ≫
        (completedRlim X (R l E X)).map
          (completedReductionTowerComplexCounit X (datum l E)
            ((cxPullR l E g).obj P))) ∧
  ∀ (P : complexesR l E Y), GoodR l E Y P →
    completedOrdinaryPullbackComplexCounit g (datum l E) P ≫
        DerivedCategory.Q.map (αT P) ≫ κR.hom.app ((cxT l E g).obj P) =
      completedPullbackComparison g (datum l E) (DerivedCategory.Q.obj P) ≫
        (completedRlim X (R l E X)).map (towerCounit l E g P)

/-- After the specified strict constant-tower comparison, localized alphaV is the existing constant
quotient-completion unit, followed by the universal reduction counit. This is the
constant-coefficient completed-pullback unit on the given representative.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsConstantUnitNormalized
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (αV : alphaVType l E g) (κC : kappaType X (C l E X)) : Prop :=
  ∀ (P : complexesR l E Y), GoodR l E Y P →
    DerivedCategory.Q.map (αV P) ≫ κC.hom.app ((cxV l E g).obj P) ≫
        (completedRlim X (C l E X)).map
          (DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (constantTowerIso l E g d a e)
              (.up ℤ)).hom.app P)) =
      (OrderedExchange.unit (datum l E) X).app
          (DerivedCategory.Q.obj ((cxPullC l E g).obj ((cxRes l E Y).obj P))) ≫
        (completedRlim X (C l E X)).map
          (OrderedExchange.reductionComplexCounit (datum l E) X
            (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P))


/-- All clauses of the strict Roos normalization, bundled as an explicit proposition:
coefficient-square and balanced-generator normalizations, strict transitions, flat K-flat
preservation, both cone lifts, both chain augmentation identities, universal derived-limit
normalization and the two completion units. The final counit isomorphisms identify the
representatives on the resolving class.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsComparison
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (αT : alphaTType l E g) (αU : alphaUType l E g) (αV : alphaVType l E g)
    (ε : EType l E g) (κR : kappaType X (R l E X))
    (jR : inclusionType X (R l E X)) (κC : kappaType X (C l E X))
    (jC : inclusionType X (C l E X)) : Prop :=
  PulledReduction.IsOrdinaryNormalized (datum l E) g d.inv ∧
  IsLambdaNormalized l E g a ∧
  (∀ (M : ModR l E Y) (n : ℕ),
    (e.hom.app M).app (op n) =
      d.hom.app (((redR l E Y).obj M).obj (op n)) ≫
        (pullC l E g).map
          (((OrderedExchange.ordinaryRho (datum l E) Y).inv.app M).app (op n))) ∧
  (∀ P : complexesR l E Y, GoodR l E Y P →
    GoodR l E X ((cxPullR l E g).obj P) ∧
    GoodC l E Y ((cxRes l E Y).obj P) ∧
    GoodC l E X ((cxPullC l E g).obj ((cxRes l E Y).obj P))) ∧
  IsAugmentationNormalized l E g αT αU αV ∧ IsENormalized l E g e ε ∧
  (∀ P : complexesR l E Y, αT P ≫ (Lmap l E g a P).hom = αU P) ∧
  (∀ P : complexesR l E Y,
    (cxRes l E X).map (αT P) ≫ (ε P).hom =
      (dComplex l E g d).hom.app P ≫ αV P) ∧
  IsUnitNormalized X (R l E X) κR jR ∧ IsUnitNormalized X (C l E X) κC jC ∧
  IsLocalized l E g a e ε αT αU κR κC ∧
  IsConstantUnitNormalized l E g d a e αV κC ∧
  ∀ P : complexesR l E Y, GoodR l E Y P →
    IsIso (towerCounit l E g P) ∧
    IsIso (completedOrdinaryPullbackComplexCounit g (datum l E) P) ∧
    IsIso (completedReductionTowerComplexCounit X (datum l E)
      ((cxPullR l E g).obj P)) ∧
    IsIso (OrderedExchange.reductionComplexCounit (datum l E) X
      (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P))

```

## New

Repair of returned deliveries 3f13967b7eb and 22e7bc4f79e: the parent retains every
original public import verbatim and publicly imports IntegralPullbackStrictRoosData.
Restoring those imports alone did not restore the old proof-import closure. The
second return still identifies WeilConjectures.completedCoefficientMap from
Sheaf.Paper.FiniteFreeCompletedScalarComparison as lost to IntegralRoosDerivedPullbackUnit.
The parent now imports FiniteFreeCompletedScalarComparison with a plain `import`, which
restores it to the import closure that the landing check reads. Reviewer correction
(fcf1350dea4): it must not be a `public import`. The published parent reached that
module only through plain imports, so IntegralRoosDerivedPullbackUnit never saw
WeilConjectures.completedCoefficientMap. Its bare `completedCoefficientMap g` means
AlgebraicGeometry.Scheme.completedCoefficientMap (from CompletedTowerPullback). A public
re-export makes that name resolve to the WeilConjectures declaration, which takes an ℕ
argument, so IntegralRoosDerivedPullbackUnit fails at lines 160, 211 and 215.
No consumer proof or statement changes for this repair.

The declarations above live, with identical names and mathematical types, in
Sheaf.Paper.IntegralPullbackStrictRoosData. The original module publicly imports it.
IsComparison retains its original conjunction definition. The proved accessors
IsAugmentationNormalized.t and IsAugmentationNormalized.u expose its T and U
coordinate equations without unfolding the full augmentation predicate in consumers.

The product comparison has an explicit reducibility boundary:

```lean
@[irreducible]
def productMap
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (P : complexesR l E Y) :
    (cxRes l E X).obj (roosP ((cxT l E g).obj P)) ⟶
      roosP ((cxV l E g).obj P) :=
  piComparison (cxRes l E X)
      (fun n : ℕ ↦ ((cxT l E g).obj P).asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ levelMap l E g e P n)
```

The existing lamComplex and Lmap abbreviations become irreducible definitions with
explicit isomorphism types and unchanged bodies. The concrete bT and bU augmentations
are also irreducible. Proved equations bT_f, bU_f, lamComplex_hom_component and Lmap_hom
expose precisely their degree, level and map components. Consumers use these equations
without unfolding the full chain constructions.
The existing unitR and towerCounit definitions also receive explicit morphism
types and irreducible attributes; their bodies are unchanged:

```lean
@[irreducible]
def unitR (W : Scheme.{u}) (K : reductionDerivedCategory W (R l E W)) :
    K ⟶ (completedRlim W (R l E W)).obj ((completedReductionTower W (datum l E)).obj K) :=
  (completedConstantRlimUnit (datum l E) W).app K ≫
    (completedRlim W (R l E W)).map ((completedReductionTowerUnit (datum l E) W).app K)

@[irreducible]
def towerCounit (P : complexesR l E Y) :
    (completedTowerPullback g (datum l E)).obj
        ((completedReductionTower Y (datum l E)).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((cxT l E g).obj P) :=
  (completedTowerPullback g (datum l E)).map
      (completedReductionTowerComplexCounit Y (datum l E) P) ≫
    completedTowerPullbackComplexCounit g (datum l E)
      ((completedReductionComplexTowerFunctor Y (datum l E)).obj P)
```

Their mathematical types are,
respectively, K to the derived limit of its reduction tower, and the derived
pulled reduction tower to Q(cxT(P)). This bounds elaboration of IsLocalized
without changing either map or any of its normalization equations.

R now abbreviates pbcAdicCompletion T (datum l E), and ModR abbreviates
pbcModules T (R l E T), matching completedModulePullback's type directly.
These are definitionally identical to the former completedRing and reductionModules
aliases; no category or coefficient construction changes.

Three proved generic helpers express product, biproduct and cone-coordinate
extensionality: roosProduct_augmentation, biprod_augmentation and
roosMap_augmentation. They use only the standard product projection, biproduct
projection, and roosF_map_χ equations, with no new assumptions or holes.

Three named zero-preservation instances share the existing composite instance proofs:
T_zero, pullRes_zero and towerRes_zero. They carry no data or new assumptions;
PreservesZeroMorphisms is a proposition. These avoid repeatedly reconstructing
large instance expressions in the complex interfaces.

The three zero maps in IsAugmentationNormalized receive explicit source and target
type annotations. Their terms and all normalization equations are unchanged.
IntegralRoosChainRepresentatives, IntegralRoosResolvingCounits and
IntegralRoosAugmentationLocalization each change exactly their import line to:

```lean
public import Sheaf.Paper.IntegralPullbackStrictRoosData
```

The parent privately imports these three statements and assembles the original
IsComparison proposition. New public theorem signatures are recorded verbatim in
their two DAG nodes. They assert only strictly smaller steps of the argument.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | Q5 | Publicly reexports the same definitions and proves its theorem from the three existing statements and two intermediate equations. |
| Sheaf.Paper.IntegralRoosChainRepresentatives | unclaimed | One-line public-import adaptation; every declaration unchanged. |
| Sheaf.Paper.IntegralRoosResolvingCounits | unclaimed | One-line public-import adaptation; every declaration unchanged. |
| Sheaf.Paper.IntegralRoosAugmentationLocalization | unclaimed | One-line public-import adaptation; every declaration unchanged. |
| Sheaf.Paper.IntegralRoosDerivedPullbackUnit | unclaimed | Public declarations still reexported; no adaptation or proof change. |
| Sheaf.Paper.IntegralRoosCompletionIsomorphisms | unclaimed | Same reexported data; no adaptation. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Same public declarations reexported, no adaptation. |
| Sheaf.Paper.FdPullbackSignedShiftWordTransport | unclaimed | Same public declarations reexported transitively, no adaptation. |

## Status

landed 20261026T070624-L-3631191 2026-10-26 (merge of deliver/Q5/Sheaf.Paper.IntegralPullbackStrictRoosNormalization)
