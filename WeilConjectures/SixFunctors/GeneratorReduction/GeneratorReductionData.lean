/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-! # Canonical coefficient squares for the basic six-functor generators

We define finite operation words built from the basic six-functor generators (tensor, pullback,
proper pushforward, extension by zero along open immersions), their system, ringed-site and
integral interpretations, the structural generator maps between words, the recursive coefficient
comparisons `Word.r`, and the coefficient square `Assertion` for each generator.

## Implementation details

The integral direct-image tower `integralSystemDerivedDirectImage` is defined here, since this
file needs its specialization to the strict quotient system.

## References

* [Stacks, Tags 03DI and 07A7]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures

/-! The integral direct-image tower used by the generator statement. -/

/-- The integral direct image is the total limit of the actual strict quotient
system's total right-derived direct image. -/
def integralSystemDerivedDirectImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : IntegralSystemRealization.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (IntegralSystemRealization.calculus l E X).reduction ⋙
    IntegralSystemRealization.Operations.push l E o f ⋙ coefficientSequenceLimit l E Y

end WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

/-- The system and ordinary ringed-site operations together with their compositors, open
comparisons, realization model and unit normalization. -/
structure Operations where
  system : IntegralSystemRealization.Operations l E
  composition : IntegralSystemRealization.Compositors l E system
  opens : IntegralSystemRealization.OpenComparisons l E system composition
  ringed : IntegralSystemRealization.RingedModels l E
  ringedOpens : IntegralSystemRealization.RingedOpenComparisons l E ringed
  realization : IntegralSystemRealization.RealizationModel l E system
  unitReduction : ∀ X : Scheme.{u},
    (IntegralSystemRealization.calculus l E X).reduction.obj
      (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit ≅
    (IntegralSystemRealization.calculus l E X).systemClosed.monoidal.tensorUnit
  unitNormalization : ∀ (X : Scheme.{u})
      (K : DerivedCategory (scalarReductionSource l E X)),
    (IntegralSystemRealization.calculus l E X).reductionTensor.inv.app
        ((IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit, K) ≫
      (IntegralSystemRealization.calculus l E X).reduction.map
        ((IntegralSystemRealization.calculus l E X).integralClosed.monoidal.leftUnitor K).hom =
    (IntegralSystemRealization.calculus l E X).systemClosed.tensor.map
      (Prod.mkHom (unitReduction X).hom (𝟙 _)) ≫
    ((IntegralSystemRealization.calculus l E X).systemClosed.monoidal.leftUnitor
      ((IntegralSystemRealization.calculus l E X).reduction.obj K)).hom

/-- Finite words in the basic operations: inputs, unit, tensor, pullback, proper pushforward
and extension by zero along open immersions. -/
inductive Word {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S) :
    S → Type (max u s i) where
  | input (k : I) : Word W location (location k)
  | unit (a : S) : Word W location a
  | tensor {a : S} (B C : Word W location a) : Word W location a
  | pull {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (B : Word W location b) : Word W location a
  | push {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
      (B : Word W location a) : Word W location b
  | open {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) : Word W location b

/-- The length (number of operations) of a finite operation word. -/
def Word.length {a : S} : Word W location a → ℕ
  | .input _ | .unit _ => 0
  | .tensor B C => B.length + C.length + 1
  | .pull _ _ _ _ B | .push _ _ _ _ _ B | .open _ _ _ B => B.length + 1

/-- The structural generators between pairs of operation words. -/
inductive GeneratorKind : {a : S} → Word W location a → Word W location a → Type (max u s i) where
  | tensorAssociator {a : S} (B C D : Word W location a) :
      GeneratorKind (Word.tensor (Word.tensor B C) D) (Word.tensor B (Word.tensor C D))
  | tensorLeftUnit {a : S} (B : Word W location a) :
      GeneratorKind (Word.tensor (Word.unit a) B) B
  | tensorRightUnit {a : S} (B : Word W location a) :
      GeneratorKind (Word.tensor B (Word.unit a)) B
  | pullComposition {a b c : S} (f : W a ⟶ W b) (g : W b ⟶ W c)
      (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
      (hsg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
      (hs : IsSeparated (f ≫ g)) (ht : LocallyOfFiniteType (f ≫ g))
      (hq : QuasiCompact (f ≫ g)) (B : Word W location c) :
      GeneratorKind (Word.pull f hsf htf hqf (Word.pull g hsg htg hqg B))
        (Word.pull (f ≫ g) hs ht hq B)
  | pushComposition {a b c : S} (f : W a ⟶ W b) (g : W b ⟶ W c)
      (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
      (hpf : IsProper f) (hsg : IsSeparated g) (htg : LocallyOfFiniteType g)
      (hqg : QuasiCompact g) (hpg : IsProper g) (hs : IsSeparated (f ≫ g))
      (ht : LocallyOfFiniteType (f ≫ g)) (hq : QuasiCompact (f ≫ g))
      (hp : IsProper (f ≫ g)) (B : Word W location a) :
      GeneratorKind (Word.push g hsg htg hqg hpg (Word.push f hsf htf hqf hpf B))
        (Word.push (f ≫ g) hs ht hq hp B)
  | pullPushUnit {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
      (B : Word W location b) :
      GeneratorKind B (Word.push f hs ht hq hp (Word.pull f hs ht hq B))
  | pullPushCounit {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
      (B : Word W location a) :
      GeneratorKind (Word.pull f hs ht hq (Word.push f hs ht hq hp B)) B
  | openUnit {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) :
      GeneratorKind B (Word.pull j (by let := hj; infer_instance)
        (by let := hj; infer_instance) hq (Word.open j hj hq B))
  | openCounit {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location b) :
      GeneratorKind (Word.open j hj hq (Word.pull j
        (by let := hj; infer_instance) (by let := hj; infer_instance) hq B)) B
  | openBaseChange {a b c d : S}
      (gU : W a ⟶ W b) (j' : W a ⟶ W c) (j : W b ⟶ W d) (g : W c ⟶ W d)
      (h : gU ≫ j = j' ≫ g) (sq : IsPullback gU j' j g)
      (hgU : IsSeparated gU) (htgU : LocallyOfFiniteType gU) (hqgU : QuasiCompact gU)
      (hg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
      (hj' : IsOpenImmersion j') (hqj' : QuasiCompact j')
      (hj : IsOpenImmersion j) (hqj : QuasiCompact j) (B : Word W location b) :
      GeneratorKind
        (Word.pull g hg htg hqg (Word.open j hj hqj B))
        (Word.open j' hj' hqj' (Word.pull gU hgU htgU hqgU B))
  | openTensor {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) (C : Word W location b) :
      GeneratorKind (Word.tensor (Word.open j hj hq B) C)
        (Word.open j hj hq (Word.tensor B (Word.pull j (by let := hj; infer_instance)
          (by let := hj; infer_instance) hq C)))
  | properOpenInterchange {a b c d : S}
      (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (i : W c ⟶ W d)
      (h : k ≫ p = r ≫ i) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
      (hi : IsOpenImmersion i) (hii : QuasiCompact i)
      (hr : IsProper r) (hp : IsProper p) (B : Word W location a) :
      GeneratorKind
        (Word.open i hi hii (Word.push r (by let := hr; infer_instance)
          (by let := hr; infer_instance) (by let := hr; infer_instance) hr B))
        (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
          (by let := hp; infer_instance) hp (Word.open k hk hki B))
  | properOpenLambda {a b c d : S}
      (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (i : W c ⟶ W d)
      (h : k ≫ p = r ≫ i) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
      (hi : IsOpenImmersion i) (hii : QuasiCompact i)
      (hr : IsProper r) (hp : IsProper p) (B : Word W location a) :
      GeneratorKind
        (Word.pull i (by let := hi; infer_instance) (by let := hi; infer_instance) hii
          (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
            (by let := hp; infer_instance) hp (Word.open k hk hki B)))
        (Word.push r (by let := hr; infer_instance) (by let := hr; infer_instance)
          (by let := hr; infer_instance) hr B)

/-- The interpretation of a word in coefficient systems, using the derived adjunctions and
tensor product. -/
def Word.systemValue (o : Operations l E)
    (M : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    {a : S} → Word W location a → coefficientSequenceDerived l E (W a)
  | _, .input k => M k
  | a, .unit _ => (IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.tensorUnit
  | a, .tensor B C => (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.obj
      (B.systemValue o M, C.systemValue o M)
  | _, .pull f _ _ _ B => (IntegralSystemRealization.pull l E f).obj (B.systemValue o M)
  | _, .push f _ _ _ _ B =>
      (IntegralSystemRealization.Operations.push l E o.system f).obj (B.systemValue o M)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.Operations.shriek l E o.system j).obj (B.systemValue o M)

/-- The ordinary integral ringed-site interpretation, before quotient completion. -/
def Word.ringedValue (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → Word W location a → DerivedCategory (scalarReductionSource l E (W a))
  | _, .input k => K k
  | a, .unit _ => (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit
  | a, .tensor B C => (o.ringed.tensor (W a)).ordinary.tensor.obj
      (B.ringedValue o K, C.ringedValue o K)
  | _, .pull f _ _ _ B =>
      (IntegralSystemRealization.ringedPull l E f).obj (B.ringedValue o K)
  | _, .push f _ _ _ _ B =>
      (IntegralSystemRealization.ringedPush l E f).obj (B.ringedValue o K)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).obj (B.ringedValue o K)

/-- The system morphism associated to a structural generator, by recursion on the
generator. -/
def GeneratorKind.systemMap (o : Operations l E)
    (M : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    {a : S} → {B C : Word W location a} → GeneratorKind W location B C →
      (B.systemValue l E W location o M ⟶ C.systemValue l E W location o M)
  | a, _, _, .tensorAssociator B C D =>
      ((IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.associator
        (B.systemValue l E W location o M) (C.systemValue l E W location o M)
        (D.systemValue l E W location o M)).hom
  | a, _, _, .tensorLeftUnit B =>
      ((IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.leftUnitor
        (B.systemValue l E W location o M)).hom
  | a, _, _, .tensorRightUnit B =>
      ((IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.rightUnitor
        (B.systemValue l E W location o M)).hom
  | _, _, _, .pullComposition f g _ _ _ _ _ _ _ _ _ B =>
      (o.composition.pullComp f g).inv.app (B.systemValue l E W location o M)
  | _, _, _, .pushComposition f g _ _ _ _ _ _ _ _ _ _ _ _ B =>
      (o.composition.pushComp l E f g).hom.app (B.systemValue l E W location o M)
  | _, _, _, .pullPushUnit f _ _ _ _ B =>
      (o.system.direct f).adj.unit.app (B.systemValue l E W location o M)
  | _, _, _, .pullPushCounit f _ _ _ _ B =>
      (o.system.direct f).adj.counit.app (B.systemValue l E W location o M)
  | _, _, _, .openUnit j hj _ B => letI := hj
      (o.system.extension j).adj.unit.app (B.systemValue l E W location o M)
  | _, _, _, .openCounit j hj _ B => letI := hj
      (o.system.extension j).adj.counit.app (B.systemValue l E W location o M)
  | _, _, _, .openBaseChange v j' j g h sq _ _ _ _ _ _ hj' _ hj _ B =>
      letI := hj'; letI := hj
      (o.opens.beta v j' j g h sq).hom.app (B.systemValue l E W location o M)
  | _, _, _, .openTensor j hj _ B C => letI := hj
      (o.opens.projection j).hom.app
        (B.systemValue l E W location o M, C.systemValue l E W location o M)
  | _, _, _, .properOpenInterchange k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      ((o.system.extension j).adj.homEquiv _ _).symm
        ((IntegralSystemRealization.properOpenLambda l E o.system o.composition o.opens
          k r p j h).inv.app (B.systemValue l E W location o M))
  | _, _, _, .properOpenLambda k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      (IntegralSystemRealization.properOpenLambda l E o.system o.composition o.opens
        k r p j h).hom.app (B.systemValue l E W location o M)

/-- The ordinary ringed-site morphism associated to a structural generator. -/
def GeneratorKind.ringedMap (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → {B C : Word W location a} → GeneratorKind W location B C →
      (B.ringedValue l E W location o K ⟶ C.ringedValue l E W location o K)
  | a, _, _, .tensorAssociator B C D =>
      (IntegralSystemRealization.ringedAssociator l E o.ringed (W a)
        (B.ringedValue l E W location o K) (C.ringedValue l E W location o K)
        (D.ringedValue l E W location o K)).hom
  | a, _, _, .tensorLeftUnit B =>
      (eqToIso (congrArg (fun T : DerivedCategory (scalarReductionSource l E (W a)) ×
        DerivedCategory (scalarReductionSource l E (W a)) ⥤
        DerivedCategory (scalarReductionSource l E (W a)) ↦
          T.obj ((IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit,
            B.ringedValue l E W location o K)) (o.ringed.tensorClosed (W a)))).hom ≫
      ((IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.leftUnitor
        (B.ringedValue l E W location o K)).hom
  | a, _, _, .tensorRightUnit B =>
      (eqToIso (congrArg (fun T : DerivedCategory (scalarReductionSource l E (W a)) ×
        DerivedCategory (scalarReductionSource l E (W a)) ⥤
        DerivedCategory (scalarReductionSource l E (W a)) ↦
          T.obj (B.ringedValue l E W location o K,
            (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit))
          (o.ringed.tensorClosed (W a)))).hom ≫
      ((IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.rightUnitor
        (B.ringedValue l E W location o K)).hom
  | _, _, _, .pullComposition f g _ _ _ _ _ _ _ _ _ B =>
      (IntegralSystemRealization.ringedPullComp l E f g).inv.app
        (B.ringedValue l E W location o K)
  | _, _, _, .pushComposition f g _ _ _ _ _ _ _ _ _ _ _ _ B =>
      (IntegralSystemRealization.ringedPushComp l E f g).hom.app
        (B.ringedValue l E W location o K)
  | _, _, _, .pullPushUnit f _ _ _ _ B =>
      (IntegralSystemRealization.ringedAdj l E f).unit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .pullPushCounit f _ _ _ _ B =>
      (IntegralSystemRealization.ringedAdj l E f).counit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .openUnit j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpenAdj l E j).unit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .openCounit j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpenAdj l E j).counit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .openBaseChange v j' j g h sq _ _ _ _ _ _ hj' _ hj _ B =>
      letI := hj'; letI := hj
      (o.ringedOpens.beta v j' j g h sq).hom.app (B.ringedValue l E W location o K)
  | _, _, _, .openTensor j hj _ B C => letI := hj
      (o.ringedOpens.projection j).hom.app
        (B.ringedValue l E W location o K, C.ringedValue l E W location o K)
  | _, _, _, .properOpenInterchange k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      ((IntegralSystemRealization.ringedOpenAdj l E j).homEquiv _ _).symm
        ((IntegralSystemRealization.ringedProperOpenLambda l E o.ringed o.ringedOpens
          k r p j h).inv.app (B.ringedValue l E W location o K))
  | _, _, _, .properOpenLambda k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      (IntegralSystemRealization.ringedProperOpenLambda l E o.ringed o.ringedOpens
        k r p j h).hom.app (B.ringedValue l E W location o K)

/-- The inverse of `f` if `f` is an isomorphism, and `0` otherwise. -/
def inverseOrZero {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) : Y ⟶ X := by
  classical
  exact if h : IsIso f then @inv C _ X Y f h else 0

/-- The integral proper direct image: the strict system direct image followed by the total
limit. -/
def integralPush (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  integralSystemDerivedDirectImage l E o.system f

/-- The canonical map from the ordinary tensor product to the completed tensor product. -/
def tensorCompletion (o : Operations l E) (X : Scheme.{u}) :=
  (o.ringed.tensor X).chi l E

/-- The coefficient comparison for the completed tensor product. -/
def tensorR (o : Operations l E) (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource l E X)) :=
  inverseOrZero ((IntegralSystemRealization.calculus l E X).reduction.map
    ((tensorCompletion l E o X).app (K, L))) ≫
  (IntegralSystemRealization.calculus l E X).reduction.map
    ((eqToIso (congrArg (fun T : DerivedCategory (scalarReductionSource l E X) ×
      DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E X) ↦ T.obj (K, L))
      (o.ringed.tensorClosed X))).hom) ≫
  (IntegralSystemRealization.calculus l E X).reductionTensor.hom.app (K, L)

/-- The coefficient comparison for the completed pullback. -/
def pullR (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y)) :=
  inverseOrZero ((IntegralSystemRealization.calculus l E X).reduction.map
    (((o.ringed.pull f).unit l E).app K)) ≫
  (o.realization.reductionPull f).hom.app K

/-- The coefficient comparison for the proper direct image, given by the counit of the
reconstruction adjunction. -/
def pushR (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :=
  (IntegralSystemRealization.calculus l E Y).adjunction.counit.app
    ((IntegralSystemRealization.Operations.push l E o.system f).obj
      ((IntegralSystemRealization.calculus l E X).reduction.obj K))

/-- The coefficient comparison for extension by zero along an open immersion. -/
def openR (o : Operations l E) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X)) :=
  inverseOrZero ((o.realization.openReduction l E j).app K)

/-- The open realization map, built from the open reduction comparison and the inverse of the
reconstruction unit. -/
def openD (o : Operations l E) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X)) :=
  (coefficientSequenceLimit l E Y).map ((o.realization.openReduction l E j).app K) ≫
    inverseOrZero ((IntegralSystemRealization.calculus l E Y).adjunction.unit.app
      ((IntegralSystemRealization.ringedOpen l E j).obj K))

/-- The integral interpretation of a word, using completed tensor and pullback, the integral
proper direct image and the ringed open extension. -/
def Word.integralValue (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → Word W location a → DerivedCategory (scalarReductionSource l E (W a))
  | _, .input k => K k
  | a, .unit _ => (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit
  | a, .tensor B C => (integralCompletedTensor l E (W a)).obj
      (B.integralValue o K, C.integralValue o K)
  | _, .pull f _ _ _ B => (integralDerivedPullback l E f).obj (B.integralValue o K)
  | _, .push f _ _ _ _ B => (integralPush l E o f).obj (B.integralValue o K)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).obj (B.integralValue o K)

/-- The completion map from the ringed-site value of a word to its integral value, defined
recursively. -/
def Word.completionMap (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      B.ringedValue l E W location o K ⟶ B.integralValue l E W location o K
  | _, .input _ | _, .unit _ => 𝟙 _
  | a, .tensor B C => (o.ringed.tensor (W a)).ordinary.tensor.map
      (Prod.mkHom (B.completionMap o K) (C.completionMap o K)) ≫
      (tensorCompletion l E o (W a)).app
        (B.integralValue l E W location o K, C.integralValue l E W location o K)
  | _, .pull f _ _ _ B =>
      (IntegralSystemRealization.ringedPull l E f).map (B.completionMap o K) ≫
      ((o.ringed.pull f).unit l E).app (B.integralValue l E W location o K)
  | _, .push f _ _ _ _ B =>
      (IntegralSystemRealization.ringedPush l E f).map (B.completionMap o K) ≫
      (IntegralSystemRealization.ringedPush l E f).map
        ((IntegralSystemRealization.calculus l E _).adjunction.unit.app
          (B.integralValue l E W location o K)) ≫
      (o.realization.push l E f).inv.app
        ((IntegralSystemRealization.calculus l E _).reduction.obj
          (B.integralValue l E W location o K))
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).map (B.completionMap o K)

/-- The integral morphism of a generator: the ringed-site generator transported along the
completion maps. -/
def GeneratorKind.integralMap (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) :=
  inverseOrZero (B.completionMap l E W location o K) ≫
    g.ringedMap l E W location o K ≫ C.completionMap l E W location o K

/-- The reduction of the input family to coefficient systems. -/
def inputReduction
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (k : I) := (IntegralSystemRealization.calculus l E (W (location k))).reduction.obj (K k)

/-- The coefficient comparison of a word, composed recursively from the primitive coefficient
comparisons. -/
def Word.r (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      (IntegralSystemRealization.calculus l E (W a)).reduction.obj
        (B.integralValue l E W location o K) ⟶
      B.systemValue l E W location o (inputReduction l E W location K)
  | _, .input _ => 𝟙 _
  | a, .unit _ => (o.unitReduction (W a)).hom
  | a, .tensor B C => tensorR l E o (W a)
      (B.integralValue l E W location o K) (C.integralValue l E W location o K) ≫
      (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
        (Prod.mkHom (B.r o K) (C.r o K))
  | _, .pull f _ _ _ B => pullR l E o f (B.integralValue l E W location o K) ≫
      (IntegralSystemRealization.pull l E f).map (B.r o K)
  | _, .push f _ _ _ _ B => pushR l E o f (B.integralValue l E W location o K) ≫
      (IntegralSystemRealization.Operations.push l E o.system f).map (B.r o K)
  | _, .open j hj _ B => letI := hj
      openR l E o j (B.integralValue l E W location o K) ≫
      (IntegralSystemRealization.Operations.shriek l E o.system j).map (B.r o K)

/-- A normalized coefficient system with origins whose levels are constructible, supported in
`[lo, hi]` and of Tor amplitude in `[torLo, torHi]`. -/
def SystemAdmissible (X : Scheme.{u}) (M : coefficientSequenceDerived l E X)
    (lo hi torLo torHi : ℤ) : Prop :=
  IsNormalizedCoefficientSequence l E X M ∧
  Nonempty (IntegralSystemRealization.Origins l E X M) ∧
  lo ≤ hi ∧ torLo ≤ torHi ∧ ∀ n : ℕ,
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) ∧
    proEtaleCohomologicalSupport
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) ⊆ Set.Icc lo hi ∧
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) torLo torHi

/-- A constructible integral complex of finite Tor dimension whose reduction system is
admissible. -/
def Admissible {X : Scheme.{u}} (Syst : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) (lo hi torLo torHi : ℤ) : Prop :=
  finiteTorConstructibleIntegral l E X K ∧
  SystemAdmissible l E X (Syst.reduction.obj K) lo hi torLo torHi

/-- Admissibility of the systems at every vertex of a word, recursively. -/
def Word.admissible {a : S} (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ) (B : Word W location a) : Prop :=
  SystemAdmissible l E (W a)
    (Word.systemValue l E W location o (inputReduction l E W location K) B) lo hi torLo torHi ∧
    match B with
    | .input _ | .unit _ => True
    | .tensor C D => C.admissible o K lo hi torLo torHi ∧
        D.admissible o K lo hi torLo torHi
    | .pull _ _ _ _ C | .push _ _ _ _ _ C | .open _ _ _ C =>
        C.admissible o K lo hi torLo torHi

/-- Admissibility of every intermediate system in the cartesian/clopen factorization of the
proper/open comparison lambda. -/
def lambdaAdmissible (o : Operations l E) {U V T Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ T) (p : V ⟶ Z) (j : T ⟶ Z)
    [IsOpenImmersion k] [QuasiCompact k] [IsOpenImmersion j] [QuasiCompact j]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ j)
    (M : coefficientSequenceDerived l E U) (lo hi torLo torHi : ℤ) : Prop :=
  SystemAdmissible l E (pullback p j)
    ((IntegralSystemRealization.pull l E (pullback.fst p j)).obj
      ((IntegralSystemRealization.Operations.shriek l E o.system k).obj M))
    lo hi torLo torHi ∧
  SystemAdmissible l E (pullback p j)
    ((IntegralSystemRealization.Operations.shriek l E o.system
      (ProEtale.StrictTower.squareLift k r p j h)).obj M) lo hi torLo torHi ∧
  SystemAdmissible l E (pullback p j)
    ((IntegralSystemRealization.Operations.push l E o.system
      (ProEtale.StrictTower.squareLift k r p j h)).obj M) lo hi torLo torHi ∧
  SystemAdmissible l E T
    ((IntegralSystemRealization.Operations.push l E o.system (pullback.snd p j)).obj
      ((IntegralSystemRealization.pull l E (pullback.fst p j)).obj
        ((IntegralSystemRealization.Operations.shriek l E o.system k).obj M)))
    lo hi torLo torHi ∧
  SystemAdmissible l E T
    ((IntegralSystemRealization.Operations.push l E o.system (pullback.snd p j)).obj
      ((IntegralSystemRealization.Operations.shriek l E o.system
        (ProEtale.StrictTower.squareLift k r p j h)).obj M)) lo hi torLo torHi ∧
  SystemAdmissible l E T
    ((IntegralSystemRealization.Operations.push l E o.system (pullback.snd p j)).obj
      ((IntegralSystemRealization.Operations.push l E o.system
        (ProEtale.StrictTower.squareLift k r p j h)).obj M)) lo hi torLo torHi

/-- Admissibility of the additional systems used by a generator. -/
def GeneratorKind.admissible (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ) :
    {a : S} → {B C : Word W location a} → GeneratorKind W location B C → Prop
  | _, _, _, .properOpenInterchange k r p j h hk qk hj qj hr hp B
  | _, _, _, .properOpenLambda k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      lambdaAdmissible l E o k r p j h
        (B.systemValue l E W location o (inputReduction l E W location K)) lo hi torLo torHi
  | _, _, _, _ => True

/-- The coefficient square of a generator commutes. -/
def Assertion (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  B.r l E W location o K ≫
    g.systemMap l E W location o (inputReduction l E W location K) =
  (IntegralSystemRealization.calculus l E (W a)).reduction.map
    (g.integralMap l E W location o K) ≫ C.r l E W location o K

/-- A family of finite-type structures over `Spec k`. -/
structure FiniteTypeFamily (k : Type u) [CommRing k] where
  structureMap : ∀ a : S, W a ⟶ Spec (CommRingCat.of k)
  locallyFiniteType : ∀ a : S, LocallyOfFiniteType (structureMap a)
  quasiCompact : ∀ a : S, QuasiCompact (structureMap a)

end WeilConjectures.GeneratorReduction
