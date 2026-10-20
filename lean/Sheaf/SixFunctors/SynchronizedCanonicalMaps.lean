/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization

/-! # The same canonical map at two input families

Source: blueprint Step 2 and the canonical maps of fix-prop-coherence
(blueprint: def-pur-synchronized-canonical-maps).

These relations retain a single constructor, its geometric data and its finite
outer contexts at two sets of inputs. Each of their four map indices is the
existing recorded map evaluated at that family's objects. There is no constructor
for arbitrary arrows or for independently chosen canonical maps at the two families.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
  (bridge : CanonicalBridge l E o) (h : ProperOpenCoherence l E o c a bridge)
  (d : RingedModels l E) (b : RingedOpenComparisons l E d)
  (q : RingedProperOpen l E d b)
  {B : Scheme.{u}} {I : Type u} {X : I → Over B}
  (M : ∀ i, System l E (X i).left) (K : ∀ i, Integral l E (X i).left)
  (MNew : ∀ i, System l E (X i).left) (KNew : ∀ i, Integral l E (X i).left)

/-- One canonical isomorphism constructor at two families.
Source: blueprint Step 2 (blueprint: def-pur-synchronized-canonical-maps). -/
inductive SynchronizedIso : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ≅ t.systemObj l E o M) →
    (e.ringedObj l E d K ≅ t.ringedObj l E d K) →
    (e.systemObj l E o MNew ≅ t.systemObj l E o MNew) →
    (e.ringedObj l E d KNew ≅ t.ringedObj l E d KNew) → Prop where
  | pullComp {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (e : Expression B I X W) :
    SynchronizedIso (.pull (f ≫ g) e) (.pull f (.pull g e)) ((c.pullComp f.left g.left).app
      (e.systemObj l E o M)) ((ringedPullComp l E f.left g.left).app (e.ringedObj l E d K))
      ((c.pullComp f.left g.left).app (e.systemObj l E o MNew))
      ((ringedPullComp l E f.left g.left).app (e.ringedObj l E d KNew))
  | pushComp {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (hf : IsProper f.left) (hg : IsProper g.left) (hfg : IsProper (f ≫ g).left)
      (e : Expression B I X U) :
    SynchronizedIso (.push g hg (.push f hf e)) (.push (f ≫ g) hfg e) ((c.pushComp l E f.left
      g.left).app (e.systemObj l E o M)) ((ringedPushComp l E f.left g.left).app (e.ringedObj l E d
      K))
      ((c.pushComp l E f.left g.left).app (e.systemObj l E o MNew))
      ((ringedPushComp l E f.left g.left).app (e.ringedObj l E d KNew))
  | openComp {U V W : Over B} (j : U ⟶ V) (k : V ⟶ W)
      [hj : IsOpenImmersion j.left] [hk : IsOpenImmersion k.left]
      (qj : QuasiCompact j.left) (qk : QuasiCompact k.left)
      (qjk : QuasiCompact (j ≫ k).left) (e : Expression B I X U) :
    SynchronizedIso (.shriek k hk qk (.shriek j hj qj e)) (.shriek (j ≫ k) (inferInstance :
      IsOpenImmersion (j.left ≫ k.left)) qjk e) ((c.openComp l E j.left k.left).app (e.systemObj l E
      o M)) ((ringedOpenComp l E j.left k.left).app (e.ringedObj l E d K))
      ((c.openComp l E j.left k.left).app (e.systemObj l E o MNew))
      ((ringedOpenComp l E j.left k.left).app (e.ringedObj l E d KNew))
  | tensorAssoc {W : Over B} (e f g : Expression B I X W) :
    SynchronizedIso (.tensor (.tensor e f) g) (.tensor e (.tensor f g)) ((calculus l E
      W.left).systemClosed.monoidal.associator
        (e.systemObj l E o M) (f.systemObj l E o M) (g.systemObj l E o M)) (ringedAssociator l E d
          W.left
        (e.ringedObj l E d K) (f.ringedObj l E d K) (g.ringedObj l E d K))
      ((calculus l E W.left).systemClosed.monoidal.associator
        (e.systemObj l E o MNew) (f.systemObj l E o MNew) (g.systemObj l E o MNew))
      (ringedAssociator l E d W.left
        (e.ringedObj l E d KNew) (f.ringedObj l E d KNew) (g.ringedObj l E d KNew))
  | tensorPull {U V : Over B} (f : U ⟶ V) (e t : Expression B I X V) :
    SynchronizedIso (.pull f (.tensor e t)) (.tensor (.pull f e) (.pull f t))
      ((pullbackTensorSystemComparison l E f.left).app
        (e.systemObj l E o M, t.systemObj l E o M)) ((ringedTensorPull l E d f.left).app
          (e.ringedObj l E d K, t.ringedObj l E d K))
      ((pullbackTensorSystemComparison l E f.left).app
        (e.systemObj l E o MNew, t.systemObj l E o MNew))
      ((ringedTensorPull l E d f.left).app (e.ringedObj l E d KNew, t.ringedObj l E d KNew))
  | beta {U' U V' V : Over B} (v : U' ⟶ U) (j' : U' ⟶ V')
      (j : U ⟶ V) (g : V' ⟶ V)
      [hj : IsOpenImmersion j.left] [hj' : IsOpenImmersion j'.left]
      (qj : QuasiCompact j.left) (qj' : QuasiCompact j'.left)
      (w : v.left ≫ j.left = j'.left ≫ g.left)
      (sq : IsPullback v.left j'.left j.left g.left) (e : Expression B I X U) :
    SynchronizedIso (.pull g (.shriek j hj qj e)) (.shriek j' hj' qj' (.pull v e)) ((a.beta v.left
      j'.left j.left g.left w sq).app (e.systemObj l E o M)) ((b.beta v.left j'.left j.left g.left w
      sq).app (e.ringedObj l E d K))
      ((a.beta v.left j'.left j.left g.left w sq).app (e.systemObj l E o MNew))
      ((b.beta v.left j'.left j.left g.left w sq).app (e.ringedObj l E d KNew))
  | clopen {U V : Over B} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] [IsClosedImmersion j.left]
      (qj : QuasiCompact j.left) (hp : IsProper j.left) (e : Expression B I X U) :
    SynchronizedIso (.shriek j hj qj e) (.push j hp e) ((a.clopen j.left).app (e.systemObj l E o M))
      ((b.clopen j.left).app (e.ringedObj l E d K))
      ((a.clopen j.left).app (e.systemObj l E o MNew))
      ((b.clopen j.left).app (e.ringedObj l E d KNew))
  | supportExpansion {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (qj : QuasiCompact cf.i) (e : Expression B I X U) :
    SynchronizedIso (.compactSupport f cf e) (.push (compactProper (f := f) cf) (inferInstance :
      IsProper cf.g)
        (.shriek (compactOpen (f := f) cf) (inferInstance : IsOpenImmersion cf.i) qj e)) (Iso.refl
          _) (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
  | openProjection {U V : Over B} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    SynchronizedIso (.tensor (.shriek j hj qj e) t) (.shriek j hj qj (.tensor e (.pull j t)))
      ((a.projection j.left).app (e.systemObj l E o M, t.systemObj l E o M)) ((b.projection
      j.left).app (e.ringedObj l E d K, t.ringedObj l E d K))
      ((a.projection j.left).app (e.systemObj l E o MNew, t.systemObj l E o MNew))
      ((b.projection j.left).app (e.ringedObj l E d KNew, t.ringedObj l E d KNew))

/-- One basic canonical generator at two families.
Source: blueprint Step 2 (blueprint: def-pur-synchronized-canonical-maps). -/
inductive SynchronizedBasic : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ⟶ t.systemObj l E o M) →
    (e.ringedObj l E d K ⟶ t.ringedObj l E d K) →
    (e.systemObj l E o MNew ⟶ t.systemObj l E o MNew) →
    (e.ringedObj l E d KNew ⟶ t.ringedObj l E d KNew) → Prop where
  | isoHom {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ≅ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ≅ t.systemObj l E o MNew}
      {r : e.ringedObj l E d K ≅ t.ringedObj l E d K}
      {rNew : e.ringedObj l E d KNew ≅ t.ringedObj l E d KNew} :
    SynchronizedIso l E o c a d b M K MNew KNew e t s r
      sNew
      rNew → SynchronizedBasic e t s.hom r.hom
      sNew.hom
      rNew.hom
  | isoInv {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ≅ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ≅ t.systemObj l E o MNew}
      {r : e.ringedObj l E d K ≅ t.ringedObj l E d K}
      {rNew : e.ringedObj l E d KNew ≅ t.ringedObj l E d KNew} :
    SynchronizedIso l E o c a d b M K MNew KNew e t s r
      sNew
      rNew → SynchronizedBasic t e s.inv r.inv
      sNew.inv
      rNew.inv
  | pullUnit {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X V) :
    SynchronizedBasic e (.push f hf (.pull f e)) (((o.direct f.left).adj).unit.app (e.systemObj l E
      o M)) ((ringedAdj l E f.left).unit.app (e.ringedObj l E d K))
      (((o.direct f.left).adj).unit.app (e.systemObj l E o MNew))
      ((ringedAdj l E f.left).unit.app (e.ringedObj l E d KNew))
  | pullCounit {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) :
    SynchronizedBasic (.pull f (.push f hf e)) e (((o.direct f.left).adj).counit.app (e.systemObj l
      E o M)) ((ringedAdj l E f.left).counit.app (e.ringedObj l E d K))
      (((o.direct f.left).adj).counit.app (e.systemObj l E o MNew))
      ((ringedAdj l E f.left).counit.app (e.ringedObj l E d KNew))
  | openUnit {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X U) :
    SynchronizedBasic e (.pull j (.shriek j hj qj e)) (((o.extension j.left).adj).unit.app
      (e.systemObj l E o M)) ((ringedOpenAdj l E j.left).unit.app (e.ringedObj l E d K))
      (((o.extension j.left).adj).unit.app (e.systemObj l E o MNew))
      ((ringedOpenAdj l E j.left).unit.app (e.ringedObj l E d KNew))
  | openCounit {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X V) :
    SynchronizedBasic (.shriek j hj qj (.pull j e)) e (((o.extension j.left).adj).counit.app
      (e.systemObj l E o M)) ((ringedOpenAdj l E j.left).counit.app (e.ringedObj l E d K))
      (((o.extension j.left).adj).counit.app (e.systemObj l E o MNew))
      ((ringedOpenAdj l E j.left).counit.app (e.ringedObj l E d KNew))
  | properOpen {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
      [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
      [hr : IsProper r.left] [hp : IsProper p.left]
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X U) :
    SynchronizedBasic (.shriek i hi qi (.push r hr e)) (.push p hp (.shriek k hk qk e)) ((h.gamma
      k.left r.left p.left i.left w).app (e.systemObj l E o M)) ((q.gamma k.left r.left p.left
      i.left w).app (e.ringedObj l E d K))
      ((h.gamma k.left r.left p.left i.left w).app (e.systemObj l E o MNew))
      ((q.gamma k.left r.left p.left i.left w).app (e.ringedObj l E d KNew))
  | exchange {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (hr : IsProper r.left) (hp : IsProper p.left)
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X V) :
    SynchronizedBasic (.pull i (.push p hp e)) (.push r hr (.pull k e)) ((properExchange l E o c
      k.left r.left p.left i.left w).app
        (e.systemObj l E o M)) ((mateEquiv (ringedAdj l E p.left) (ringedAdj l E r.left)
        (TwoSquare.mk _ _ _ _ (ringedSquare l E k.left r.left p.left i.left w).hom)).natTrans.app
          (e.ringedObj l E d K))
      ((properExchange l E o c k.left r.left p.left i.left w).app
        (e.systemObj l E o MNew))
      ((mateEquiv (ringedAdj l E p.left) (ringedAdj l E r.left)
        (TwoSquare.mk _ _ _ _ (ringedSquare l E k.left r.left p.left i.left w).hom)).natTrans.app
          (e.ringedObj l E d KNew))
  | projection {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    SynchronizedBasic (.tensor (.push f hf e) t) (.push f hf (.tensor e (.pull f t)))
      (((properProjection l E o f.left).app (e.systemObj l E o M)).app
        (t.systemObj l E o M)) (((ringedProperProjection l E d f.left).app (e.ringedObj l E d
          K)).app
        (t.ringedObj l E d K))
      (((properProjection l E o f.left).app (e.systemObj l E o MNew)).app
        (t.systemObj l E o MNew))
      (((ringedProperProjection l E d f.left).app (e.ringedObj l E d KNew)).app
        (t.ringedObj l E d KNew))
  | compactExchange {U V U' V' : Over B}
      (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
      (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
      (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
      (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    SynchronizedBasic (.pull y (.compactSupport f cf e)) (.compactSupport f' cf' (.pull x e))
      ((compactificationExchange l E o c a cf cf' x.left y.left z wi wp hi).app
        (e.systemObj l E o M)) ((ringedCompactificationExchange l E d b cf cf' x.left y.left z wi wp
          hi).app
        (e.ringedObj l E d K))
      ((compactificationExchange l E o c a cf cf' x.left y.left z wi wp hi).app
        (e.systemObj l E o MNew))
      ((ringedCompactificationExchange l E d b cf cf' x.left y.left z wi wp hi).app
        (e.ringedObj l E d KNew))
  | compactProjection {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    SynchronizedBasic (.tensor (.compactSupport f cf e) t) (.compactSupport f cf (.tensor e (.pull f
      t))) (compactificationProjection l E o c a cf (e.systemObj l E o M) (t.systemObj l E o M))
      (ringedCompactificationProjection l E d b cf
        (e.ringedObj l E d K) (t.ringedObj l E d K))
      (compactificationProjection l E o c a cf (e.systemObj l E o MNew) (t.systemObj l E o MNew))
      (ringedCompactificationProjection l E d b cf
        (e.ringedObj l E d KNew) (t.ringedObj l E d KNew))

/-- One finite canonical composite and all its outer contexts at two families.
Source: blueprint Step 2 (blueprint: def-pur-synchronized-canonical-maps). -/
inductive SynchronizedPair : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ⟶ t.systemObj l E o M) →
    ((e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K) →
    (e.systemObj l E o MNew ⟶ t.systemObj l E o MNew) →
    ((e.evaluate (integralInterpretation l E)).obj KNew ⟶
      (t.evaluate (integralInterpretation l E)).obj KNew) → Prop where
  | basic {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : e.ringedObj l E d K ⟶ t.ringedObj l E d K}
      {rNew : e.ringedObj l E d KNew ⟶ t.ringedObj l E d KNew}
      (g : SynchronizedBasic l E o c a bridge h d b q M K MNew KNew e t s r sNew rNew)
      (he : IsIso (e.completionMap l E d K))
      (heNew : IsIso (e.completionMap l E d KNew)) :
    SynchronizedPair e t s (@inv _ _ _ _ (e.completionMap l E d K) he ≫ r ≫ t.completionMap l E d K)
      sNew
      (@inv _ _ _ _ (e.completionMap l E d KNew) heNew ≫ rNew ≫ t.completionMap l E d KNew)
  | identity {W : Over B} (e : Expression B I X W) : SynchronizedPair e e (𝟙 _) (𝟙 _)
      (𝟙 _)
      (𝟙 _)
  | comp {W : Over B} {e t v : Expression B I X W}
      {s₁ : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {s₁New : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {s₂ : t.systemObj l E o M ⟶ v.systemObj l E o M}
      {s₂New : t.systemObj l E o MNew ⟶ v.systemObj l E o MNew}
      {r₁ : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {r₁New : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew}
      {r₂ : (t.evaluate (integralInterpretation l E)).obj K ⟶
        (v.evaluate (integralInterpretation l E)).obj K}
      {r₂New : (t.evaluate (integralInterpretation l E)).obj KNew ⟶
        (v.evaluate (integralInterpretation l E)).obj KNew}
      (_gt : t.geometric) (_ht : t.admissible l E o M) (_htNew : t.admissible l E o MNew) :
    SynchronizedPair e t s₁ r₁
      s₁New
      r₁New → SynchronizedPair t v s₂ r₂
      s₂New
      r₂New →
      SynchronizedPair e v (s₁ ≫ s₂) (r₁ ≫ r₂)
      (s₁New ≫ s₂New)
      (r₁New ≫ r₂New)
  | pull {U V : Over B} (f : U ⟶ V)
      {e t : Expression B I X V}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    SynchronizedPair e t s r
      sNew
      rNew → SynchronizedPair (.pull f e) (.pull f t) ((pull l E f.left).map s)
        ((integralDerivedPullback l E f.left).map r)
      ((pull l E f.left).map sNew)
      ((integralDerivedPullback l E f.left).map rNew)
  | push {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    SynchronizedPair e t s r
      sNew
      rNew → SynchronizedPair (.push f hf e) (.push f hf t) ((Operations.push l E o f.left).map s)
        ((ringedPush l E f.left).map r)
      ((Operations.push l E o f.left).map sNew)
      ((ringedPush l E f.left).map rNew)
  | shriek {U V : Over B} (f : U ⟶ V) [hf : IsOpenImmersion f.left] (hq : QuasiCompact f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    SynchronizedPair e t s r
      sNew
      rNew → SynchronizedPair (.shriek f hf hq e) (.shriek f hf hq t) ((Operations.shriek l E o
        f.left).map s) ((ringedOpen l E f.left).map r)
      ((Operations.shriek l E o f.left).map sNew)
      ((ringedOpen l E f.left).map rNew)
  | compactSupport {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    SynchronizedPair e t s r
      sNew
      rNew → SynchronizedPair (.compactSupport f cf e) (.compactSupport f cf t) ((Operations.shriek
        l E o cf.i ⋙ Operations.push l E o cf.g).map s) ((PurCompactSupport.image
        (PurCompactSupport.completed l E) cf).map r)
      ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map sNew)
      ((PurCompactSupport.image (PurCompactSupport.completed l E) cf).map rNew)
  | tensor {W : Over B} {e t v z : Expression B I X W}
      {s₁ : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {s₁New : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {s₂ : v.systemObj l E o M ⟶ z.systemObj l E o M}
      {s₂New : v.systemObj l E o MNew ⟶ z.systemObj l E o MNew}
      {r₁ : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {r₁New : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew}
      {r₂ : (v.evaluate (integralInterpretation l E)).obj K ⟶
        (z.evaluate (integralInterpretation l E)).obj K}
      {r₂New : (v.evaluate (integralInterpretation l E)).obj KNew ⟶
        (z.evaluate (integralInterpretation l E)).obj KNew} :
    SynchronizedPair e t s₁ r₁
      s₁New
      r₁New → SynchronizedPair v z s₂ r₂
      s₂New
      r₂New →
      SynchronizedPair (.tensor e v) (.tensor t z) ((calculus l E W.left).systemClosed.tensor.map
        (Prod.mkHom s₁ s₂)) ((integralCompletedTensor l E W.left).map (Prod.mkHom r₁ r₂))
      ((calculus l E W.left).systemClosed.tensor.map (Prod.mkHom s₁New s₂New))
      ((integralCompletedTensor l E W.left).map (Prod.mkHom r₁New r₂New))

/-- Each synchronized evaluation is one of the existing canonical pairs.
Source: blueprint Step 2 (blueprint: def-pur-synchronized-canonical-maps).

Proof: induct on the synchronized construction, including the isomorphism and
basic-generator relations. Each generator is the identical recorded constructor
at the respective family. The basic integral transport uses its respective
completion-unit inverse. Composition has both admissibility witnesses and all
outer context constructors preserve the projected relation. Thus the two
projections lie in the existing CanonicalPair relation. -/
theorem SynchronizedPair.components {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K}
    {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
    {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
      (t.evaluate (integralInterpretation l E)).obj KNew}
    (g : SynchronizedPair l E o c a bridge h d b q M K MNew KNew e t s r sNew rNew) :
    CanonicalPair l E o c a bridge h d b q M K e t s r ∧
      CanonicalPair l E o c a bridge h d b q MNew KNew e t sNew rNew := by
  sorry

/-- No canonical generator or finite context is lost by synchronization.
Source: blueprint Step 2 (blueprint: def-pur-synchronized-canonical-maps).

Proof: induct on the existing canonical-pair construction, with the same induction
on its isomorphism and basic-generator relations. Repeat every actual component
at the identical family. Duplicate each completion-isomorphism witness and each
intermediate admissibility witness. The synchronized constructor has exactly
these indices, so every step gives the diagonal relation. -/
theorem SynchronizedPair.diagonal {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K}
    (g : CanonicalPair l E o c a bridge h d b q M K e t s r) :
    SynchronizedPair l E o c a bridge h d b q M K M K e t s r s r := by
  sorry

end WeilConjectures.IntegralSystemRealization

