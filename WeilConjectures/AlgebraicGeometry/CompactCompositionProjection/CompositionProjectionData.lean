/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Compact-support composition and projection notation

The existing operations and component formulas, shared by the assembly theorem and
its contraction lemma. Source: Stacks 0F7B--0F7K
(blueprint: def-sf-composition-projection-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace AlgebraicGeometry.ProEtale.CompactCompositionProjection

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

/-- Finite-type spaces in the statement are Noetherian. This is the existing finite-type
Noetherian instance, with the two subtype properties supplied explicitly; it adds no hypothesis.
Source: Stacks 01T6 (blueprint: lem-sf-composition-projection-mate). -/
instance spaceNoetherian (F : WeilConjectures.FiniteFieldDatum.{u}) (X : Spaces F) :
    IsNoetherian X.obj.left := by
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  exact isNoetherian_of_locallyOfFiniteType X.obj.hom

/-- Component notation for the existing tensor and projection maps, not new operations.
The realizations below insert the published counit-defined projections and open tensor maps.
Source: def-exchange-projection (blueprint: lem-sf-composition-projection-mate). -/
structure TensorData (c : Calculus.{u, g, h, v, w} G geo) where
  tensor : ∀ X, c.D X × c.D X ⥤ c.D X
  pi : ∀ {X Y} (f : X ⟶ Y) (M : c.D X) (N : c.D Y),
    (tensor Y).obj ((c.S f).obj M, N) ⟶
      (c.S f).obj ((tensor X).obj (M, (c.P f).obj N))
  delta : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)]
    (M : c.D X) (N : c.D Y),
    (tensor Y).obj ((c.J j).obj M, N) ⟶
      (c.J j).obj ((tensor X).obj (M, (c.P j).obj N))

variable (c : Calculus.{u, g, h, v, w} G geo) (t : TensorData c)

/-- Compact support for the indicated compactification, with no choice of compactification.
Source: Stacks 0F7J (blueprint: lem-sf-composition-projection-mate). -/
def compact {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion (geo.map j)] : c.D X ⥤ c.D Y := c.J j ⋙ c.S q

/-- The specified compactification projection: proper counit projection, open tensor map,
then the inverse pullback compositor. This is def-exchange-projection's component formula.
Source: Stacks 0E48 (blueprint: lem-sf-composition-projection-mate). -/
def projection {X V Y : G} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion (geo.map j)] (K : c.D X) (L : c.D Y) :
    (t.tensor Y).obj ((compact c j q).obj K, L) ⟶
      (compact c j q).obj ((t.tensor X).obj (K, (c.P (j ≫ q)).obj L)) :=
  t.pi q ((c.J j).obj K) L ≫
    (c.S q).map (t.delta j K ((c.P q).obj L) ≫
      (c.J j).map ((t.tensor X).map
        (Prod.mkHom (𝟙 K) ((c.pComp j q).inv.app L))))

/-- The normalized composition map: the proper/open mate, then the canonical direct-image
and open-extension compositors. No arbitrary comparison map is supplied.
Source: Stacks 0F7J (blueprint: lem-sf-composition-projection-mate). -/
def alpha {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) :
    compact c j q ⋙ compact c i s ⟶ compact c (j ≫ b) (p ≫ s) :=
  (Functor.associator (c.J j) (c.S q) (c.J i ⋙ c.S s)).hom ≫
    Functor.whiskerLeft (c.J j) (Functor.associator (c.S q) (c.J i) (c.S s)).inv ≫
    Functor.whiskerLeft (c.J j) (Functor.whiskerRight (c.gamma b q p i hb) (c.S s)) ≫
    Functor.whiskerLeft (c.J j) (Functor.associator (c.J b) (c.S p) (c.S s)).hom ≫
    Functor.whiskerLeft (c.J j) (Functor.whiskerLeft (c.J b) (c.sComp p s).hom) ≫
    (Functor.associator (c.J j) (c.J b) (c.S (p ≫ s))).inv ≫
    Functor.whiskerRight (c.jComp j b).hom (c.S (p ≫ s))

/-- The final canonical pullback transport, retaining P_f P_g on its source.
Source: Stacks 03CB, 0F7J (blueprint: lem-sf-composition-projection-mate). -/
def trianglePull {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z) (hb : b ≫ p = q ≫ i) :
    c.P (i ≫ s) ⋙ c.P (j ≫ q) ≅ c.P ((j ≫ b) ≫ (p ≫ s)) :=
  (c.pComp (j ≫ q) (i ≫ s)).symm ≪≫
    c.pCongr (by
      calc
        (j ≫ q) ≫ (i ≫ s) = j ≫ ((q ≫ i) ≫ s) := by simp only [Category.assoc]
        _ = j ≫ ((b ≫ p) ≫ s) := congrArg (fun a ↦ j ≫ (a ≫ s)) hb.symm
        _ = (j ≫ b) ≫ (p ≫ s) := by simp only [Category.assoc])

/-- The left side of the displayed projection identity, including its last pullback cast.
Source: blueprint composition calculation (blueprint: lem-sf-composition-projection-mate). -/
def leftMap {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :
    (t.tensor Z).obj (((compact c j q ⋙ compact c i s).obj K), L) ⟶
      (compact c (j ≫ b) (p ≫ s)).obj
        ((t.tensor X).obj (K, (c.P ((j ≫ b) ≫ (p ≫ s))).obj L)) :=
  projection c t i s ((compact c j q).obj K) L ≫
    (compact c i s).map (projection c t j q K ((c.P (i ≫ s)).obj L)) ≫
    (alpha c j b q p i s hb).app
      ((t.tensor X).obj (K, (c.P (j ≫ q)).obj ((c.P (i ≫ s)).obj L))) ≫
    (compact c (j ≫ b) (p ≫ s)).map
      ((t.tensor X).map (Prod.mkHom (𝟙 K) ((trianglePull c j b q p i s hb).hom.app L)))

/-- The right side, alpha tensor identity followed by the composite projection.
Source: blueprint composition calculation (blueprint: lem-sf-composition-projection-mate). -/
def rightMap {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z) :=
  (t.tensor Z).map (Prod.mkHom ((alpha c j b q p i s hb).app K) (𝟙 L)) ≫
    projection c t (j ≫ b) (p ≫ s) K L

/-- Equations for every supplied compatible triangle. The naturality clause is for the
common composite, not merely for objectwise equality. Properness of s says (i,s)
compactifies g; no separated structure map or Cartesian condition is imposed.
Source: Stacks 0F7J and blueprint (blueprint: lem-sf-composition-projection-mate). -/
def TriangleLaws : Prop :=
  ∀ {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    [IsProper (geo.map s)] (hb : b ≫ p = q ≫ i),
    IsIso (alpha c j b q p i s hb) ∧
    (∀ (K : c.D X) (L : c.D Z),
      leftMap c t j b q p i s hb K L = rightMap c t j b q p i s hb K L) ∧
    (∀ {K K' : c.D X} {L L' : c.D Z} (a : K ⟶ K') (d : L ⟶ L'),
      (t.tensor Z).map (Prod.mkHom ((compact c j q ⋙ compact c i s).map a) d) ≫
          leftMap c t j b q p i s hb K' L' =
        leftMap c t j b q p i s hb K L ≫
          (compact c (j ≫ b) (p ≫ s)).map
            ((t.tensor X).map
              (Prod.mkHom a ((c.P ((j ≫ b) ≫ (p ≫ s))).map d))))

/-- Associativity on the actual three-cell compactification grid of Stacks 0F7K.
The two rectangle equations are included as explicit proofs of consequences of the three
cell equations, not as additional geometric restrictions. Equality transports at the end
identify the two parenthesizations of the open and proper composites.
Source: Stacks 0F7K (blueprint: lem-sf-composition-projection-mate). -/
def Associativity : Prop :=
  ∀ {X U V W Y A B Z C T : G}
    (j : X ⟶ U) (b : U ⟶ V) (d : V ⟶ W)
    (q : U ⟶ Y) (r : V ⟶ A) (p : W ⟶ B)
    (i : Y ⟶ A) (e : A ⟶ B) (s : A ⟶ Z) (t₀ : B ⟶ C)
    (k : Z ⟶ C) (v₀ : C ⟶ T)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map d)] [IsOpenImmersion (geo.map i)]
    [IsOpenImmersion (geo.map e)] [IsOpenImmersion (geo.map k)]
    [QuasiCompact (geo.map b)] [QuasiCompact (geo.map d)]
    [QuasiCompact (geo.map i)] [QuasiCompact (geo.map e)] [QuasiCompact (geo.map k)]
    [IsProper (geo.map q)] [IsProper (geo.map r)] [IsProper (geo.map p)]
    [IsProper (geo.map s)] [IsProper (geo.map t₀)] [IsProper (geo.map v₀)]
    (hA : b ≫ r = q ≫ i) (_hB : d ≫ p = r ≫ e) (hC : e ≫ t₀ = s ≫ k)
    (hAB : (b ≫ d) ≫ p = q ≫ (i ≫ e))
    (hBC : d ≫ (p ≫ t₀) = (r ≫ s) ≫ k) (K : c.D X),
    (compact c k v₀).map ((alpha c j b q r i s hA).app K) ≫
        (alpha c (j ≫ b) d (r ≫ s) (p ≫ t₀) k v₀ hBC).app K ≫
        (c.S ((p ≫ t₀) ≫ v₀)).map
          ((c.jCongr (Category.assoc j b d)).hom.app K) ≫
        (c.sCongr (Category.assoc p t₀ v₀)).hom.app ((c.J (j ≫ (b ≫ d))).obj K) =
      (alpha c i e s t₀ k v₀ hC).app ((compact c j q).obj K) ≫
        (alpha c j (b ≫ d) q p (i ≫ e) (t₀ ≫ v₀) hAB).app K

/-- Insert the actual finite-coefficient tensor, counit projection and unit-normalized
open tensor map into the component notation above.
Source: def-exchange-projection (blueprint: lem-sf-composition-projection-mate). -/
def ordinaryTensor (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : TensorData (ordinary F Λ) where
  tensor X := Functor.uncurry.obj (ProperOpenTensor Λ X.obj.left)
  pi f M N := properOpenProjection Λ f.hom.left M N
  delta j hj M N := by
    letI : IsOpenImmersion j.hom.left := hj
    exact (properOpenTensorIso Λ j.hom.left M N).hom

open WeilConjectures.IntegralSystemRealization in
/-- The supplied simultaneous system calculus. Its alpha is the inverse mate of the
intrinsically normalized Gamma; taking its proper mate recovers that very Gamma.
The adjunction bijection determines this map uniquely, before evaluation.
Source: integral system realization (blueprint: lem-sf-composition-projection-mate). -/
def realizedSystems (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : Operations l E) (z : Realizations l E F o) :
    Calculus (Spaces F) (geometry F) where
  D X := System l E X.obj.left
  P f := pull l E f.hom.left
  S f := Operations.push l E o f.hom.left
  J j hj := by
    letI : IsOpenImmersion j.hom.left := hj
    exact Operations.shriek l E o j.hom.left
  adj f := (o.direct f.hom.left).adj
  openAdj j hj := by
    letI : IsOpenImmersion j.hom.left := hj
    exact (o.extension j.hom.left).adj
  pComp f g := z.compositors.pullComp f.hom.left g.hom.left
  pId X := z.canonicalBridge.pull l E (𝟙 X.obj.left) ≪≫
    SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X.obj.left
  alpha b q p i hb hi hqb hqi hq hp h := by
    letI : IsOpenImmersion b.hom.left := hb
    letI : IsOpenImmersion i.hom.left := hi
    letI : QuasiCompact b.hom.left := hqb
    letI : QuasiCompact i.hom.left := hqi
    letI : IsProper q.hom.left := hq
    letI : IsProper p.hom.left := hp
    exact (mateEquiv (o.direct q.hom.left).adj (o.direct p.hom.left).adj).symm
      (TwoSquare.mk _ _ _ _ (z.properOpen.gamma b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h)))

open WeilConjectures.IntegralSystemRealization in
/-- Insert the published system tensor and its actual proper and open projections.
All quotient transitions remain part of these ringed-diagram morphisms.
Source: def-exchange-projection (blueprint: lem-sf-composition-projection-mate). -/
def realizedTensor (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : Operations l E) (z : Realizations l E F o) :
    TensorData (realizedSystems F l E o z) where
  tensor X := (calculus l E X.obj.left).systemClosed.tensor
  pi f M N := ((properProjection l E o f.hom.left).app M).app N
  delta j hj M N := by
    letI : IsOpenImmersion j.hom.left := hj
    exact (z.openComparisons.projection j.hom.left).hom.app (M, N)

/-- The component equation for each supplied triangle, without invertibility,
naturality or associativity assertions.
Source: the composition calculation of Stacks 0F7J
(blueprint: lem-sf-triangle-projection-compositor-contraction). -/
def TriangleEquations : Prop :=
  ∀ {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    [IsProper (geo.map s)] (hb : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z),
    leftMap c t j b q p i s hb K L = rightMap c t j b q p i s hb K L

end AlgebraicGeometry.ProEtale.CompactCompositionProjection
