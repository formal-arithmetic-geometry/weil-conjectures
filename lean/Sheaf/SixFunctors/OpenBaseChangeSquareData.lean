/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.SixFunctors.OpenFactorCoherence

/-! # Open projection/base-change square

Source: current blueprint, sec-six-functors/sk-prop-sf-pf-coherence,
base-change paragraph (blueprint: lem-sf-pf-open-base-change-square).
The maps below use the intrinsic finite module categories and the completed integral
categories. Positive coefficient level `n` means exponent `n+1`. The auxiliary predicates
spell out the displayed equations; they do not introduce replacement operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures.OpenProjectionBaseChange

/-- The tensor monoidality equation of the source, in left-to-right Lean composition.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def Monoidality {D₁ : Type u₁} {D₂ : Type u₂} {D₃ : Type u₃} {D₄ : Type u₄}
    [Category.{v₁} D₁] [Category.{v₂} D₂] [Category.{v₃} D₃] [Category.{v₄} D₄]
    (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
    (T₃ : D₃ × D₃ ⥤ D₃) (T₄ : D₄ × D₄ ⥤ D₄)
    (F : D₁ ⥤ D₂) (F' : D₃ ⥤ D₄) (G : D₁ ⥤ D₃) (H : D₂ ⥤ D₄)
    (theta : G ⋙ F' ≅ F ⋙ H)
    (muF : ∀ B C, F.obj (T₁.obj (B, C)) ≅ T₂.obj (F.obj B, F.obj C))
    (muF' : ∀ B C, F'.obj (T₃.obj (B, C)) ≅ T₄.obj (F'.obj B, F'.obj C))
    (muG : ∀ B C, G.obj (T₁.obj (B, C)) ≅ T₃.obj (G.obj B, G.obj C))
    (muH : ∀ B C, H.obj (T₂.obj (B, C)) ≅ T₄.obj (H.obj B, H.obj C)) : Prop :=
  ∀ B C : D₁,
    theta.hom.app (T₁.obj (B, C)) ≫ H.map (muF B C).hom ≫
        (muH (F.obj B) (F.obj C)).hom =
      F'.map (muG B C).hom ≫ (muF' (G.obj B) (G.obj C)).hom ≫
        T₄.map (Prod.mkHom (theta.hom.app B) (theta.hom.app C))

/-- The displayed open equation, including the definition of z as its last two factors.
This predicate merely spells out an equality in the four supplied categories.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def OpenIdentityAt {U : Type u₁} {X : Type u₂} {U' : Type u₃} {X' : Type u₄}
    [Category.{v₁} U] [Category.{v₂} X] [Category.{v₃} U'] [Category.{v₄} X']
    (TU : U × U ⥤ U) (TX : X × X ⥤ X)
    (TU' : U' × U' ⥤ U') (TX' : X' × X' ⥤ X')
    (H : X ⥤ X') (A : U ⥤ U') (J : X ⥤ U) (J' : X' ⥤ U')
    (O : U ⥤ X) (O' : U' ⥤ X')
    (gamma : ∀ N T, TX.obj (O.obj N, T) ⟶ O.obj (TU.obj (N, J.obj T)))
    (gamma' : ∀ N T, TX'.obj (O'.obj N, T) ⟶ O'.obj (TU'.obj (N, J'.obj T)))
    (beta : ∀ N, H.obj (O.obj N) ⟶ O'.obj (A.obj N))
    (K : U) (P : X)
    (muA : A.obj (TU.obj (K, J.obj P)) ⟶ TU'.obj (A.obj K, A.obj (J.obj P)))
    (muH : H.obj (TX.obj (O.obj K, P)) ⟶ TX'.obj (H.obj (O.obj K), H.obj P))
    (sigma : A.obj (J.obj P) ⟶ J'.obj (H.obj P)) : Prop :=
  H.map (gamma K P) ≫ beta (TU.obj (K, J.obj P)) ≫
      O'.map (muA ≫ TU'.map (Prod.mkHom (𝟙 (A.obj K)) sigma)) =
    muH ≫ TX'.map (Prod.mkHom (beta K) (𝟙 (H.obj P))) ≫
      gamma' (A.obj K) (H.obj P)

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
variable (E : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]

/-- Inverses in residue fields, transported from the coefficient prime's inverse in k.
Source: global coefficient convention of the blueprint
(blueprint: lem-sf-pf-open-base-change-square). -/
@[instance_reducible] def units (W : SixFunctorSpace D) : ∀ x : W.obj.left,
    Invertible (c.l : W.obj.left.residueField x) :=
  fun x ↦ (map_natCast (W.obj.hom.residueFieldAlgebraMap x) c.l) ▸
    ((PurCompactSupport.coefficientPrimeUnit c.l D c.different).map
      (W.obj.hom.residueFieldAlgebraMap x)).invertible

/-- The existing canonical finite tensor comparison; no invertibility assumption is added.
Source: Stacks 07A4, normalized in lem-pur-derived-pullback-tensor-iso
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteMu {X Y : SixFunctorSpace D} (f : X ⟶ Y) (n : ℕ) :=
  @canonicalFinitePullbackTensor c.l _ E _ _ _ X.obj.left Y.obj.left f.hom.left n
    (units D c X) (units D c Y)

/-- Completed pullback on the recorded full constructible categories.
Source: def-weil-derived-pullback-tensor-hom, integral clause
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  @constructibleIntegralPullback c.l _ E _ _ _ X.obj.left Y.obj.left f.hom.left
    (units D c X) (units D c Y)

/-- The recorded completed tensor on the full constructible category.
Source: def-weil-derived-pullback-tensor-hom, integral clause
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralTensor (W : SixFunctorSpace D) :=
  @constructibleIntegralTensor c.l _ E _ _ _ W.obj.left (units D c W)

/-- The specified completed tensor comparison, retaining its strict quotient construction.
Source: lem-pur-derived-pullback-tensor-iso
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralMu {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  @canonicalIntegralPullbackTensor c.l _ E _ _ _ X.obj.left Y.obj.left f.hom.left
    (units D c X) (units D c Y)

/-- The composition-normalized integral pullback square.
Source: Stacks 0D6D; lem-pur-derived-pullback-tensor-iso
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralTheta (Q : SixFunctorCompactifiedSquare D) :
    integralPull D c E Q.g ⋙ integralPull D c E Q.p' ≅
      integralPull D c E Q.p ⋙ integralPull D c E Q.h :=
  (@pullbackTensorIntegralComposition c.l _ E _ _ _ Q.Y'.obj.left Q.Y.obj.left
    Q.Z'.obj.left Q.g.hom.left Q.p'.hom.left (units D c Q.Y') (units D c Q.Y)
      (units D c Q.Z')).symm ≪≫
    eqToIso (congrArg (fun f ↦ @constructibleIntegralPullback c.l _ E _ _ _
      Q.Z'.obj.left Q.Y.obj.left f (units D c Q.Z') (units D c Q.Y))
        Q.properSquare.w.symm) ≪≫
    @pullbackTensorIntegralComposition c.l _ E _ _ _ Q.Z.obj.left Q.Y.obj.left
      Q.Z'.obj.left Q.p.hom.left Q.h.hom.left (units D c Q.Z) (units D c Q.Y)
        (units D c Q.Z')

variable (n : ℕ)

/-- Ordinary finite extension by zero for the left open factor.
Source: def-exchange-projection, finite clause
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteOpen (Q : SixFunctorCompactifiedSquare D) :=
  @sfIntrinsicDerivedOpen (finiteCoefficientRing c.l E (n + 1)) _
    (pullbackTensorCoefficientFinite c.l E n) _ _ Q.i.hom.left Q.open_i

/-- Ordinary finite extension by zero for the base-changed open factor.
Source: def-exchange-projection, finite clause
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteOpen' (Q : SixFunctorCompactifiedSquare D) :=
  @sfIntrinsicDerivedOpen (finiteCoefficientRing c.l E (n + 1)) _
    (pullbackTensorCoefficientFinite c.l E n) _ _ Q.i'.hom.left Q.open_i'

/-- The canonical open maps at finite coefficients. Their inverse open-unit transposes
fix gamma and gamma prime uniquely, and beta is fixed by its actual mate. Thus these
are presentations of the maps in def-exchange-projection, never free comparison maps.
Naturality in both arguments is included by using natural isomorphisms.
Source: Stacks 03DI, 0E8I, 0GL1; def-exchange-projection
(blueprint: lem-sf-pf-open-base-change-square). -/
structure FiniteMaps (Q : SixFunctorCompactifiedSquare D) where
  gamma : (finiteOpen D c E n Q).prod (𝟭 _) ⋙
      finiteIntrinsicDerivedTensor c.l E Q.Z.obj.left n ≅
    (𝟭 _).prod (finiteDerivedPullback c.l E n Q.i.hom.left) ⋙
      finiteIntrinsicDerivedTensor c.l E Q.X.obj.left n ⋙ finiteOpen D c E n Q
  gamma' : (finiteOpen' D c E n Q).prod (𝟭 _) ⋙
      finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n ≅
    (𝟭 _).prod (finiteDerivedPullback c.l E n Q.i'.hom.left) ⋙
      finiteIntrinsicDerivedTensor c.l E Q.X'.obj.left n ⋙ finiteOpen' D c E n Q
  gamma_normalized : ∀ K P,
    (@exceptionalOpenAdjunction _ _ Q.i.hom.left Q.open_i
      (finiteCoefficientRing c.l E (n + 1)) _
        (pullbackTensorCoefficientFinite c.l E n)).homEquiv _ _ (gamma.inv.app (K, P)) =
      (finiteIntrinsicDerivedTensor c.l E Q.X.obj.left n).map
        (Prod.mkHom ((@sfIntrinsicDerivedOpenUnit
          (finiteCoefficientRing c.l E (n + 1)) _
          (pullbackTensorCoefficientFinite c.l E n) _ _ Q.i.hom.left Q.open_i).app K) (𝟙 _)) ≫
        (finiteMu D c E Q.i n ((finiteOpen D c E n Q).obj K) P).inv
  gamma'_normalized : ∀ K P,
    (@exceptionalOpenAdjunction _ _ Q.i'.hom.left Q.open_i'
      (finiteCoefficientRing c.l E (n + 1)) _
        (pullbackTensorCoefficientFinite c.l E n)).homEquiv _ _ (gamma'.inv.app (K, P)) =
      (finiteIntrinsicDerivedTensor c.l E Q.X'.obj.left n).map
        (Prod.mkHom ((@sfIntrinsicDerivedOpenUnit
          (finiteCoefficientRing c.l E (n + 1)) _
          (pullbackTensorCoefficientFinite c.l E n) _ _ Q.i'.hom.left Q.open_i').app K)
          (𝟙 _)) ≫
        (finiteMu D c E Q.i' n ((finiteOpen' D c E n Q).obj K) P).inv
  beta : finiteOpen D c E n Q ⋙ finiteDerivedPullback c.l E n Q.h.hom.left ≅
    finiteDerivedPullback c.l E n Q.g'.hom.left ⋙ finiteOpen' D c E n Q
  beta_normalized : beta.inv =
    @sfIntrinsicDerivedOpenMate (finiteCoefficientRing c.l E (n + 1)) _
      (pullbackTensorCoefficientFinite c.l E n) _ _ _ _ Q.g'.hom.left Q.i'.hom.left
        Q.i.hom.left Q.h.hom.left Q.open_i Q.open_i' Q.openSquare.w

/-- Composition comparison for the proper Cartesian square at finite level.
Source: Stacks 0D6D (blueprint: lem-sf-pf-open-base-change-square). -/
def finiteTheta (Q : SixFunctorCompactifiedSquare D) :=
  (sfIntrinsicDerivedSquarePullback (finiteCoefficientRing c.l E (n + 1))
    Q.h.hom.left Q.p'.hom.left Q.p.hom.left Q.g.hom.left Q.properSquare.w).symm

/-- The open Cartesian square with its canonical pullback identification.
Source: the blueprint base-change diagram
(blueprint: lem-sf-pf-open-base-change-square). -/
def openSquare (Q : SixFunctorCompactifiedSquare D) :
    OpenImmersionSquare Q.g'.hom.left Q.i'.hom.left Q.i.hom.left Q.h.hom.left where
  w := Q.openSquare.w
  isoPullback := Q.openSquare.isoPullback
  hom_fst := Q.openSquare.isoPullback_hom_fst
  hom_snd := Q.openSquare.isoPullback_hom_snd
  isOpenImmersion := Q.open_i
  isOpenImmersion' := Q.open_i'

/-- Presentations of the specified completed maps, with strict quotient normalization.
These are the already recorded open-factor data, including the two target tensor models.
Source: lem-sf-pf-open-factor-coherence, clauses (1)--(3)
(blueprint: lem-sf-pf-open-base-change-square). -/
def IntegralMaps (Q : SixFunctorCompactifiedSquare D) :=
  letI := Q.open_i
  letI := Q.open_i'
  OpenFactorCoherence.Assertion c.l E (openSquare D Q) ×
    OpenFactorCoherence.Tensor c.l E Q.X'.obj.left ×
    OpenFactorCoherence.Tensor c.l E Q.Z'.obj.left

/-- Actual integral extension by zero.
Source: def-exchange-projection (blueprint: lem-sf-pf-open-base-change-square). -/
def integralOpen (Q : SixFunctorCompactifiedSquare D) :=
  letI := Q.open_i
  OpenFactorCoherence.J c.l E Q.i.hom.left

/-- Actual integral extension by zero after base change.
Source: def-exchange-projection (blueprint: lem-sf-pf-open-base-change-square). -/
def integralOpen' (Q : SixFunctorCompactifiedSquare D) :=
  letI := Q.open_i'
  OpenFactorCoherence.J c.l E Q.i'.hom.left

/-- The existing canonical completed exchange, before finite evaluation.
Source: lem-sf-pf-open-factor-coherence, clause (3)
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralBeta (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps D c E Q) :=
  letI := Q.open_i
  letI := Q.open_i'
  OpenFactorCoherence.beta c.l E d.1.ambientExchange d.1.horizontal
    d.1.horizontalU d.1.openData'

/-- The existing canonical completed open tensor map.
Source: lem-sf-pf-open-factor-coherence, clause (3)
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralGamma (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps D c E Q) :=
  letI := Q.open_i
  letI := Q.open_i'
  letI := Q.open_i
  OpenFactorCoherence.gamma c.l E d.1.openData d.1.tensorU d.1.tensorX

/-- The same actual tensor map for the base-changed open immersion.
Source: lem-sf-pf-open-factor-coherence, clause (3)
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralGamma' (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps D c E Q) :=
  letI := Q.open_i'
  letI := Q.open_i
  OpenFactorCoherence.gamma c.l E d.1.openData' d.2.1 d.2.2

/-- Ordinary open restriction, identified with completed restriction on complete objects.
Source: lem-sf-pf-open-factor-coherence, clause (1)
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralJ (Q : SixFunctorCompactifiedSquare D) :=
  OpenFactorCoherence.star c.l E Q.i.hom.left

/-- Restriction after base change.
Source: lem-sf-pf-open-factor-coherence, clause (1)
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralJ' (Q : SixFunctorCompactifiedSquare D) :=
  OpenFactorCoherence.star c.l E Q.i'.hom.left

/-- The canonical completed square comparison in the source's sigma orientation.
Source: lem-sf-pf-open-factor-coherence, square_unit
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralSigma (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps D c E Q) :=
  letI := Q.open_i
  letI := Q.open_i'
  d.1.completedSquare.symm

/-- The ambient arrow of the recorded constructible tensor comparison.
Source: lem-pur-derived-pullback-tensor-iso
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralMuHom {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (B C : DerivedCategory (scalarReductionSource.{u, u} c.l E Y.obj.left))
    (hB : sfIntegralConstructible c.l E Y.obj.left B)
    (hC : sfIntegralConstructible c.l E Y.obj.left C) :=
  ((integralMu D c E f) ⟨B, hB⟩ ⟨C, hC⟩).hom.hom

/-- The source's M = j shriek K.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralM (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left)) :=
  (integralOpen D c E Q).obj K

/-- The source's P = F L.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralP (Q : SixFunctorCompactifiedSquare D)
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left)) :=
  (integralDerivedPullback.{u, u} c.l E Q.p.hom.left).obj L

/-- The source's Q = M tensor P.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralQ (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left)) :=
  (integralCompletedTensor.{u, u} c.l E Q.Z.obj.left).obj
    (integralM D c E Q K, integralP D c E Q L)

/-- The source's V = K tensor J P.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralV (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left)) :=
  (integralCompletedTensor.{u, u} c.l E Q.X.obj.left).obj
    (K, (integralJ D c E Q).obj (integralP D c E Q L))

/-- The source's W = A K tensor J prime H P.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def integralW (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left)) :=
  (integralCompletedTensor.{u, u} c.l E Q.X'.obj.left).obj
    ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj K,
      (integralJ' D c E Q).obj
        ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj (integralP D c E Q L)))

/-- Every integral object in the open equation and the four proper images is on
its bounded constructible derived-complete domain. These are conclusions, not hypotheses.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
structure IntegralDomains (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left)) : Prop where
  M : sfIntegralConstructible c.l E Q.Z.obj.left
    (integralM D c E Q K)
  P : sfIntegralConstructible c.l E Q.Z.obj.left
    (integralP D c E Q L)
  tensorQ : sfIntegralConstructible c.l E Q.Z.obj.left
    (integralQ D c E Q K L)
  JP : sfIntegralConstructible c.l E Q.X.obj.left
    ((integralJ D c E Q).obj (integralP D c E Q L))
  V : sfIntegralConstructible c.l E Q.X.obj.left
    (integralV D c E Q K L)
  AK : sfIntegralConstructible c.l E Q.X'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj K)
  HP : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj
      (integralP D c E Q L))
  HM : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj
      (integralM D c E Q K))
  HQ : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj
      (integralQ D c E Q K L))
  AJP : sfIntegralConstructible c.l E Q.X'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj
      ((integralJ D c E Q).obj (integralP D c E Q L)))
  AV : sfIntegralConstructible c.l E Q.X'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj
      (integralV D c E Q K L))
  JHP : sfIntegralConstructible c.l E Q.X'.obj.left
    ((integralJ' D c E Q).obj
      ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj (integralP D c E Q L)))
  W : sfIntegralConstructible c.l E Q.X'.obj.left
    (integralW D c E Q K L)
  extensionV : sfIntegralConstructible c.l E Q.Z.obj.left
    ((integralOpen D c E Q).obj (integralV D c E Q K L))
  extensionAV : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralOpen' D c E Q).obj
      ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj (integralV D c E Q K L)))
  extensionAK : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralOpen' D c E Q).obj
      ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj K))
  extensionW : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralOpen' D c E Q).obj (integralW D c E Q K L))
  SM : sfIntegralConstructible c.l E Q.Y.obj.left
    ((sfCompletedDerivedDirectImage c.l E Q.p.hom.left).obj
      (integralM D c E Q K))
  SQ : sfIntegralConstructible c.l E Q.Y.obj.left
    ((sfCompletedDerivedDirectImage c.l E Q.p.hom.left).obj
      (integralQ D c E Q K L))
  SHM : sfIntegralConstructible c.l E Q.Y'.obj.left
    ((sfCompletedDerivedDirectImage c.l E Q.p'.hom.left).obj
      ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj (integralM D c E Q K)))
  SHQ : sfIntegralConstructible c.l E Q.Y'.obj.left
    ((sfCompletedDerivedDirectImage c.l E Q.p'.hom.left).obj
      ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj (integralQ D c E Q K L)))
  HextensionV : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj
      ((integralOpen D c E Q).obj (integralV D c E Q K L)))
  betaTensor : sfIntegralConstructible c.l E Q.Z'.obj.left
    ((integralCompletedTensor.{u, u} c.l E Q.Z'.obj.left).obj
      ((integralOpen' D c E Q).obj ((integralDerivedPullback.{u, u} c.l E Q.g'.hom.left).obj K),
        (integralDerivedPullback.{u, u} c.l E Q.h.hom.left).obj (integralP D c E Q L)))

/-- The completed open equation uses the ambient arrows of the recorded comparisons.
Domain proofs are obtained in the conclusion IntegralDomains.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def IntegralEquation (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps D c E Q)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left))
    (hK : sfIntegralConstructible c.l E Q.X.obj.left K)
    (dom : IntegralDomains D c E Q K L) : Prop :=
  OpenIdentityAt
    (integralCompletedTensor.{u, u} c.l E Q.X.obj.left)
    (integralCompletedTensor.{u, u} c.l E Q.Z.obj.left)
    (integralCompletedTensor.{u, u} c.l E Q.X'.obj.left)
    (integralCompletedTensor.{u, u} c.l E Q.Z'.obj.left)
    (integralDerivedPullback.{u, u} c.l E Q.h.hom.left)
    (integralDerivedPullback.{u, u} c.l E Q.g'.hom.left)
    (integralJ D c E Q) (integralJ' D c E Q)
    (integralOpen D c E Q) (integralOpen' D c E Q)
    (integralGamma D c E Q d) (integralGamma' D c E Q d)
    (integralBeta D c E Q d) K (integralP D c E Q L)
    (integralMuHom D c E Q.g' K
      ((integralJ D c E Q).obj (integralP D c E Q L)) hK dom.JP)
    (integralMuHom D c E Q.h (integralM D c E Q K) (integralP D c E Q L)
      dom.M dom.P)
    ((integralSigma D c E Q d).hom.app (integralP D c E Q L))

/-- The finite open equation is in the ambient derived category.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def FiniteEquation (Q : SixFunctorCompactifiedSquare D) (d : FiniteMaps D c E n Q)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))) :
    Prop :=
  OpenIdentityAt
    (finiteIntrinsicDerivedTensor c.l E Q.X.obj.left n)
    (finiteIntrinsicDerivedTensor c.l E Q.Z.obj.left n)
    (finiteIntrinsicDerivedTensor c.l E Q.X'.obj.left n)
    (finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n)
    (finiteDerivedPullback c.l E n Q.h.hom.left)
    (finiteDerivedPullback c.l E n Q.g'.hom.left)
    (finiteDerivedPullback c.l E n Q.i.hom.left)
    (finiteDerivedPullback c.l E n Q.i'.hom.left)
    (finiteOpen D c E n Q) (finiteOpen' D c E n Q)
    (fun N T ↦ d.gamma.hom.app (N, T)) (fun N T ↦ d.gamma'.hom.app (N, T))
    d.beta.hom.app K ((finiteDerivedPullback c.l E n Q.p.hom.left).obj L)
    ((finiteMu D c E Q.g' n K
      ((finiteDerivedPullback c.l E n Q.i.hom.left).obj
        ((finiteDerivedPullback c.l E n Q.p.hom.left).obj L))).hom)
    ((finiteMu D c E Q.h n ((finiteOpen D c E n Q).obj K)
      ((finiteDerivedPullback c.l E n Q.p.hom.left).obj L)).hom)
    ((sfIntrinsicDerivedSquarePullback (finiteCoefficientRing c.l E (n + 1))
      Q.g'.hom.left Q.i'.hom.left Q.i.hom.left Q.h.hom.left Q.openSquare.w).hom.app
        ((finiteDerivedPullback c.l E n Q.p.hom.left).obj L))

/-- The source's M = j shriek K.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteM (Q : SixFunctorCompactifiedSquare D)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1))) :=
  (finiteOpen D c E n Q).obj K

/-- The source's P = F L.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteP (Q : SixFunctorCompactifiedSquare D)
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))) :=
  (finiteDerivedPullback c.l E n Q.p.hom.left).obj L

/-- The source's Q = M tensor P.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteQ (Q : SixFunctorCompactifiedSquare D)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))) :=
  (finiteIntrinsicDerivedTensor c.l E Q.Z.obj.left n).obj
    (finiteM D c E n Q K, finiteP D c E n Q L)

/-- The source's V = K tensor J P.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteV (Q : SixFunctorCompactifiedSquare D)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))) :=
  (finiteIntrinsicDerivedTensor c.l E Q.X.obj.left n).obj
    (K, (finiteDerivedPullback c.l E n Q.i.hom.left).obj (finiteP D c E n Q L))

/-- The source's W = A K tensor J prime H P.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
def finiteW (Q : SixFunctorCompactifiedSquare D)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))) :=
  (finiteIntrinsicDerivedTensor c.l E Q.X'.obj.left n).obj
    ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj K,
      (finiteDerivedPullback c.l E n Q.i'.hom.left).obj
        ((finiteDerivedPullback c.l E n Q.h.hom.left).obj (finiteP D c E n Q L)))

/-- Bounded constructibility of all finite open-equation inputs and tensors.
No Tor condition is imposed on the first input.
Source: blueprint base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square). -/
structure FiniteDomains (Q : SixFunctorCompactifiedSquare D)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))) : Prop where
  M : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z.obj.left
    (finiteM D c E n Q K)
  P : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z.obj.left
    (finiteP D c E n Q L)
  tensorQ : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z.obj.left
    (finiteQ D c E n Q K L)
  JP : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X.obj.left
    ((finiteDerivedPullback c.l E n Q.i.hom.left).obj (finiteP D c E n Q L))
  V : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X.obj.left
    (finiteV D c E n Q K L)
  AK : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X'.obj.left
    ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj K)
  HP : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteDerivedPullback c.l E n Q.h.hom.left).obj
      (finiteP D c E n Q L))
  HM : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteDerivedPullback c.l E n Q.h.hom.left).obj
      (finiteM D c E n Q K))
  HQ : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteDerivedPullback c.l E n Q.h.hom.left).obj
      (finiteQ D c E n Q K L))
  AJP : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X'.obj.left
    ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj
      ((finiteDerivedPullback c.l E n Q.i.hom.left).obj (finiteP D c E n Q L)))
  AV : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X'.obj.left
    ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj
      (finiteV D c E n Q K L))
  JHP : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X'.obj.left
    ((finiteDerivedPullback c.l E n Q.i'.hom.left).obj
      ((finiteDerivedPullback c.l E n Q.h.hom.left).obj (finiteP D c E n Q L)))
  W : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X'.obj.left
    (finiteW D c E n Q K L)
  extensionV : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z.obj.left
    ((finiteOpen D c E n Q).obj (finiteV D c E n Q K L))
  extensionAV : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteOpen' D c E n Q).obj
      ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj (finiteV D c E n Q K L)))
  extensionAK : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteOpen' D c E n Q).obj
      ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj K))
  extensionW : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteOpen' D c E n Q).obj (finiteW D c E n Q K L))
  HextensionV : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteDerivedPullback c.l E n Q.h.hom.left).obj
      ((finiteOpen D c E n Q).obj (finiteV D c E n Q K L)))
  betaTensor : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Z'.obj.left
    ((finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n).obj
      ((finiteOpen' D c E n Q).obj ((finiteDerivedPullback c.l E n Q.g'.hom.left).obj K),
        (finiteDerivedPullback c.l E n Q.h.hom.left).obj (finiteP D c E n Q L)))

end WeilConjectures.OpenProjectionBaseChange
