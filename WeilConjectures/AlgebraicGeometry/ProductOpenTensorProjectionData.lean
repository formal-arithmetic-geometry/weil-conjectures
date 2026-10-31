/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenProductSwap
public import WeilConjectures.SixFunctors.ProperOpenProjectionMate

/-! # Open tensor and projection identities for a product compactification

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, proper reduction.
(blueprint: lem-pur-product-open-tensor-projection).

All arrows below are composites of the recorded normalized open comparisons,
ordinary derived projection mates and their canonical exact-pullback transports.
No projection arrow or open counit is inverted. The only inverses of units are
those of the fully faithful open-extension adjunctions.
-/

-- Shared definitions (blueprint: def-pur-product-open-tensor-projection-data).

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
open WeilConjectures.FiniteOpenProduct
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.ProductOpenTensorProjection

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Exact inverse-image coordinates for the counit-defined ordinary projection map.
Source: def-exchange-projection, finite formula
(blueprint: lem-pur-product-open-tensor-projection). -/
def projection {T U : Scheme.{u}} (f : T ⟶ U) (M : FiniteD A T) (N : FiniteD A U) :=
  properOpenProjection A f M N ≫
    (ProperOpenPush A f).map
      (((ProperOpenTensor A T).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app N))

/-- The same counit-defined exchange, transported to exact inverse-image coordinates.
Source: def-exchange-projection, finite Ex_* formula
(blueprint: lem-pur-product-open-tensor-projection). -/
def exchange {T' T U' U : Scheme.{u}}
    (p : T' ⟶ T) (q : T' ⟶ U') (f : T ⟶ U) (g : U' ⟶ U)
    (sq : IsPullback p q f g) (M : FiniteD A T) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app
      ((ProperOpenPush A f).obj M) ≫
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M ≫
    (ProperOpenPush A q).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).hom.app M)

/-- The invertible unit for a fully faithful exact open extension.
Source: lem-sf-open-tensor-normalization, unit clause
(blueprint: lem-pur-product-open-tensor-projection). -/
def openUnit {T U : Scheme.{u}} (j : T ⟶ U) [IsOpenImmersion j] (M : FiniteD A T) :
    M ≅ (pull A j).obj ((finiteShriek A j).obj M) :=
  letI : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit_isIso_of_L_fully_faithful
  letI : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).unit.app M)

variable {Xb Zb B X Z : Scheme.{u}}

/-- Properness of the named second projection is proper base change.
Source: lem-weil-pbc-proper-base-change
(blueprint: lem-pur-product-open-tensor-projection). -/
instance secondProper (a : Xb ⟶ B) (b : Zb ⟶ B) [IsProper a] :
    IsProper (second a b) := by
  unfold second product
  dsimp only [id_eq]
  infer_instance

/-- Quasi-compactness of the second open is preserved by base change.
Source: lem-weil-pbc-proper-base-change, base-change calculus
(blueprint: lem-pur-product-open-tensor-projection). -/
instance rightOpenQuasiCompact (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb)
    [QuasiCompact k] : QuasiCompact (rightOpen a b k) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (rightSquare a b k) inferInstance

set_option linter.defProp false in
/-- The defining Cartesian square of the named fibre product.
Source: def-pc-fibre-product
(blueprint: lem-pur-product-open-tensor-projection). -/
def productSquare (a : Xb ⟶ B) (b : Zb ⟶ B) :
    IsPullback (first a b) (second a b) a b := by
  unfold first second product
  exact IsPullback.of_hasPullback a b

set_option linter.defProp false in
/-- The defining square for i: Xbar times Z into Xbar times Zbar.
Source: def-pc-fibre-product
(blueprint: lem-pur-product-open-tensor-projection). -/
def iSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb) :
    rightOpen a b k ≫ second a b = second a (k ≫ b) ≫ k :=
  (rightSquare a b k).w.symm

set_option linter.defProp false in
/-- The two successive opens compose to the product open.
Source: lem-cbc-extension-zero-composition, product factorization
(blueprint: lem-pur-product-open-tensor-projection). -/
def openComposition (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb) :
    leftOpen a (k ≫ b) j ≫ rightOpen a b k = productOpen a b j k := by
  unfold leftOpen rightOpen productOpen product
  dsimp only [id_eq]
  apply pullback.hom_ext <;> simp

set_option linter.defProp false in
/-- Projection equality along j_q, including the chosen pullback projections.
Source: def-pc-fibre-product
(blueprint: lem-pur-product-open-tensor-projection). -/
def qSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb) :
    leftOpen a (k ≫ b) j ≫ second a (k ≫ b) = second (j ≫ a) (k ≫ b) := by
  unfold leftOpen second product
  dsimp only [id_eq]
  simp

variable (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- H=j_! M.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def H (M : FiniteD A X) := (finiteShriek A j).obj M

/-- J=k_! N.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def J (N : FiniteD A Z) := (finiteShriek A k).obj N

/-- D=P_p M tensor P_q N on X times Z.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def D (M : FiniteD A X) (N : FiniteD A Z) :=
  tensor A (product (j ≫ a) (k ≫ b))
    ((pull A (first (j ≫ a) (k ≫ b))).obj M)
    ((pull A (second (j ≫ a) (k ≫ b))).obj N)

/-- F=P_r H.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def F (M : FiniteD A X) := (pull A (first a b)).obj (H A j M)

/-- K=j_q! P_p M.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def K (M : FiniteD A X) := (finiteShriek A (leftOpen a (k ≫ b) j)).obj
  ((pull A (first (j ≫ a) (k ≫ b))).obj M)

/-- K_D=j_q! D.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def KD (M : FiniteD A X) (N : FiniteD A Z) :=
  (finiteShriek A (leftOpen a (k ≫ b) j)).obj (D A a b j k M N)

/-- m=i_! K.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def m (M : FiniteD A X) := (finiteShriek A (rightOpen a b k)).obj (K A a b j k M)

/-- L_0=P_b R_a H.
Source: node notation (blueprint: lem-pur-product-open-tensor-projection). -/
def L0 (M : FiniteD A X) := (pull A b).obj ((ProperOpenPush A a).obj (H A j M))

/-- The actual two-stage comparison e supplied by the open-product node.
Source: lem-pur-finite-open-product-swap
(blueprint: lem-pur-product-open-tensor-projection). -/
def e (M : FiniteD A X) (N : FiniteD A Z) := comparison A a b j k M N

/-- The normalized beta:E=P_i F to K, including projection composition.
Source: lem-sf-open-tensor-normalization
(blueprint: lem-pur-product-open-tensor-projection). -/
def betaI (M : FiniteD A X) :
    (pull A (rightOpen a b k)).obj (F A a b j M) ≅ K A a b j k M :=
  (composeEq A (rightOpen a b k) (first a b) (first a (k ≫ b)) (by
    unfold rightOpen first product
    dsimp only [id_eq]
    simp)).app (H A j M) ≪≫
  (beta A _ _ _ _ (leftSquare a (k ≫ b) j)).app M

/-- chi is the inverse beta extended by zero, followed by the open counit.
Source: node definition of chi (blueprint: lem-pur-product-open-tensor-projection). -/
def chi (M : FiniteD A X) : m A a b j k M ⟶ F A a b j M :=
  (finiteShriek A (rightOpen a b k)).map (betaI A a b j k M).inv ≫
    (adj A (rightOpen a b k)).counit.app (F A a b j M)

/-- A_0 is the actual exchange for the proper square (a,b).
Source: def-exchange-projection, Ex_* formula
(blueprint: lem-pur-product-open-tensor-projection). -/
def A0 (M : FiniteD A X) :=
  exchange A _ _ _ _ (productSquare a b) (H A j M)

/-- The compactification-relative exchange B_0, with the actual open beta.
Source: def-exchange-projection, Ex_!^c
(blueprint: lem-pur-product-open-tensor-projection). -/
def B0 (M : FiniteD A X) :
    (pull A k).obj (L0 A a b j M) ⟶ (ProperOpenPush A (second a (k ≫ b))).obj
      (K A a b j k M) :=
  (pullComp A k b).inv.app ((ProperOpenPush A a).obj (H A j M)) ≫
    exchange A _ _ _ _ (productSquare a (k ≫ b)) (H A j M) ≫
    (ProperOpenPush A (second a (k ≫ b))).map
      ((beta A _ _ _ _ (leftSquare a (k ≫ b) j)).hom.app M)

/-- The tensor d, including the j_q/v projection compositor.
Source: lem-sf-open-tensor-normalization
(blueprint: lem-pur-product-open-tensor-projection). -/
def d (M : FiniteD A X) (N : FiniteD A Z) :
    tensor A (product a (k ≫ b)) (K A a b j k M)
      ((pull A (second a (k ≫ b))).obj N) ⟶ KD A a b j k M N :=
  gamma A (leftOpen a (k ≫ b) j) ((pull A (first (j ≫ a) (k ≫ b))).obj M)
      ((pull A (second a (k ≫ b))).obj N) ≫
    extendedProjectionTensor A (leftOpen a (k ≫ b) j) (second a (k ≫ b))
      (first (j ≫ a) (k ≫ b)) (second (j ≫ a) (k ≫ b)) (qSquare a b j k) M N

/-- P_i P_t J=P_v N, with the open-unit identification explicitly inserted.
Source: canonical pullback compositors and open units
(blueprint: lem-pur-product-open-tensor-projection). -/
def iTensorSecond (N : FiniteD A Z) :
    (pull A (rightOpen a b k)).obj ((pull A (second a b)).obj (J A k N)) ≅
      (pull A (second a (k ≫ b))).obj N :=
  (square A (rightOpen a b k) (second a b) (second a (k ≫ b)) k
    (iSquare a b k)).app (J A k N) ≪≫
    (pull A (second a (k ≫ b))).mapIso (openUnit A k N).symm

/-- The specified w: delta_i, i_!(d), and the open compositor.
Source: node definition of w (blueprint: lem-pur-product-open-tensor-projection). -/
def w (M : FiniteD A X) (N : FiniteD A Z) :
    tensor A (product a b) (m A a b j k M) ((pull A (second a b)).obj (J A k N)) ⟶
      (finiteShriek A (productOpen a b j k)).obj (D A a b j k M N) :=
  gamma A (rightOpen a b k) (K A a b j k M) ((pull A (second a b)).obj (J A k N)) ≫
    (finiteShriek A (rightOpen a b k)).map
      (tensorMap A _ (𝟙 (K A a b j k M)) (iTensorSecond A a b k N).hom ≫
        d A a b j k M N) ≫
    (compTo A (leftOpen a (k ≫ b) j) (rightOpen a b k) (productOpen a b j k)
      (openComposition a b j k)).hom.app (D A a b j k M N)

/-- nu is the two-symmetry open tensor comparison, with the supported factor second.
Source: node definition of nu (blueprint: lem-pur-product-open-tensor-projection). -/
def nu (M : FiniteD A X) (N : FiniteD A Z) := rho A k (L0 A a b j M) N

/-- eta is the open counit tensored with the identity on J.
Source: node definition of eta (blueprint: lem-pur-product-open-tensor-projection). -/
def eta (M : FiniteD A X) (N : FiniteD A Z) :=
  tensorMap A Zb ((adj A k).counit.app (L0 A a b j M)) (𝟙 (J A k N))

/-- delta_k with P_k J identified with N by the specified open unit.
Source: lem-sf-open-tensor-normalization
(blueprint: lem-pur-product-open-tensor-projection). -/
def delta (Q : FiniteD A Z) (N : FiniteD A Z) :=
  gamma A k Q (J A k N) ≫
    (finiteShriek A k).map (tensorMap A Z (𝟙 Q) (openUnit A k N).inv)

variable [IsProper a] [QuasiCompact k]

/-- The actual normalized proper/open Gamma for (i,v,k,t).
Source: lem-sf-proper-open-tensor-compatibility
(blueprint: lem-pur-product-open-tensor-projection). -/
def Gamma :
    ProperOpenPush A (second a (k ≫ b)) ⋙ finiteShriek A k ⟶
      finiteShriek A (rightOpen a b k) ⋙ ProperOpenPush A (second a b) :=
  properOpenMate A (rightOpen a b k) (second a (k ≫ b)) (second a b) k (iSquare a b k)

/-- s=Gamma_K k_!(B_0).
Source: node definition of s (blueprint: lem-pur-product-open-tensor-projection). -/
def s (M : FiniteD A X) :=
  (finiteShriek A k).map (B0 A a b j k M) ≫ (Gamma A a b k).app (K A a b j k M)

/-- The final proper/open mate on K_D, followed by the canonical open compositor.
Source: node definition of Psi and w
(blueprint: lem-pur-product-open-tensor-projection). -/
def GammaD (M : FiniteD A X) (N : FiniteD A Z) :=
  (Gamma A a b k).app (KD A a b j k M N) ≫
    (ProperOpenPush A (second a b)).map
      ((compTo A (leftOpen a (k ≫ b) j) (rightOpen a b k) (productOpen a b j k)
        (openComposition a b j k)).hom.app (D A a b j k M N))

/-- The part of Psi following k_!(B_0 tensor 1), on the specified K and N.
Source: node definition of Psi (blueprint: lem-pur-product-open-tensor-projection). -/
def projectionTail (M : FiniteD A X) (N : FiniteD A Z) :=
  (finiteShriek A k).map
      (projection A (second a (k ≫ b)) (K A a b j k M) N) ≫
    (finiteShriek A k).map ((ProperOpenPush A (second a (k ≫ b))).map (d A a b j k M N)) ≫
    GammaD A a b j k M N

/-- Psi, as the exact counit-defined compactification composite in the node.
Source: node definition of Psi (blueprint: lem-pur-product-open-tensor-projection). -/
def Psi (M : FiniteD A X) (N : FiniteD A Z) :=
  (finiteShriek A k).map (tensorMap A Z (B0 A a b j k M) (𝟙 N)) ≫
    projectionTail A a b j k M N

/-- The common Z-object P_k L_0 tensor N used in all three normalizations.
Source: node open unit identifications
(blueprint: lem-pur-product-open-tensor-projection). -/
def T (M : FiniteD A X) (N : FiniteD A Z) :=
  tensor A Z ((pull A k).obj (L0 A a b j M)) N

/-- The source of nu restricted to Z, using only tensor comparison and the open unit.
Source: node normalization clause
(blueprint: lem-pur-product-open-tensor-projection). -/
def restrictNu (M : FiniteD A X) (N : FiniteD A Z) :=
  tensorPullIso A k (L0 A a b j M) (J A k N) ≪≫
    tensorIsoMap A Z (Iso.refl _) (openUnit A k N).symm

/-- The source of eta restricted to Z, using both specified open units.
Source: node normalization clause
(blueprint: lem-pur-product-open-tensor-projection). -/
def restrictEta (M : FiniteD A X) (N : FiniteD A Z) :=
  tensorPullIso A k ((finiteShriek A k).obj ((pull A k).obj (L0 A a b j M)))
      (J A k N) ≪≫
    tensorIsoMap A Z (openUnit A k ((pull A k).obj (L0 A a b j M))).symm
      (openUnit A k N).symm

/-- m is the extension along u of P_p M, by the canonical open compositor.
Source: lem-cbc-extension-zero-composition
(blueprint: lem-pur-product-open-tensor-projection). -/
def mSupport (M : FiniteD A X) :
    m A a b j k M ≅ (finiteShriek A (productOpen a b j k)).obj
      ((pull A (first (j ≫ a) (k ≫ b))).obj M) :=
  (compTo A (leftOpen a (k ≫ b) j) (rightOpen a b k) (productOpen a b j k)
    (openComposition a b j k)).app _

/-- The canonical restriction of the source of w to D on P.
Source: node supported-source and normalization clauses
(blueprint: lem-pur-product-open-tensor-projection). -/
def restrictW (M : FiniteD A X) (N : FiniteD A Z) :=
  tensorPullIso A (productOpen a b j k) (m A a b j k M)
      ((pull A (second a b)).obj (J A k N)) ≪≫
    tensorIsoMap A (product (j ≫ a) (k ≫ b))
      ((pull A (productOpen a b j k)).mapIso (mSupport A a b j k M) ≪≫
        (openUnit A (productOpen a b j k)
          ((pull A (first (j ≫ a) (k ≫ b))).obj M)).symm)
      ((square A (productOpen a b j k) (second a b)
        (second (j ≫ a) (k ≫ b)) k (by
          unfold productOpen second product
          dsimp only [id_eq]
          simp)).app (J A k N) ≪≫
        (pull A (second (j ≫ a) (k ≫ b))).mapIso (openUnit A k N).symm)


end WeilConjectures.ProductOpenTensorProjection
