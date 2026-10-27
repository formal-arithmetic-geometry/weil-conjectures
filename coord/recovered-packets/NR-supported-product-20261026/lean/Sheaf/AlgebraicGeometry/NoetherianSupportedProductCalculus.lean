module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.AlgebraicGeometry.RegularImmersionClassSystem
public import Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.ClosedSupportPlusAdjunction
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.SignedLineScalarTensorTower
import Sheaf.Paper.SupportedSourceSystemCupCalculus
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.SixFunctors.GeoCartierCoeffExtension
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion

/-! # Supported products and Cartier interchange

Source: ILO, Expose XVI, sections 2.1--2.3, especially Lemma 2.2.2.4,
Proposition 2.2.3.2 and the proof of Theorem 2.3.2, pp. 228--236
(blueprint: lem-per-noetherian-supported-product-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.NoetherianSupportedProducts

/-- The signed Tate object in the ordinary small-etale derived category.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
abbrev line (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) (b : ℤ) : DerivedCategoryModule A X :=
  (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A m X hA b)

/-- Signed supported cohomology in the supported-Hom realization of closedSupportHom.
Source: ILO XVI 2.1; Stacks 0A45
(blueprint: lem-per-noetherian-supported-product-calculus). -/
abbrev H (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (a b : ℤ) :=
  closedConstantDerivedModule A i ⟶ (line A m hA X b)⟦a⟧

/-- Change only the supported source, by its specified restriction map.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def changeSupport (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {Z Z' X : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X)
    (f : Z ⟶ Z') (hf : f ≫ i' = i) (a b : ℤ) (x : H A m hA i a b) :
    H A m hA i' a b :=
  (DerivedCategory.singleFunctor _ 0).map
    (closedConstantSupportChange A i' i f hf) ≫ x

/-- Forget support by precomposing with the constant restriction unit.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def forgetSupport (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (a b : ℤ) (x : H A m hA i a b) :
    ordinaryFiniteUnit A X ⟶ (line A m hA X b)⟦a⟧ :=
  (DerivedCategory.singleFunctor _ 0).map (supportedConstantUnit A i) ≫ x

/-- Realization with derived direct image as source, including its exact-single comparison.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def realize (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a b : ℤ) (x : H A m hA i a b) :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A Z) ⟶
      (line A m hA X b)⟦a⟧ :=
  ((lowerStar (ModuleCat.{u + 1} A) i).singleFunctorCompRightDerivedFunctorIso.app
    (ordinaryFiniteConstant A Z)).hom ≫ x

/-- The normalized multiplication of shifted signed lines.
Source: ILO XVI 2.2.3 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def multiply (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ) :
    (line A m hA X b)⟦a⟧ ⊗ (line A m hA X b')⟦a'⟧ ⟶
      (line A m hA X (b + b'))⟦a + a'⟧ :=
  (derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _ a a').hom ≫
    (shiftFunctor _ (a + a')).map
      ((singleFunctorObjTensorIso
        (Scheme.finiteEtaleTateSheaf A m X hA b)
        (Scheme.finiteEtaleTateSheaf A m X hA b')
        (ObjectProperty.flat_of_tensorIso
          (t.p X hX b (-b) ≪≫ eqToIso (congrArg
            (Scheme.finiteEtaleTateSheaf A m X hA) (add_neg_cancel b)) ≪≫
            eqToIso (by rfl)))).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (t.p X hX b b').hom)

/-- Canonical inverse image of a shifted signed line.
Source: ILO XVI 2.1, 2.2.3 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def targetPullback (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Y X : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
    (hY : IsUnit (m : Γ(Y, ⊤))) (a b : ℤ) :
    (ordinaryFinitePullback A v).obj ((line A m hA X b)⟦a⟧) ≅
      (line A m hA Y b)⟦a⟧ :=
  letI : (ordinaryFinitePullback A v).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) v
  ((ordinaryFinitePullback A v).commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (t.c v hX hY b))

/-- The graph of pullback on supported classes. The source arrow is the canonical closed
exchange, not a chosen comparison. It is invertible for a Cartesian closed pair.
Source: ILO XVI 2.2.3; Stacks 03Q1
(blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def PullsTo (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : IsPullback w i' i v)
    (hX : IsUnit (m : Γ(X, ⊤))) (hX' : IsUnit (m : Γ(X', ⊤))) (a b : ℤ)
    (x : H A m hA i a b) (y : H A m hA i' a b) : Prop :=
  (DerivedCategory.singleFunctor _ 0).map
      (supportedConstantExchange A i i' v w sq.toCommSq) ≫ y =
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).inv.app
        (closedConstantModule A i) ≫
      (ordinaryFinitePullback A v).map x ≫ (targetPullback A m hA t v hX hX' a b).hom

/-- The relative Kummer boundary for an arbitrary framed invertible module.
The extension's lifting torsor is the actual frame torsor, and its specified open
frame maps to zero; this fixes the relative class and the connecting-map sign.
Source: ILO XVI 2.1; Stacks 03AJ, 03PL
(blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def IsFramedBoundary (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L)
    (c : H A m hA i 2 1) : Prop :=
  ∃ (τ : (Scheme.Modules.etaleIsoTorsor L).sheaf.obj.obj
        (op (Scheme.Etale.mk i.openComplement.ι)))
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (α : X.gmSheaf ⟶ E)
    (β : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
    (hαβ : α ≫ β = 0) (hE : (ShortComplex.mk α β hαβ).ShortExact)
    (f : (Scheme.Modules.etaleIsoTorsor L).sheaf ⟶
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E),
    Scheme.Modules.etaleIsoTorsorVal L τ = s ∧
    (∀ (U : X.Etaleᵒᵖ) (g : X.gmSheaf.obj.obj U)
      (p : (Scheme.Modules.etaleIsoTorsor L).sheaf.obj.obj U),
      @id (E.obj.obj U) (f.hom.app U ((Scheme.Modules.etaleIsoTorsor L).vadd U g p)) =
        α.hom.app U g + @id (E.obj.obj U) (f.hom.app U p)) ∧
    (∀ (U : X.Etaleᵒᵖ) (p : (Scheme.Modules.etaleIsoTorsor L).sheaf.obj.obj U),
      β.hom.app U (f.hom.app U p) =
        ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)).obj.map
          ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).op
          ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 X)))
            (supportedIntegralOne X))) ∧
    @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.hom.app (op (Scheme.Etale.mk i.openComplement.ι)) τ) = 0 ∧
    (Ext.mk₀ (supportedIntegralGenerator A i)).comp
        ((Ext.homEquiv.symm c).mapExactFunctor (RawModuleScalarComparison.forget A X))
        (zero_add 2) =
      (hE.extClass.comp (X.kummerSequence_shortExact m hX).extClass
        (rfl : 1 + 1 = 2)).comp
          (Ext.mk₀ (ordinaryFiniteRootMap A m hA X)) (add_zero 2)

/-- Tensor product of open frames through the existing strong monoidal pullback.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
abbrev tensorFrame {X : Scheme.{u}} (W : X.Opens) (L M : X.Modules)
    (s : (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback W.ι).obj L)
    (t : (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback W.ι).obj M) :
    (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback W.ι).obj (L ⊗ M) :=
  (Scheme.Modules.pullback W.ι).map (λ_ (Scheme.Modules.unit X)).inv ≫
    (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback W.ι) _ _) ≫ tensorHom s t ≫
      Functor.LaxMonoidal.μ (Scheme.Modules.pullback W.ι) L M

/-- Ordinary Kummer Chern class, as an abelian cohomology class with the recorded root map.
Source: ILO XVI 1.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def chern (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] :=
  letI := Scheme.Modules.IsInvertible.of_sheafOfModules L
  Sheaf.H.map (ordinaryFiniteRootMap A m hA X) 2
    (X.kummerδ₁ m hX (Scheme.Pic.toCohomologicalPicardGroup X
      (Scheme.Pic.ofIsInvertible L)))

/-- The operations asserted at one coefficient level. All classes are morphisms in the
ordinary etale derived category; the normalization laws below specify the operations.
Source: ILO XVI 2.1--2.3 (blueprint: lem-per-noetherian-supported-product-calculus). -/
structure LevelData (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0) where
  cup : ∀ {Z D X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ),
    H A m hA i a b →ₗ[A] H A m hA j a' b' →ₗ[A]
      H A m hA (intersectionSupport i j) (a + a') (b + b')
  action : ∀ {Z Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ),
    H A m hA i a b →ₗ[A] H A m hA j a' b' →ₗ[A]
      H A m hA (i ≫ j) (a + a') (b + b')
  e : ∀ {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s], H A m hA i 2 1
  c1 : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (m : Γ(X, ⊤)))
    (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L],
    ordinaryFiniteUnit A X ⟶ (line A m hA X 1)⟦(2 : ℤ)⟧

/-- View an absolute class on the identity closed support.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def onIdentity (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) (a b : ℤ)
    (x : ordinaryFiniteUnit A X ⟶ (line A m hA X b)⟦a⟧) : H A m hA (𝟙 X) a b :=
  (DerivedCategory.singleFunctor _ 0).map
    ((lowerStarId (ModuleCat.{u + 1} A) X).hom.app (ordinaryFiniteConstant A X)) ≫ x

/-- Relabel equal support arrows; the map is the equality transport on their sources.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
def relabel (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {Z X : Scheme.{u}} {i j : Z ⟶ X} (h : i = j) (a b : ℤ)
    (x : H A m hA i a b) : H A m hA j a b :=
  eqToHom (congrArg (closedConstantDerivedModule A) h).symm ≫ x

/-- Cup with an absolute class and return to the original support by the canonical
identity-intersection section. This is also the product for a class on a closed ambient.
Source: ILO XVI 2.2.3 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def cupAbsolute (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (O : LevelData A m hA) {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsUnit (m : Γ(X, ⊤)))
    (a a' b b' : ℤ) (x : H A m hA i a b)
    (y : ordinaryFiniteUnit A X ⟶ (line A m hA X b')⟦a'⟧) :
    H A m hA i (a + a') (b + b') :=
  changeSupport A m hA (intersectionSupport i (𝟙 X)) i
    (pullback.lift (𝟙 Z) i (by simp)) (by simp [intersectionSupport]) _ _
      (O.cup i (𝟙 X) hX a a' b b' x (onIdentity A m hA X a' b' y))

/-- Absolute cup, obtained from the same supported pairing by forgetting support.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def absoluteCup (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (O : LevelData A m hA) (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ)
    (x : ordinaryFiniteUnit A X ⟶ (line A m hA X b)⟦a⟧)
    (y : ordinaryFiniteUnit A X ⟶ (line A m hA X b')⟦a'⟧) :
    ordinaryFiniteUnit A X ⟶ (line A m hA X (b + b'))⟦a + a'⟧ :=
  forgetSupport A m hA (𝟙 X) _ _
    (cupAbsolute A m hA O (𝟙 X) hX a a' b b' (onIdentity A m hA X a b x) y)

/-- Pullback of an absolute class through the canonical constant and signed-line comparisons.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def absolutePullback (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Scheme.FiniteEtaleTwistPullbackData A m hA) {Y X : Scheme.{u}} (v : Y ⟶ X)
    (hX : IsUnit (m : Γ(X, ⊤))) (hY : IsUnit (m : Γ(Y, ⊤))) (a b : ℤ)
    (x : ordinaryFiniteUnit A X ⟶ (line A m hA X b)⟦a⟧) :
    ordinaryFiniteUnit A Y ⟶ (line A m hA Y b)⟦a⟧ :=
  (ordinaryFiniteUnitPullback A v).inv ≫ (ordinaryFinitePullback A v).map x ≫
    (targetPullback A m hA t v hX hY a b).hom

/-- The pseudo-divisor operator on every smaller support is the nested action by e.
Its source is the cohomology on Y supported on Z, not an ambient-X cohomology group.
Source: ILO XVI 2.1 (blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def gysin (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (O : LevelData A m hA) {Z Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (k : Z ⟶ Y) (i : Y ⟶ X) [IsClosedImmersion k] [IsClosedImmersion i]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s]
    (a b : ℤ) (x : H A m hA k a b) : H A m hA (k ≫ i) (a + 2) (b + 1) :=
  O.action k i hY hX a 2 b 1 x (O.e i hX L s)

/-- The projection-normalized composition description of the nested action. The same
composite transposes under the fixed closed-support adjunctions to exceptional composition.
The Koszul sign compares the reversed projection factors with the stated order of action.
Source: ILO XVI 2.1, 2.2.3; Stacks 0B56
(blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def IsComposition (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b')
    (z : H A m hA (i ≫ j) (a + a') (b + b')) : Prop :=
  ∃ δ : (ordinaryFinitePushforward A j).obj ((line A m hA Y b)⟦a⟧) ⟶
      (line A m hA X (b + b'))⟦a + a'⟧,
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
        (ordinaryFiniteUnit A Y)).app ((line A m hA X b)⟦a⟧) ≫
      (ordinaryFinitePushforward A j).map
        (tensorHom (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom
          (targetPullback A m hA t j hX hY a b).hom ≫ (λ_ _).hom) ≫ δ =
      ((-1 : ℤ) ^ (a * a').natAbs) •
        (tensorHom (realize A m hA j a' b' y) (𝟙 _) ≫
          multiply A m hA t X hX a' a b' b ≫
          eqToHom (congrArg₂ (fun r q ↦ (line A m hA X r)⟦q⟧)
            (add_comm b' b) (add_comm a' a))) ∧
    realize A m hA (i ≫ j) _ _ z =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) i j).inv.app
          (ordinaryFiniteUnit A Z) ≫
        (ordinaryFinitePushforward A j).map (realize A m hA i a b x) ≫ δ

/-- All normalization, algebra, pullback and pseudo-divisor laws at one level.
`HEq` below expresses only the canonical equality transports in integer degrees, weights,
and equal composite support arrows. For nonidentical intersection schemes the explicit
canonical support map is composed before the equality is asserted.
Source: ILO XVI 2.1--2.3 (blueprint: lem-per-noetherian-supported-product-calculus). -/
structure LevelLaws (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    (O : LevelData A m hA) : Prop where
  sections_identification : ∀ {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i],
    ∃ e : closedSupportHomFunctor A i ≅ supportedEtaleSections A X i.openComplement,
      e.hom ≫ supportedEtaleSectionsι A X i.openComplement = closedSupportHomToSections A i
  cup_normalization : ∀ {Z D X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b'),
    closedConstantDerivedTensorMap A i j ≫ O.cup i j hX a a' b b' x y =
      tensorHom x y ≫ multiply A m hA t X hX a a' b b'
  cup_associative : ∀ {Z D E X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
    (hX : IsUnit (m : Γ(X, ⊤))) (a a' a'' b b' b'' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b') (z : H A m hA k a'' b''),
    HEq (O.cup (intersectionSupport i j) k hX (a + a') a'' (b + b') b''
      (O.cup i j hX a a' b b' x y) z)
      ((DerivedCategory.singleFunctor _ 0).map
          (closedConstantAssociativitySupportMap A i j k) ≫
        O.cup i (intersectionSupport j k) hX a (a' + a'') b (b' + b'') x
          (O.cup j k hX a' a'' b' b'' y z))
  cup_interchange : ∀ {Z D X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b'),
    HEq (O.cup i j hX a a' b b' x y)
      (((-1 : ℤ) ^ (a * a').natAbs) •
        ((DerivedCategory.singleFunctor _ 0).map
            (closedConstantSymmetrySupportMap A j i) ≫ O.cup j i hX a' a b' b y x))
  action_composition : ∀ {Z Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (a a' b b' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b'),
    IsComposition A m hA t i j hY hX a a' b b' x y
      (O.action i j hY hX a a' b b' x y)
  action_associative : ∀ {Z Y X T : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian X] [IsNoetherian T]
    (i : Z ⟶ Y) (j : Y ⟶ X) (k : X ⟶ T)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    (hT : IsUnit (m : Γ(T, ⊤))) (a a' a'' b b' b'' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b') (z : H A m hA k a'' b''),
    HEq (O.action (i ≫ j) k hX hT (a + a') a'' (b + b') b''
      (O.action i j hY hX a a' b b' x y) z)
      (O.action i (j ≫ k) hY hT a (a' + a'') b (b' + b'') x
        (O.action j k hX hT a' a'' b' b'' y z))
  projection : ∀ {Z Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    (a a' a'' b b' b'' : ℤ) (x : H A m hA i a b)
    (y : ordinaryFiniteUnit A Y ⟶ (line A m hA Y b')⟦a'⟧)
    (z : H A m hA j a'' b''),
    HEq (O.action i j hY hX (a + a') a'' (b + b') b''
      (cupAbsolute A m hA O i hY a a' b b' x y) z)
      (O.action i j hY hX a (a' + a'') b (b' + b'') x
        (relabel A m hA (Category.id_comp j) _ _
          (O.action (𝟙 Y) j hY hX a' a'' b' b''
            (onIdentity A m hA Y a' b' y) z)))
  exceptional_composition : ∀ [Finite A] {Z Y X : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (U : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (V : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (W : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (f : (rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) i).obj U ⟶ V)
    (g : (rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj V ⟶ W),
    (((closedSupportPlusAdjunction A i).comp (closedSupportPlusAdjunction A j)).homEquiv U W)
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).map f ≫ g) =
      ((closedSupportPlusAdjunction A i).homEquiv U ((closedSupportPlus A j).obj W))
        (f ≫ ((closedSupportPlusAdjunction A j).homEquiv V W) g)
  pullback_exists : ∀ {Z X Z' X' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : IsPullback w i' i v)
    (hX : IsUnit (m : Γ(X, ⊤))) (hX' : IsUnit (m : Γ(X', ⊤))) (a b : ℤ)
    (x : H A m hA i a b), ∃! y : H A m hA i' a b,
      PullsTo A m hA t i i' v w sq hX hX' a b x y
  cup_pullback : ∀ {Z D X Z' D' X' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (i : Z ⟶ X) (j : D ⟶ X) (i' : Z' ⟶ X') (j' : D' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion i'] [IsClosedImmersion j']
    (v : X' ⟶ X) (w : Z' ⟶ Z) (w' : D' ⟶ D)
    (sq : IsPullback w i' i v) (sq' : IsPullback w' j' j v)
    (wI : pullback i' j' ⟶ pullback i j)
    (sqI : IsPullback wI (intersectionSupport i' j') (intersectionSupport i j) v)
    (hX : IsUnit (m : Γ(X, ⊤))) (hX' : IsUnit (m : Γ(X', ⊤))) (a a' b b' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b')
    (x' : H A m hA i' a b) (y' : H A m hA j' a' b'),
    PullsTo A m hA t i i' v w sq hX hX' a b x x' →
    PullsTo A m hA t j j' v w' sq' hX hX' a' b' y y' →
    PullsTo A m hA t (intersectionSupport i j) (intersectionSupport i' j') v wI sqI
      hX hX' (a + a') (b + b') (O.cup i j hX a a' b b' x y)
        (O.cup i' j' hX' a a' b b' x' y')
  action_pullback : ∀ {Z Y X Z' Y' X' : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian X] [IsNoetherian Y'] [IsNoetherian X']
    (i : Z ⟶ Y) (j : Y ⟶ X) (i' : Z' ⟶ Y') (j' : Y' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion i'] [IsClosedImmersion j']
    (vZ : Z' ⟶ Z) (vY : Y' ⟶ Y) (vX : X' ⟶ X)
    (sq : IsPullback vZ i' i vY) (sq' : IsPullback vY j' j vX)
    (sqC : IsPullback vZ (i' ≫ j') (i ≫ j) vX)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    (hY' : IsUnit (m : Γ(Y', ⊤))) (hX' : IsUnit (m : Γ(X', ⊤))) (a a' b b' : ℤ)
    (x : H A m hA i a b) (y : H A m hA j a' b')
    (x' : H A m hA i' a b) (y' : H A m hA j' a' b'),
    PullsTo A m hA t i i' vY vZ sq hY hY' a b x x' →
    PullsTo A m hA t j j' vX vY sq' hX hX' a' b' y y' →
    PullsTo A m hA t (i ≫ j) (i' ≫ j') vX vZ sqC hX hX' (a + a') (b + b')
      (O.action i j hY hX a a' b b' x y) (O.action i' j' hY' hX' a a' b b' x' y')
  boundary : ∀ {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s],
    IsFramedBoundary A m hA i hX L s (O.e i hX L s)
  chern_normalization : ∀ (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L],
    (Ext.mk₀ (ordinaryFiniteIntegralGenerator A X)).comp
        ((Ext.homEquiv.symm (O.c1 X hX L)).mapExactFunctor
          (RawModuleScalarComparison.forget A X)) (zero_add 2) = chern A m hA X hX L
  boundary_forget : ∀ {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s],
    forgetSupport A m hA i 2 1 (O.e i hX L s) = O.c1 X hX L
  boundary_tensor : ∀ {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsUnit (m : Γ(X, ⊤))) (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} M]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s]
    (s' : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj M) [IsIso s'],
    O.e i hX (L ⊗ M) (tensorFrame i.openComplement L M s s') =
      O.e i hX L s + O.e i hX M s'
  boundary_dual : ∀ {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.dual L)]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s]
    (s' : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.dual L)) [IsIso s'],
    tensorFrame i.openComplement L (Scheme.Modules.dual L) s s' ≫
      (Scheme.Modules.pullback i.openComplement.ι).map (Scheme.Modules.dualEvaluation L) =
        𝟙 _ → O.e i hX (Scheme.Modules.dual L) s' = -O.e i hX L s

  boundary_enlarge : ∀ {Z Z' X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) (i' : Z' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i']
    (f : Z ⟶ Z') (hf : f ≫ i' = i) (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s]
    (s' : (Scheme.Modules.pullback i'.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i'.openComplement.ι).obj L) [IsIso s']
    (τ : (Scheme.Modules.etaleIsoTorsor L).sheaf.obj.obj
      (op (Scheme.Etale.mk i.openComplement.ι)))
    (τ' : (Scheme.Modules.etaleIsoTorsor L).sheaf.obj.obj
      (op (Scheme.Etale.mk i'.openComplement.ι)))
    (v : Scheme.Etale.mk i'.openComplement.ι ⟶ Scheme.Etale.mk i.openComplement.ι),
    Scheme.Modules.etaleIsoTorsorVal L τ = s →
    Scheme.Modules.etaleIsoTorsorVal L τ' = s' →
    (Scheme.Modules.etaleIsoTorsor L).sheaf.obj.map v.op τ = τ' →
    changeSupport A m hA i i' f hf 2 1 (O.e i hX L s) = O.e i' hX L s'
  cartier_positive : ∀ {D X : Scheme.{u}} [IsNoetherian X]
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hX : IsUnit (m : Γ(X, ⊤)))
    [SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.dual i.ker.toModules)]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.dual i.ker.toModules))
    [IsIso s] (hs : s = supportedDivisorSectionPullback i i.openComplement)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine X m A hA) 2),
    SupportedKummerBoundary A m hA i hI hX κ →
    O.e i hX (Scheme.Modules.dual i.ker.toModules) s = κ.hom
  cartier_ideal : ∀ {D X : Scheme.{u}} [IsNoetherian X]
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hX : IsUnit (m : Γ(X, ⊤)))
    [SheafOfModules.IsInvertible.{u, u, u} i.ker.toModules]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj i.ker.toModules) [IsIso s]
    (hs : s ≫ (Scheme.Modules.pullback i.openComplement.ι).map i.ker.toModulesι = 𝟙 _)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine X m A hA) 2),
    SupportedKummerBoundary A m hA i hI hX κ → O.e i hX i.ker.toModules s = -κ.hom
  gysin_restriction : ∀ {Z Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (k : Z ⟶ Y) (i : Y ⟶ X) [IsClosedImmersion k] [IsClosedImmersion i]
    (sq : IsPullback (𝟙 Z) k (k ≫ i) i)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((Scheme.Modules.pullback i).obj L)]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s]
    (a b : ℤ) (x : H A m hA k a b),
    PullsTo A m hA t (k ≫ i) k i (𝟙 Z) sq hX hY (a + 2) (b + 1)
      (gysin A m hA O k i hY hX L s a b x)
      (cupAbsolute A m hA O k hY a 2 b 1 x
        (O.c1 Y hY ((Scheme.Modules.pullback i).obj L)))
  gysin_forget : ∀ {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s]
    (a b : ℤ) (x : ordinaryFiniteUnit A X ⟶ (line A m hA X b)⟦a⟧),
    forgetSupport A m hA ((𝟙 Y) ≫ i) (a + 2) (b + 1)
        (gysin A m hA O (𝟙 Y) i hY hX L s a b
          (onIdentity A m hA Y a b (absolutePullback A m hA t i hX hY a b x))) =
      absoluteCup A m hA O X hX a 2 b 1 x (O.c1 X hX L)
  cartier_interchange : ∀ {Z D₁ D₂ X : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian D₁] [IsNoetherian D₂] [IsNoetherian X]
    (i : D₁ ⟶ X) (j : D₂ ⟶ X) (p : Z ⟶ D₁) (q : Z ⟶ D₂)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsClosedImmersion p] [IsClosedImmersion q] (sq : IsPullback q p j i)
    (hi : i.ker.IsInvertible) (hj : j.ker.IsInvertible)
    (hp : p.ker.IsInvertible) (hq : q.ker.IsInvertible)
    (hZ : IsUnit (m : Γ(Z, ⊤))) (h₁ : IsUnit (m : Γ(D₁, ⊤)))
    (h₂ : IsUnit (m : Γ(D₂, ⊤))) (hX : IsUnit (m : Γ(X, ⊤)))
    (κi : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D₁))
      (Scheme.finiteEtaleTateLine X m A hA) 2)
    (κj : Ext ((lowerStar (ModuleCat.{u + 1} A) j).obj (ordinaryFiniteConstant A D₂))
      (Scheme.finiteEtaleTateLine X m A hA) 2)
    (κp : Ext ((lowerStar (ModuleCat.{u + 1} A) p).obj (ordinaryFiniteConstant A Z))
      (Scheme.finiteEtaleTateLine D₁ m A hA) 2)
    (κq : Ext ((lowerStar (ModuleCat.{u + 1} A) q).obj (ordinaryFiniteConstant A Z))
      (Scheme.finiteEtaleTateLine D₂ m A hA) 2),
    SupportedKummerBoundary A m hA i hi hX κi →
    SupportedKummerBoundary A m hA j hj hX κj →
    SupportedKummerBoundary A m hA p hp h₁ κp →
    SupportedKummerBoundary A m hA q hq h₂ κq →
    ∀ (a b : ℤ) (x : H A m hA (𝟙 Z) a b),
    HEq (O.action p i h₁ hX (a + 2) 2 (b + 1) 1
      (relabel A m hA (Category.id_comp p) _ _
        (O.action (𝟙 Z) p hZ h₁ a 2 b 1 x (-κp.hom))) (-κi.hom))
      (O.action q j h₂ hX (a + 2) 2 (b + 1) 1
        (relabel A m hA (Category.id_comp q) _ _
          (O.action (𝟙 Z) q hZ h₂ a 2 b 1 x (-κq.hom))) (-κj.hom))

/-- The existing residue-coefficient restriction functor, named to display its derived map.
Source: ILO XVI 3.3 (blueprint: lem-per-noetherian-supported-product-calculus). -/
abbrev reductionFunctor (ell n N : ℕ) (hnN : n ≤ N) (X : Scheme.{u}) :=
  Sheaf.restrictScalars X.smallEtaleTopology (regularClassReduction ell n N hnN)

/-- The graph of coefficient reduction on signed supported morphisms. The source map
is closed pushforward of the constant residue map; the target map is the normalized
signed root-power comparison. Applying the exact restriction-of-scalars functor to the
B-valued morphism is equivalent by adjunction to derived extension of scalars A to B.
Source: ILO XVI 3.3; Stacks 06YU, 06YY
(blueprint: lem-per-noetherian-supported-product-calculus). -/
@[irreducible]
def ReducesTo (ell : ℕ) (hell : ell.Prime) (n N : ℕ) (hnN : n ≤ N)
    (d : RegularClassReductionData ell n N hnN
      (regularClassTransport ell hell N) (regularClassTransport ell hell n))
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hZ : IsUnit (ell : Γ(Z, ⊤))) (hX : IsUnit (ell : Γ(X, ⊤))) (a b : ℤ)
    (x : H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) i a b)
    (y : H (regularClassCoefficient ell n) (ell ^ n) (regularClassAnnihilator ell n) i a b) :
    Prop :=
  (DerivedCategory.singleFunctor _ 0).map
      ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficient ell N)) i).map
        ((d.val Z hZ).2 0)) ≫
      ((reductionFunctor ell n N hnN X).mapDerivedCategorySingleFunctor 0).inv.app
        (closedConstantModule (regularClassCoefficient ell n) i) ≫
      (reductionFunctor ell n N hnN X).mapDerivedCategory.map y ≫
      ((reductionFunctor ell n N hnN X).mapDerivedCategory.commShiftIso a).hom.app
        (line (regularClassCoefficient ell n) (ell ^ n) (regularClassAnnihilator ell n) X b) ≫
      (shiftFunctor _ a).map
        (((reductionFunctor ell n N hnN X).mapDerivedCategorySingleFunctor 0).hom.app
          (Scheme.finiteEtaleTateSheaf (regularClassCoefficient ell n) (ell ^ n) X
            (regularClassAnnihilator ell n) b)) =
    x ≫ (shiftFunctor _ a).map ((DerivedCategory.singleFunctor _ 0).map ((d.val X hX).2 b))

/-- The simultaneous finite-coefficient calculus and its reduction maps.
There is no flatness condition on coefficient reduction. The prime-power coefficient
rings and the root-power normalization are the already recorded constructions.
Source: ILO XVI 2.1--2.3, 3.3
(blueprint: lem-per-noetherian-supported-product-calculus). -/
structure Data (ell : ℕ) (hell : ell.Prime) where
  level : ∀ (n : ℕ), 0 < n → LevelData (regularClassCoefficient.{u} ell n)
    (ell ^ n) (regularClassAnnihilator ell n)
  laws : ∀ (n : ℕ) (hn : 0 < n), LevelLaws (regularClassCoefficient.{u} ell n)
    (ell ^ n) (regularClassAnnihilator ell n) (regularClassTransport ell hell n) (level n hn)
  coefficientData : ∀ (n N : ℕ), 0 < n → 0 < N → ∀ hnN : n ≤ N,
    RegularClassReductionData.{u} ell n N hnN
      (regularClassTransport ell hell N) (regularClassTransport ell hell n)
  reduce : ∀ (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (hnN : n ≤ N)
    {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : IsUnit (ell : Γ(Z, ⊤))) (hX : IsUnit (ell : Γ(X, ⊤))) (a b : ℤ),
    H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) i a b →+
      H (regularClassCoefficient ell n) (ell ^ n) (regularClassAnnihilator ell n) i a b
  reduce_normalization : ∀ (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (hnN : n ≤ N)
    {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : IsUnit (ell : Γ(Z, ⊤))) (hX : IsUnit (ell : Γ(X, ⊤))) (a b : ℤ)
    (x : H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) i a b),
    ReducesTo ell hell n N hnN (coefficientData n N hn hN hnN) i hZ hX a b x
      (reduce n N hn hN hnN i hZ hX a b x)
  cup_reduce : ∀ (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (hnN : n ≤ N)
    {Z D X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hZ : IsUnit (ell : Γ(Z, ⊤))) (hD : IsUnit (ell : Γ(D, ⊤)))
    (hI : IsUnit (ell : Γ(pullback i j, ⊤))) (hX : IsUnit (ell : Γ(X, ⊤)))
    (a a' b b' : ℤ)
    (x : H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) i a b)
    (y : H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) j a' b'),
    reduce n N hn hN hnN (intersectionSupport i j) hI hX (a + a') (b + b')
        ((level N hN).cup i j (regularClassExponentUnit ell N X hX) a a' b b' x y) =
      (level n hn).cup i j (regularClassExponentUnit ell n X hX) a a' b b'
        (reduce n N hn hN hnN i hZ hX a b x) (reduce n N hn hN hnN j hD hX a' b' y)
  action_reduce : ∀ (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (hnN : n ≤ N)
    {Z Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hZ : IsUnit (ell : Γ(Z, ⊤))) (hY : IsUnit (ell : Γ(Y, ⊤)))
    (hX : IsUnit (ell : Γ(X, ⊤))) (a a' b b' : ℤ)
    (x : H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) i a b)
    (y : H (regularClassCoefficient ell N) (ell ^ N) (regularClassAnnihilator ell N) j a' b'),
    reduce n N hn hN hnN (i ≫ j) hZ hX (a + a') (b + b')
        ((level N hN).action i j (regularClassExponentUnit ell N Y hY)
          (regularClassExponentUnit ell N X hX) a a' b b' x y) =
      (level n hn).action i j (regularClassExponentUnit ell n Y hY)
        (regularClassExponentUnit ell n X hX) a a' b b'
        (reduce n N hn hN hnN i hZ hY a b x) (reduce n N hn hN hnN j hY hX a' b' y)
  boundary_reduce : ∀ (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (hnN : n ≤ N)
    {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : IsUnit (ell : Γ(Z, ⊤))) (hX : IsUnit (ell : Γ(X, ⊤))) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : (Scheme.Modules.pullback i.openComplement.ι).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback i.openComplement.ι).obj L) [IsIso s],
    reduce n N hn hN hnN i hZ hX 2 1
        ((level N hN).e i (regularClassExponentUnit ell N X hX) L s) =
      (level n hn).e i (regularClassExponentUnit ell n X hX) L s

/-- Supported cup and nested action products, the relative Kummer identities and operators,
and transverse ideal-normalized Cartier interchange, simultaneously at every positive level.
Source: ILO, Expose XVI 2.1, Lemma 2.2.2.4, Proposition 2.2.3.2 and Theorem 2.3.2,
pp. 228--236 (blueprint: lem-per-noetherian-supported-product-calculus).

Proof plan from the DAG:

1. Put $P_C=(i_C)_*\Lambda_C$ and let $\rho_C:\Lambda_X\to P_C$ be constant restriction. The
open-closed short exact sequence, applied to $\Lambda_X$, identifies
$\operatorname{Hom}_X(P_C,M)$ with $\ker(\Gamma(X,M)\to\Gamma(X\setminus C,M))$: precompose with
$\rho_C$ and evaluate at $1$. Derive this identity on bounded-below injective resolutions. The
supported-Hom theorem and the support-restriction triangle (take its first support to be all of
$X$) give
$$H_C^a(X,\Lambda(b))=\operatorname{Hom}_{D(X_{\mathrm{et}},\Lambda)}(P_C,\Lambda_X(b)[a]).$$
These are the same identifications, since both are induced by the preceding underived kernel
identity. In particular forgetting support is precomposition with $\rho_C$, and restriction to a
closed subscheme is ordinary inverse image of the represented morphism with the closed-constant
exchange. All coefficient complexes here are bounded below, including every shifted line sheaf
used below.
Uses: lem-weil-pbc-open-closed-short-exact, lem-amb-closed-support-hom,
lem-pur-support-restriction-triangle, def-pur-etale-derived-supported-sections,
lem-pur-etale-closed-constant-tensor.

2. For $\alpha:P_C\to\Lambda(b)[a]$ and $\beta:P_D\to\Lambda(b')[a']$, define their product by
$$P_{C\cap D}\xrightarrow{\mu_{C,D}^{-1}}P_C\otimes^L
P_D\xrightarrow{\alpha\otimes\beta}\Lambda(b)[a]\otimes^L\Lambda(b')[a']
\xrightarrow{t_{a,a'}}\Lambda(b+b')[a+a'].$$
The closed-constant tensor lemma supplies the specified associative, symmetric multiplication
$\mu$, and the twist lemma supplies locally free rank-one coefficient lines. The multiplication
of signed powers is associative and symmetric: on any local basis it sends $e^b\otimes e^{b'}$
to $e^{b+b'}$, including negative powers by evaluation. Apply the source-system cup-calculus
lemma with labels the closed supports and meet their intersection. Its hypotheses are exactly
these flatness and coherence statements. It gives bilinearity, associativity and interchange
sign $(-1)^{aa'}$ for every integer degree and twist. Bilinearity factors the pairing through
the tensor product of the cohomology groups. No purity or regularity assertion is used.
Uses: lem-pur-etale-closed-constant-tensor, lem-asd-etale-finite-twist-pullback,
lem-pur-signed-line-scalar-tensor-tower, lem-pur-supported-source-system-cup-calculus.

3. For $k:Z\hookrightarrow Y$ and $i:Y\hookrightarrow X$, represent $u\in H_Z^a(Y,\Lambda(b))$
by $k_*\Lambda_Z\to\Lambda_Y(b)[a]$, and $v\in H_Y^{a'}(X,\Lambda(b'))$ by
$P_Y\to\Lambda_X(b')[a']$. Closed pushforward is exact: closed immersions are finite and finite
direct image is exact. Identify $i_*k_*\Lambda_Z=P_Z$ by composition of direct images. Let
$$p_{i,N,K}:i_*N\otimes^L K\longrightarrow i_*(N\otimes^Li^*K)$$ be the canonical projection
map, adjoint to the inverse-image tensor comparison followed by the ordinary adjunction counit.
For a shifted twist line $K$ it is an isomorphism: locally trivialize the line and use the
projection map's unit and shift laws. Its inverse identifies $i_*\Lambda_Y(b)[a]$ with
$P_Y(b)[a]$. Define $$u\cdot v=(-1)^{a a'}v(b)[a]\circ p_{i,\Lambda_Y,\Lambda_X(b)[a]}^{-1}\circ
i_*u.$$ The displayed sign is the Koszul comparison for composing homogeneous morphisms with the
fixed $t_{a,a'}$: moving the second degree past the first shift contributes $(-1)^{a a'}$. This
is the shifted tensor action, expressed as composition of supported morphisms; for every Cartier
factor its degree is two and this sign is $1$. This gives the nested action with support $Z$;
the same formula applies to every further closed support in $Y$. Its associativity is
composition associativity: for degrees $a,a',a''$ both signs are $(-1)^{a a'+a a''+a' a''}$, and
both parenthesizations are the successive pushed morphisms, with all line factors reassociated
by $(n\otimes l)\otimes l'\mapsto n\otimes(ll')$. The signed shift comparisons agree by the
shifted tensor-calculus lemma.
Uses: lem-weil-pbc-closed-immersion-finite, lemma-weil-pbc-finite-direct-image-exact,
lem-weil-pbc-inverse-image-composition, lem-weil-pbc-ringed-projection-mate-exact,
lem-asd-etale-finite-twist-pullback, lem-pur-shifted-tensor-morphism-calculus.

4. Projection for a class on $Y$ is the same composition formula with its first support all of
$Y$. Thus $(u\cup y)\cdot v=u\cdot(y\cdot v)$, with the indicated shifts, by the associativity
just checked. For an ambient class $x$, naturality of $p_{i,N,K}$ in $K$ says that tensoring by
$x$ before the projection map equals $i_*i^*x$ after it. This gives $(i^*x)\cdot v=x\cup v$,
including any smaller support in $Y$. This is the projection formula used here. Finally the
right adjoints $Ri^!$ and $Rk^!$ exist for closed immersions. With the homogeneous-composition
sign fixed in Step 3, a composite
$i_*k_*\Lambda_Z\xrightarrow{i_*u}i_*\Lambda_Y(b)[a]\xrightarrow{v(b)[a]}\Lambda_X(b+b')[a+a']$
transposes by applying first the $i_*\dashv Ri^!$ Hom bijection and then the $k_*\dashv Rk^!$
bijection. Their composite is exactly the Hom bijection for $(ik)_*\dashv Rk^!Ri^!$. Including
that same shift comparison, this is exceptional composition after adjunction. The line
comparison in this displayed composite is the one fixed in Step 3.
Uses: lem-weil-pbc-ringed-projection-mate-exact, lem-exc-closed-ambient,
def-weil-pbc-composite-adjunction.

5. Let $v:X'\to X$, and pull back every closed support scheme-theoretically. Inverse image on
constant-coefficient etale modules is exact. The particular closed-constant exchanges
$b_{v,C}:v^{-1}P_C\cong P_{C'}$ preserve $\rho$ and $\mu$, and the roots-of-unity comparisons
preserve line multiplication and evaluation. Consequently the exact-pullback clause of the
source-system cup-calculus lemma applies to Step 2. For Step 3 use finite exchange for each
closed immersion, on both the source and target of the pushed morphism. The projection map is
the mate of the tensor comparison and counit; replacing these by their inverse-image comparisons
gives the same mate, so the defining nested composite pulls back to the composite defining the
pulled-back action. More explicitly, before taking mates both maps are the tensor of the
pulled-back morphism with the identity followed by the pulled-back counit; the adjunction
bijection identifies them. Exchanges compose as constant restriction and inverse image do, so
these products preserve identities and compositions of pair maps. Open restriction is the case
that $v$ is open. No Cartier hypothesis is needed for this step.
Uses: prop-weil-pbc-inverse-image-modules-exact, lem-pur-etale-closed-constant-tensor,
lem-asd-etale-finite-twist-pullback, lem-pur-supported-source-system-cup-calculus,
lemma-weil-pbc-finite-exchange, lem-weil-pbc-ringed-projection-mate-exact.

6. For coefficient reduction $A=\mathbf Z/\ell^N\to B=\mathbf Z/\ell^n$, $N\geq n$, use the
derived change-of-rings functor $F=-\otimes_A^LB$, not underived tensor on arbitrary complexes.
The closed-source scalar comparison gives $F(P_C^A)\cong P_C^B$ without flatness of $B$ over
$A$. The map on lines is induced by $z\mapsto z^{\ell^{N-n}}$; etale locally a primitive root is
a basis and maps to a primitive-root basis at level $n$, so its scalar extension is an
isomorphism. The signed-power lemma extends this comparison to all weights, compatibly with
multiplication and evaluation. The ringed-topos tensor-pullback theorem, specialized to the
identity topos and $A\to B$, gives $F(K\otimes_A^LL)\cong FK\otimes_B^LFL$. Its compatibility
with our products is visible on flat K-flat models: $(p\otimes q)\otimes
s\mapsto(p\otimes1)\otimes(q\otimes s)$ respects multiplication, reassociation and the sign
$(-1)^{a'p}$ of the shift comparison. Thus applying $F$ to the defining tensor composite in Step
2 gives exactly the $B$ composite. The closed projection comparison and closed scalar-source
maps are induced by these same balanced formulas, so applying $F$ to the composite in Step 3
gives its $B$ counterpart as well. The natural scalar source map is fixed by the coefficient
unit, so forgetting support also commutes. This proves reduction compatibility without asserting
that reduction is exact on module sheaves.
Uses: lem-pur-derived-change-of-rings, lem-geo-cartier-coeff-extension,
lem-pur-signed-line-scalar-tensor-tower, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-pur-shifted-tensor-morphism-calculus, lem-weil-pbc-ringed-projection-mate-exact.

7. Let $U=X\setminus C$. The frame torsor of $(L,s)$ determines $[L,s]\in H^1(X,U;\mathbf G_m)$
by the relative torsor theorem. Apply the relative connecting map for the exact $\ell^n$-Kummer
sequence to define $e_C(L,s)$. The line-torsor correspondence sends tensor product to contracted
product. To see addition with the specified sections, form the product of two framed torsors, a
$\mathbf G_m\times\mathbf G_m$-torsor, and push it out by multiplication. Relative cohomology of
a finite product of coefficient sheaves is the product of relative cohomologies: take the
product of the two injective resolutions and their restriction cones. Projection naturality of
the relative torsor classification identifies its two coordinates with the given relative
classes; multiplication therefore sends them to their sum. The relative Kummer connecting map is
a group homomorphism, so $e_C(L\otimes M,s\otimes t)=e_C(L,s)+e_C(M,t)$. The evaluation pairing
identifies $(L\otimes L^\vee,s\otimes s^\vee)$ with the trivial framed line; its class is zero.
Hence $e_C(L^\vee,s^\vee)=-e_C(L,s)$. When supports differ, restrict both specified sections to
the complement of their union and apply the same argument there; forgetting the old support is
induced by that restriction of the cones.
Uses: lem-amb-relative-torsor-cohomology, lem-amb-kummer-any-base, lem-sc-line-bundle-torsor.

8. The relative torsor theorem makes these classes natural under pullback of the pair, and
identifies forgetting the specified section with the ordinary line-torsor class. Naturality of
its connecting maps therefore identifies the forgotten $e_C(L,s)$ with the ordinary Kummer
$c_1(L)$. Reduction from level $N$ to $n$ uses the commuting Kummer diagram: the map on roots is
$z\mapsto z^{\ell^{N-n}}$, the map on the middle $\mathbf G_m$ is the same power, and the map on
the right $\mathbf G_m$ is the identity. Indeed $(z^{\ell^{N-n}})^{\ell^n}=z^{\ell^N}$. Its
relative connecting square sends $e_C^{(N)}(L,s)$ to $e_C^{(n)}(L,s)$, under Step 6's
coefficient identification. For a Cartier $D$, the ordinary supported Kummer theorem identifies
$e_D(\mathcal O_X(D),1)$ with $c_{D,\Lambda}$. Since $\mathcal O_X(D)=\mathcal I_D^\vee$ with
dual off-divisor trivializations, Step 7 identifies $e_D(\mathcal I_D,1)$ with $-c_{D,\Lambda}$.
Pullback retains this Cartier interpretation whenever the inverse-image divisor is Cartier;
pullback of the framed line class itself always exists.
Uses: lem-amb-relative-torsor-cohomology, lem-amb-kummer-any-base,
lem-asd-ordinary-supported-kummer, def-pc-divisor-line-bundle.

9. Define $G_{L,s}(u)=u\cdot e_C(L,s)$ by Step 3 with $Y=C$. For $u\in H_W^a(C,\Lambda(b))$, its
represented source after closed pushforward is $P_W$; hence the same formula lands in
$H_W^{a+2}(X,\Lambda(b+1))$. This supplies the required extension for every closed $W\subset C$.
Pull back the defining morphism to $C$. Closed inverse image cancels its own direct image, and
Step 8 identifies the inverse image of $e_C(L,s)$ with $c_1(L|_C)$, because the pulled-back
support is all of $C$. Thus restriction of $G$ is multiplication by this class. For $x\in
H^a(X,\Lambda(b))$, Step 4 gives $G_{L,s}(x|_C)=x\cup e_C(L,s)$. Precomposition with $\rho_C$
forgets support by Step 1; the restriction/multiplication map defining $\mu$ carries the two
constant units to the constant unit on the intersection. Forgetting support therefore gives
$x\cup c_1(L)$, as asserted. The pullback and reduction compatibilities of $G$ follow by
substituting Step 8 into the defining action and applying Steps 5–6.
Uses: prop-openclosed-lowerstar-fully-faithful, lem-amb-relative-torsor-cohomology,
lem-pur-etale-closed-constant-tensor.

10. Write $i:D_1\hookrightarrow X$, $j:D_2\hookrightarrow X$ and $I=D_1\times_XD_2$, with
$k:I\hookrightarrow D_1$. Let $e_1,e_2$ be the ideal-normalized supported classes.
Transversality ensures that $I$ is Cartier in each $D_i$. Pullback of the local equation and its
ideal trivialization identifies $i^*e_2$ with $e(\mathcal I_{I/D_1},1)$ by Step 8 (and likewise
with the indices reversed). Apply naturality of the projection map of Step 3 to the morphism
$e_2:P_{D_2}\to\Lambda(1)[2]$: $$p_{i,\Lambda,\Lambda(1)[2]}(1\otimes
e_2)=i_*(i^*e_2)\,p_{i,\Lambda,P_{D_2}}.$$ The latter projection map is $\mu_{D_1,D_2}$ under
the closed-constant exchange: both are induced by restricting the two constant sections and
multiplying them on $I$. Their equality is an equality of degree-zero sheaf maps; the same
equality holds on their flat models. Compose the displayed square with $e_1(1)[2]$ and invert
the projection isomorphisms. The resulting identity is $$e_1\star e_2=e_1(1)[2]\circ
p_{i,\Lambda,\Lambda(1)[2]}^{-1}\circ i_*(i^*e_2):P_I\to\Lambda(2)[4].$$ Thus the two iterated
Cartier class morphisms are respectively $e_1\star e_2$ and $e_2\star e_1$. Step 2 makes them
equal, since $(-1)^{2\cdot2}=1$.
Uses: lem-weil-pbc-ringed-projection-mate-exact, lem-pur-etale-closed-constant-tensor,
lem-asd-ordinary-supported-kummer.

11. For an arbitrary $u\in H^a(I,\Lambda(b))$, push its represented morphism
$\Lambda_I\to\Lambda_I(b)[a]$ to $X$, obtaining $\widetilde u:P_I\to P_I(b)[a]$. By Step 3, the
two composites of the extended operators in the question are the two class morphisms in Step 10,
shifted and twisted by $(b)[a]$, each precomposed with the same $\widetilde u$. Their equality
in Step 10 therefore gives equality on every such $u$, in $H_I^{a+4}(X,\Lambda(b+2))$. This also
checks the common domain and codomain; no extension of $u$ to $D_1$, $D_2$, or $X$ is assumed.
All arguments used only exact closed-support functors, line twists, and the Cartier condition on
the two restrictions. In particular no regularity hypothesis on $X$ has entered.
Uses: .
-/
theorem noetherian_supported_product_calculus (ell : ℕ) (hell : ell.Prime) :
    Nonempty (Data.{u} ell hell) := by
  sorry

end AlgebraicGeometry.Etale.NoetherianSupportedProducts
