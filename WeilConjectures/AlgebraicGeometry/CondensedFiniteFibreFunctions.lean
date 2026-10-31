/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.LocalFrobeniusLargeCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-!
# Functions on a finite étale fibre with condensed coefficients

Source: blueprint latest, `sec-fourier-transform/sk-lem-as-properties/lem-fd-as-trace.proof.md`,
first paragraph (blueprint: lem-fd-condensed-finite-fibre-functions).

The auxiliary maps below are the actual coefficient-unit comparisons and counit projections.
The statement includes their universal property, scalar sections, functoriality, Frobenius and
idempotent images. No comparison map is supplied as unconstrained data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedFiniteFibre

/-- The coefficient unit, using the recorded pulled-back condensed ring.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev unit (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T)

/-- The canonical unit comparison, in the direction from the pullback to the unit.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def unitPullback (l : ℕ) [Fact l.Prime] {T U : Scheme.{u}} (a : T ⟶ U) :
    (upperStar (Profinite.padicAlgClRingObj l) a).obj (unit l U) ≅ unit l T :=
  (Functor.Monoidal.εIso (upperStar (Profinite.padicAlgClRingObj l) a)).symm

/-- Direct image of the coefficient unit.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev push (l : ℕ) [Fact l.Prime] {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  (lowerStar (Profinite.padicAlgClRingObj l) f).obj (unit l Y)

/-- The counit projection followed by the canonical coefficient-unit comparison.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
@[irreducible] def component (l : ℕ) [Fact l.Prime] {Y X P : Scheme.{u}} (f : Y ⟶ X)
    (x : P ⟶ X) (y : P ⟶ Y) (h : y ≫ f = x) :
    (upperStar (Profinite.padicAlgClRingObj l) x).obj (push l f) ⟶ unit l P :=
  stalkLowerStarProj (Profinite.padicAlgClRingObj l) h (unit l Y) ≫
    (unitPullback l y).hom

/-- The coefficient-unit exchange attached to a commutative square. For an isomorphism
square this is the induced Weil structure; for maps of covers it is pullback of functions.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def exchange (l : ℕ) [Fact l.Prime] {Y X Y' X' : Scheme.{u}}
    {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : Y' ⟶ Y} {b : X' ⟶ X}
    (sq : CommSq a f' f b) :
    (upperStar (Profinite.padicAlgClRingObj l) b).obj (push l f) ⟶ push l f' :=
  (lowerStarBaseChange (Profinite.padicAlgClRingObj l) sq).app (unit l Y) ≫
    (lowerStar (Profinite.padicAlgClRingObj l) f').map (unitPullback l a).hom

/-- The canonical scalar of an endomorphism of the unit at an algebraically closed point.
The inverse regular-endomorphism equivalence recovers its global section; the coefficient
section equivalence recovers the function, evaluated at the unique point.
Source: blueprint scalar-fibre clause (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def scalar (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (e : End (unit l (Spec (.of k)))) : PadicAlgCl l :=
  ((padicAlgClSectionRingEquiv l (Spec (.of k))).symm
    ((RingEquiv.ofBijective Mod.regularEndRingHom
      Mod.regularEndRingHom_bijective).symm e)).1 (IsLocalRing.closedPoint k)

/-- Scalar fibre coordinates are obtained by the actual counit projections, with sections
represented by maps from the regular module. This is the usual terminal-section convention.
Source: blueprint scalar-fibre clause (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def coordinates (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (x : Spec (.of k) ⟶ X)
    (v : unit l (Spec (.of k)) ⟶
      (upperStar (Profinite.padicAlgClRingObj l) x).obj (push l f)) :
    FibrePoints f x → PadicAlgCl l :=
  fun y ↦ scalar l (v ≫ component l f x y.1 y.2)

/-- Base change of a morphism to the datum's chosen algebraic closure. This uses exactly
`FiniteFieldDatum.geometricFiber`, rather than a second choice of algebraic closure.
Source: blueprint finite-cover setup (blueprint: lem-fd-condensed-finite-fibre-functions). -/
@[irreducible] def geometricMap (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (f₀ : Y₀ ⟶ X₀) :
    (D.geometricFiber Y₀).left ⟶ (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- The canonical Weil structure on the direct image of the coefficient unit, for a square of
isomorphisms: the base-change exchange followed by the direct image of the coefficient-unit
comparison. Its forward map is `exchange l sq`.
Source: blueprint finite-fibre paragraph, induced Weil structure
(blueprint: lem-fd-condensed-finite-fibre-functions). -/
def weil (l : ℕ) [Fact l.Prime] {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    [IsIso a] [IsIso b] (sq : CommSq a f f b) :
    (upperStar (Profinite.padicAlgClRingObj l) b).obj (push l f) ≅ push l f :=
  (asIso (lowerStarBaseChange (Profinite.padicAlgClRingObj l) sq)).app (unit l Y) ≪≫
    (lowerStar (Profinite.padicAlgClRingObj l) f).mapIso (unitPullback l a)

/-- The local return operator of the induced coefficient-unit Weil structure.
Source: blueprint local Frobenius clause (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def returnEnd (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k]
    {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    (sq : CommSq a f f b) (σ : Spec (.of k) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ b = σ ≫ x) :
    End ((upperStar (Profinite.padicAlgClRingObj l) x).obj (push l f)) :=
  (pointComparison (Profinite.padicAlgClRingObj l)
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) σ) b hx).hom.app
      (push l f) ≫
    (upperStar (Profinite.padicAlgClRingObj l) x).map (exchange l sq)

set_option maxHeartbeats 0 in
-- The kernel compares the exact pullback and monoidal unit instances under the field binders.
/-- The clauses of the canonical finite-fibre comparison, as one proposition-valued interface.
Source: blueprint latest `lem-fd-as-trace.proof.md`, first paragraph
(blueprint: lem-fd-condensed-finite-fibre-functions). -/
structure Comparison (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    (Y₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (f₀ : Y₀ ⟶ X₀) : Prop where
  finite (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    Finite (FibrePoints (geometricMap D f₀) x)
  fan (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    Nonempty (IsLimit (Fan.mk
      ((upperStar (Profinite.padicAlgClRingObj l) x).obj (push l (geometricMap D f₀)))
      (fun y : FibrePoints (geometricMap D f₀) x ↦
        component l (geometricMap D f₀) x y.1 y.2)))
  scalar_bijective (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    Function.Bijective (coordinates l (geometricMap D f₀) x)
  scalar_linear (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (c : End (unit l (Spec (.of D.k))))
      (v : unit l (Spec (.of D.k)) ⟶
        (upperStar (Profinite.padicAlgClRingObj l) x).obj (push l (geometricMap D f₀))) :
    coordinates l (geometricMap D f₀) x (c ≫ v) =
      fun y ↦ scalar l c * coordinates l (geometricMap D f₀) x v y
  scalar_add (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (v w : unit l (Spec (.of D.k)) ⟶
        (upperStar (Profinite.padicAlgClRingObj l) x).obj (push l (geometricMap D f₀))) :
    coordinates l (geometricMap D f₀) x (v + w) =
      coordinates l (geometricMap D f₀) x v + coordinates l (geometricMap D f₀) x w
  exchange_isIso (a : Aut (D.geometricFiber Y₀).left)
      (b : Aut (D.geometricFiber X₀).left)
      (sq : CommSq a.hom (geometricMap D f₀) (geometricMap D f₀) b.hom) :
    IsIso (exchange l sq)
  derived (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    Nonempty ((moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l) x).obj
        ((DerivedCategory.singleFunctor _ 0).obj (push l (geometricMap D f₀))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (∏ᶜ fun _ : FibrePoints (geometricMap D f₀) x ↦ unit l (Spec (.of D.k))))
  naturality {Y' X' : Scheme.{u}} {f' : Y' ⟶ X'}
      {a : Y' ⟶ (D.geometricFiber Y₀).left}
      {b : X' ⟶ (D.geometricFiber X₀).left}
      (sq : CommSq a f' (geometricMap D f₀) b)
      (x : Spec (.of D.k) ⟶ X') (y : Spec (.of D.k) ⟶ Y')
      (hy : y ≫ f' = x) (hxy : (y ≫ a) ≫ geometricMap D f₀ = x ≫ b) :
    (upperStarComp (Profinite.padicAlgClRingObj l) x b).hom.app
        (push l (geometricMap D f₀)) ≫
      (upperStar (Profinite.padicAlgClRingObj l) x).map (exchange l sq) ≫
      component l f' x y hy =
    component l (geometricMap D f₀) (x ≫ b) (y ≫ a) hxy
  semilinear (a : Aut (D.geometricFiber Y₀).left)
      (b : Aut (D.geometricFiber X₀).left)
      (sq : CommSq a.hom (geometricMap D f₀) (geometricMap D f₀) b.hom)
      (σ : Aut (Spec (.of D.k)))
      (x x' : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (hx : x ≫ b.hom = σ.hom ≫ x')
      (y y' : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
      (hy : y ≫ geometricMap D f₀ = x)
      (hy' : y' ≫ geometricMap D f₀ = x') (h : y ≫ a.hom = σ.hom ≫ y') :
    (pointComparison (Profinite.padicAlgClRingObj l)
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) σ.hom) b.hom hx).hom.app
        (push l (geometricMap D f₀)) ≫
      (upperStar (Profinite.padicAlgClRingObj l) x).map (exchange l sq) ≫
      component l (geometricMap D f₀) x y hy =
    component l (geometricMap D f₀) x' y' hy'
  image (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (e : End (push l (geometricMap D f₀))) (he : e ≫ e = e) :
    ∃ i : (upperStar (Profinite.padicAlgClRingObj l) x).obj (Limits.image e) ≅
        Limits.image ((upperStar (Profinite.padicAlgClRingObj l) x).map e),
      i.hom ≫ Limits.image.ι ((upperStar (Profinite.padicAlgClRingObj l) x).map e) =
        (upperStar (Profinite.padicAlgClRingObj l) x).map (Limits.image.ι e)
  image_scalar (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (e : End (push l (geometricMap D f₀))) (he : e ≫ e = e) :
    Set.range (fun v : unit l (Spec (.of D.k)) ⟶
        (upperStar (Profinite.padicAlgClRingObj l) x).obj (Limits.image e) ↦
      coordinates l (geometricMap D f₀) x
        (v ≫ (upperStar (Profinite.padicAlgClRingObj l) x).map (Limits.image.ι e))) =
    Set.range (fun v : unit l (Spec (.of D.k)) ⟶
        (upperStar (Profinite.padicAlgClRingObj l) x).obj (push l (geometricMap D f₀)) ↦
      coordinates l (geometricMap D f₀) x
        (v ≫ (upperStar (Profinite.padicAlgClRingObj l) x).map e))
  image_operator (a : Aut (D.geometricFiber Y₀).left)
      (b : Aut (D.geometricFiber X₀).left)
      (sq : CommSq a.hom (geometricMap D f₀) (geometricMap D f₀) b.hom)
      (σ : Spec (.of D.k) ⟶ Spec (.of D.k))
      (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (hx : x ≫ b.hom = σ ≫ x)
      (e : End (push l (geometricMap D f₀))) (he : e ≫ e = e)
      (hWeil : (upperStar (Profinite.padicAlgClRingObj l) b.hom).map e ≫ exchange l sq =
        exchange l sq ≫ e) :
    ∃! F : End ((upperStar (Profinite.padicAlgClRingObj l) x).obj (Limits.image e)),
      F ≫ (upperStar (Profinite.padicAlgClRingObj l) x).map (Limits.image.ι e) =
        (upperStar (Profinite.padicAlgClRingObj l) x).map (Limits.image.ι e) ≫
          returnEnd l sq σ x hx
  image_derived (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (e : End (push l (geometricMap D f₀))) (he : e ≫ e = e) :
    Nonempty ((moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l) x).obj
        ((DerivedCategory.singleFunctor _ 0).obj (Limits.image e)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Limits.image ((upperStar (Profinite.padicAlgClRingObj l) x).map e)))
  local_operator (n : ℕ)
      (sq : CommSq (D.geometricFrobenius Y₀).hom (geometricMap D f₀) (geometricMap D f₀)
        (D.geometricFrobenius X₀).hom)
      (sqn : CommSq (localPositivePower (D.geometricFrobenius Y₀).hom n)
        (geometricMap D f₀) (geometricMap D f₀)
        (localPositivePower (D.geometricFrobenius X₀).hom n))
      (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (hx : x ≫ localPositivePower (D.geometricFrobenius X₀).hom n =
        localPositivePower (frobeniusPointIso D).hom n ≫ x) :
    CondensedModule.operator l D (D.geometricFrobenius X₀).hom (push l (geometricMap D f₀))
        (weil l sq) x n hx =
      (pointSections l D.k).map
        (returnEnd l sqn (localPositivePower (frobeniusPointIso D).hom n) x hx)
  frobenius (n : ℕ) (z : D.extensionPoints X₀ (n + 1) (Nat.succ_pos n)) :
    ∃ (sq : CommSq (localPositivePower (D.geometricFrobenius Y₀).hom n)
        (geometricMap D f₀) (geometricMap D f₀)
        (localPositivePower (D.geometricFrobenius X₀).hom n))
      (π : FibrePoints (geometricMap D f₀)
          (localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z) ≃
        FibrePoints (geometricMap D f₀)
          (localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z)),
      (∀ y, localPositivePower (frobeniusPointIso D).hom n ≫ (π y).1 =
        y.1 ≫ localPositivePower (D.geometricFrobenius Y₀).hom n) ∧
      ∀ (hx : localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z ≫
            localPositivePower (D.geometricFrobenius X₀).hom n =
          localPositivePower (frobeniusPointIso D).hom n ≫
            localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z)
        (v : unit l (Spec (.of D.k)) ⟶
          (upperStar (Profinite.padicAlgClRingObj l)
            (localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z)).obj
              (push l (geometricMap D f₀))),
        coordinates l (geometricMap D f₀)
            (localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z)
            (v ≫ returnEnd l sq (localPositivePower (frobeniusPointIso D).hom n)
              (localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z) hx) =
          fun y ↦ coordinates l (geometricMap D f₀)
            (localExtensionPoint D X₀ (n + 1) (Nat.succ_pos n) z) v (π y)

/-- The canonical finite-fibre comparison with condensed Qbar_l coefficients.
Source: blueprint latest `lem-fd-as-trace.proof.md`, first paragraph
(blueprint: lem-fd-condensed-finite-fibre-functions).
Proof: the finite étale stalk fan has counit projections. Exact module pullback identifies
its degree-zero derived fibre, and terminal sections identify each unit with Qbar_l. Transpose
base-change mates and apply the adjunction triangle identities and unit coherence to obtain
the naturality equations, also after semilinear point transport. These give deck pullback.
Iterating the induced unit Weil structure, the recorded local operator of
def-weil-local-frobenius-trace is point sections of the single power-square exchange, by the
pasting law for base-change mates and the coherence of the unit comparisons. The rational point
return reindexes the fibre by arithmetic Frobenius; the coefficient-unit point comparison
fixes scalars. Exactness of
pullback and terminal sections preserves the split image of an idempotent and the local
operator restricts whenever it commutes with that idempotent. -/
theorem finite_fibre_functions (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Y₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (f₀ : Y₀ ⟶ X₀) [IsFinite f₀.left] [Etale f₀.left] :
    Comparison l D Y₀ X₀ f₀ := by
  sorry

end WeilConjectures.CondensedFiniteFibre
