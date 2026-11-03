/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.SmoothPurity.PurityBaseField
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Cup product with closed supports at every admissible coefficient

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-supported-cup.md and its
proof (blueprint: def-pur-supported-cup).

This module is an ADDITION: the finite-level `ProEtale.supportedCup` and
`PurityFiniteSetting.functorialCup` stay unchanged. Here the coefficient is a presentation
`c : PurityTransport.Coefficient ell`, the category is the internal-module category over
the pulled-back condensed ring `c.obj ell`, i.e. the abelian category under `c.derived ell X`,
and the twist lines are the constructed root-tower lines `c.line ell X r`.

Coefficient range (stack decision deliv/COEFF-DECISION.md). Every declaration holds for every
presentation `c : PurityTransport.Coefficient ell`, with no further hypothesis on `c`. This is
exactly the coefficient field `Setting.coefficient : Coefficient coefficients.l` of the current
def-pur-conventions Lean (`WeilConjectures.CurrentPurityConventions.Setting`): the finite
constructor accepts every finite commutative ell-primary ring A (any `ell ^ (n + 1) = 0`), and the
other constructors are Z_ell, Q_ell, O_E, E and Qbar_ell. The admissibility of the underlying ring
`ring ell c` in the sense of `CondensedRing.IsAdmissibleCoefficientFor` is
`PurityFiniteSetting.nativeChernAdmissible` (Sheaf.Paper.NativeChernClasses). No declaration of
the withdrawn model module of lem-pur-condensed-cartier-compact-exchange is used or imported.

The supported cohomology group is the Hom model of lem-pur-supported-hom
(`Admissible.supportedHom` identifies it with derived supported sections). The cup product
is the composite of the inverse coefficient identification theta, the tensor of the two
representatives and the right-shift-first comparison t_{a,b}, for arbitrary objects F, G
(`cup`, with F, G bounded below as in lem-pur-supported-hom), exactly the displayed composite
of the unit; it is the native-coefficient form of the general record `ProEtale.supportedCup`.
The twist-line version with multiplication of twist lines is only the helper `lineCup`.
The coefficient map is the unique map compatible with restriction of the unit; it is chosen
from an `∃!` statement only.

Base field (G1 over K, stack g1k RULES). Nothing in this module involves a base field: the only
inputs are the prime `ell`, the presentation `c`, closed immersions, and (for pullback) the
residue-field invertibility of `ell` as instance arguments. Over `K : PurityBaseField ell` these
instances are supplied by `K.residueInverse` (Sheaf.Paper.PurityBaseField), as in
`nativeChernPullback`. So the module is stated once; the k̄ case `K = P.geometricBase` uses the
same declarations, and no `…Over` version or `_geometric` comparison is needed.

## Main definitions

- `ring`, `source`, `sourceObject`, `target`, `H`: the coefficient ring and supported Hom model.
- `CoefficientSpec`, `coefficientMap`, `derivedCoefficientMap`: the restriction/multiplication
  map mu and its derived comparison.
- `lineMul`, `derivedLineMul`: multiplication of the positive Tate lines.
- `Plus`, `SupportedHom`: bounded-below objects and H^a_Z(X, F) = Hom(i_*Λ_Z, F[a]).
- `cupHom`, `cup`: the supported cup product θ⁻¹ ≫ (α ⊗ β) ≫ t_{a,b} for arbitrary F, G
  (`cup` is the node declaration, with F, G bounded below).
- `lineCup`: helper, the cup for F = Λ(r), G = Λ(s) followed by multiplication of twist lines.
- `supportMap`, `changeSupport`: extension of supports along an inclusion of closed supports.
- `linePull`, `targetPull`, `pullback`: pullback of supported classes along Cartesian squares.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.NativeSupportedCup

open AlgebraicGeometry.ProEtale.CondensedRing.Admissible

variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- The condensed coefficient ring of the presentation c, as a ring object.
Source: def-pur-conventions, admissible coefficients (blueprint: def-pur-supported-cup). -/
abbrev ring : Profinite.CondensedRing.{u} := Mon.mk (c.obj.{u} ell)

/-- The underived closed direct image of the regular coefficient module.
Source: def-pur-supported-cup, the factors i_*Λ_Z (blueprint: def-pur-supported-cup). -/
abbrev source {Z X : Scheme.{u}} (i : Z ⟶ X) : Modules (ring ell c) X :=
  CondensedRing.Admissible.source (ring ell c) i

/-- The supported source, placed in degree zero of `c.derived ell X`.
Source: lem-pur-supported-hom (blueprint: def-pur-supported-cup).
-/
abbrev sourceObject {Z X : Scheme.{u}} (i : Z ⟶ X) : c.derived ell X :=
  (DerivedCategory.singleFunctor _ 0).obj (source ell c i)

/-- The shifted positive Tate line Λ_X(r)[a].
Source: def-pur-conventions and sk-def-sp-tate-twist (blueprint: def-pur-supported-cup). -/
abbrev target (X : Scheme.{u}) (a : ℤ) (r : ℕ) : c.derived ell X :=
  ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X r))⟦a⟧

/-- Supported cohomology H^a_Z(X, Λ(r)) in the Hom model of lem-pur-supported-hom,
for an arbitrary integer degree. Source: lem-pur-supported-hom
(blueprint: def-pur-supported-cup). -/
abbrev H {Z X : Scheme.{u}} (i : Z ⟶ X) (a : ℤ) (r : ℕ) :=
  sourceObject ell c i ⟶ target ell c X a r

/-- The coefficient map mu restricts both unit factors to the intersection and multiplies,
i.e. it is compatible with the unit restrictions and the left unitor of the tensor unit.
Source: def-pur-supported-cup, proof step 2, the map mu_et (blueprint: def-pur-supported-cup). -/
def CoefficientSpec {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    (mu : source ell c i ⊗ source ell c j ⟶ source ell c (cupIntersection i j)) : Prop :=
  -- CHECK: `λ_ (unit ..)` has source `𝟙_ ⊗ unit`; this typechecks only if
  -- `Admissible.unit Λ X = Mod.regular _` is defeq to the monoidal unit `𝟙_` of `Modules Λ X`
  -- (the reference `Admissible.unitPull` relies on the same identification).
  (unitRestriction (ring ell c) i ⊗ₘ unitRestriction (ring ell c) j) ≫ mu =
    (λ_ (unit (ring ell c) X)).hom ≫ unitRestriction (ring ell c) (cupIntersection i j)

/-- The coefficient map is uniquely determined by its restriction normalization.
Source: def-pur-supported-cup, proof steps 2--3 (blueprint: def-pur-supported-cup).
Proof: as `cupCoefficientMap_existsUnique`. Each unit restriction is the cokernel of
j_!Λ_U → Λ_X (`Admissible.coefficientSequence_exact`), hence epi; the relative tensor
is a left adjoint in each variable, so the tensor of the two restrictions is epi, which
gives uniqueness. Existence: factor the restrictions through the intersection using
`lowerStarComp`, apply the lax monoidal comparison of the closed direct image and
the multiplication of the regular module there. -/
theorem coefficientMap_existsUnique {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃! mu : source ell c i ⊗ source ell c j ⟶ source ell c (cupIntersection i j),
      CoefficientSpec ell c i j mu := by
  sorry

/-- The specified underived coefficient map mu. Chosen from an `∃!` statement.
Source: def-pur-supported-cup, displayed coefficient identification
(blueprint: def-pur-supported-cup).
-/
def coefficientMap {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    source ell c i ⊗ source ell c j ⟶ source ell c (cupIntersection i j) :=
  (coefficientMap_existsUnique ell c i j).choose

/-- The underived coefficient map is invertible.
Source: def-pur-supported-cup, proof steps 2--3 (blueprint: def-pur-supported-cup).
Proof (node steps 2--3): step 2, on the finite etale realization the restriction-multiplication
map mu_et : i_*Λ_Z ⊗ j_*Λ_W → h_*Λ is an isomorphism by lem-pur-etale-closed-constant-tensor
(at a geometric point the factors are 0 or Λ and mu is Λ ⊗_Λ Λ ≅ Λ exactly on the
intersection). Step 3, closed immersions are proper, hence quasi-compact and quasi-separated
(lem-weil-pbc-closed-immersion-proper, lem-pc-separated-quasi-separated), so
sk-thm-pe-direct-image-comparison identifies ν_X^*(c_{et,*}Λ_C) with c_{proet,*}Λ_C for
c = i, j, h, compatibly with units; the exact comparison inverse image commutes with tensor
(lem-weil-pbc-ringed-topoi-derived-tensor-pullback) and carries mu_et to this map, which is
fixed by `CoefficientSpec`. -/
theorem coefficientMap_isIso {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (coefficientMap ell c i j) := by
  sorry

/-- The closed coefficient module is flat for the relative tensor product.
Source: def-pur-supported-cup, proof steps 2--3 (blueprint: def-pur-supported-cup).
Proof (node steps 2--3): on the finite etale realization i_*Λ_Z is flat by
lem-pur-etale-closed-constant-tensor (stalks 0 or Λ). By step 3 the pro-etale module is
ν_X^* of it (sk-thm-pe-direct-image-comparison, i proper hence qcqs), and the exact comparison
inverse image preserves flatness (lem-exc-constant-inverse-image-flat). -/
theorem source_flat {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ObjectProperty.flat (source ell c i) := by
  sorry

/-- The derived coefficient comparison: the canonical degree-zero tensor comparison
followed by mu. Source: def-pur-supported-cup, theta induced by mu
(blueprint: def-pur-supported-cup). -/
def derivedCoefficientMap {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    sourceObject ell c i ⊗ sourceObject ell c j ⟶ sourceObject ell c (cupIntersection i j) :=
  cupDerivedCoefficientMap (coefficientMap ell c i j)

/-- The derived coefficient comparison is invertible.
Source: def-pur-supported-cup, K-flat tensor descent (blueprint: def-pur-supported-cup).
Proof: `source_flat` makes the degree-zero complex K-flat, so the localization tensor
comparison is invertible (`DerivedCategory.isIso_μ_Qh_of_kFlat`); then
`coefficientMap_isIso`, exactly as `cupDerivedCoefficientMap_isIso`. -/
theorem derivedCoefficientMap_isIso {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (derivedCoefficientMap ell c i j) := by
  sorry

/-- Multiplication of positive Tate lines, built from the recursive definition
line (s+1) = line s ⊗ line 1 by unitors and associators only.
Source: def-coefficient-twists-detailed, tensor powers (blueprint: def-pur-supported-cup). -/
def lineMul (X : Scheme.{u}) (r : ℕ) : (s : ℕ) →
    c.line ell X r ⊗ c.line ell X s ≅ c.line ell X (r + s)
  | 0 => ρ_ (c.line ell X r)
  | s + 1 => (α_ (c.line ell X r) (c.line ell X s) (c.firstLine ell X)).symm ≪≫
      whiskerRightIso (lineMul X r s) (c.firstLine ell X)

/-- The degree-zero tensor comparison followed by line multiplication.
Source: def-pur-supported-cup, the product of coefficient twists
(blueprint: def-pur-supported-cup).
-/
def derivedLineMul (X : Scheme.{u}) (r s : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj (c.line ell X r) ⊗
        (DerivedCategory.singleFunctor _ 0).obj (c.line ell X s) ⟶
      (DerivedCategory.singleFunctor (Modules (ring ell c) X) 0).obj (c.line ell X (r + s)) :=
  cupSingleTensorMap (c.line ell X r) (c.line ell X s) ≫
    (DerivedCategory.singleFunctor _ 0).map (lineMul ell c X r s).hom

/-- The bounded-below derived category of Λ_X-modules, the inputs of lem-pur-supported-hom.
Source: lem-pur-supported-hom, bounded-below complexes (blueprint: def-pur-supported-cup). -/
abbrev Plus (X : Scheme.{u}) := DerivedCategory.Plus (Modules (ring ell c) X)

/-- Supported cohomology H^a_Z(X, F) of an arbitrary object F in the Hom model of
lem-pur-supported-hom: morphisms i_*Λ_Z → F[a]. Source: lem-pur-supported-hom
(blueprint: def-pur-supported-cup). -/
abbrev SupportedHom {Z X : Scheme.{u}} (i : Z ⟶ X) (F : c.derived ell X) (a : ℤ) :=
  sourceObject ell c i ⟶ F⟦a⟧

/-- The displayed composite of def-pur-supported-cup for arbitrary objects F, G:
θ⁻¹ : h_*Λ ≅ i_*Λ_Z ⊗^L j_*Λ_W, then α ⊗ β, then t_{a,b} : F[a] ⊗ G[b] ≅ (F ⊗^L G)[a+b]
(`cupComposite`). Source: def-pur-supported-cup, displayed composite; proof step 4
(blueprint: def-pur-supported-cup). -/
def cupHom {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (F G : c.derived ell X) (a b : ℤ)
    (α : SupportedHom ell c i F a) (β : SupportedHom ell c j G b) :
    SupportedHom ell c (cupIntersection i j) (F ⊗ G) (a + b) :=
  -- The shift-commutation families are supplied explicitly: instance search for these
  -- ∀-families on D(Mod_{Λ_X}) times out (see `CondensedRing.commShiftTensorLeftFamily`).
  letI : ∀ K : c.derived ell X, ((curriedTensor (c.derived ell X)).obj K).CommShift ℤ :=
    fun K ↦ DerivedCategory.commShiftTensorLeft _ K
  letI : ∀ K : c.derived ell X, ((curriedTensor (c.derived ell X)).flip.obj K).CommShift ℤ :=
    fun K ↦ DerivedCategory.commShiftTensorRight _ K
  cupComposite (derivedCoefficientMap ell c i j) (derivedCoefficientMap_isIso ell c i j)
    a b α β

/-- The supported cup product at the coefficient c, for bounded-below F, G (the classes of
lem-pur-supported-hom): α ∈ H^a_Z(X, F), β ∈ H^b_W(X, G) give
θ⁻¹ ≫ (α ⊗ β) ≫ t_{a,b} ∈ H^{a+b}_{Z∩W}(X, F ⊗^L G). This is the node declaration; it is
the native-coefficient form of the general record `ProEtale.supportedCup` (F G : CupPlus).
Source: latest blueprint def-pur-supported-cup, displayed composite
(blueprint: def-pur-supported-cup). -/
def cup {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (F G : Plus ell c X) (a b : ℤ)
    (α : SupportedHom ell c i F.obj a) (β : SupportedHom ell c j G.obj b) :
    SupportedHom ell c (cupIntersection i j) (F.obj ⊗ G.obj) (a + b) :=
  cupHom ell c i j F.obj G.obj a b α β

/-- Helper, not the node declaration: the cup of twist-line classes α ∈ H^a_Z(X, Λ(r)),
β ∈ H^b_W(X, Λ(s)), i.e. `cupHom` at F = Λ(r), G = Λ(s), followed by multiplication of the
twist lines Λ(r) ⊗ Λ(s) → Λ(r+s) (`derivedLineMul`). Used by the localized top Chern class.
Source: def-pur-supported-cup with F, G Tate lines, and def-coefficient-twists-detailed
(blueprint: def-pur-supported-cup). -/
def lineCup {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (a b : ℤ) (r s : ℕ)
    (α : H ell c i a r) (β : H ell c j b s) :
    H ell c (cupIntersection i j) (a + b) (r + s) :=
  cupHom ell c i j _ _ a b α β ≫ (derivedLineMul ell c X r s)⟦a + b⟧'

/-- Restriction of supported coefficients along an inclusion d of closed supports.
Source: def-pur-supported-class-operations, extension of supports; the support
restriction of lem-pur-divisor-class(c) (blueprint: def-pur-supported-cup). -/
def supportMap {V Z X : Scheme.{u}} (h : V ⟶ X) (k : Z ⟶ X) (d : Z ⟶ V) (hd : d ≫ h = k) :
    sourceObject ell c h ⟶ sourceObject ell c k :=
  (DerivedCategory.singleFunctor _ 0).map (supportRestriction (ring ell c) k h d hd)

/-- Extension of supports: a class supported on Z becomes a class supported on V.
Source: def-pur-supported-class-operations (blueprint: def-pur-supported-cup).
-/
def changeSupport {V Z X : Scheme.{u}} (h : V ⟶ X) (k : Z ⟶ X) (d : Z ⟶ V) (hd : d ≫ h = k)
    (a : ℤ) (r : ℕ) (α : H ell c k a r) : H ell c h a r :=
  supportMap ell c h k d hd ≫ α

/-- One tensor step of the pullback of a tensor power along a monoidal functor `F`:
the inverse monoidal comparison of `F` on `A ⊗ B`, then the given comparisons `e` and `g`.
The objects `L`, `L'` and the functor `G` of `g` are identified with `A ⊗ B`, `A' ⊗ B'`
and `F` by equalities, so that at use sites the kernel compares these objects and functors
directly and never conversions underneath `Functor.obj` (perf guide, pattern A).
Source: sk-prop-sfb-cartesian-coefficients, monoidal structure of inverse image
(blueprint: def-pur-supported-cup). -/
def monoidalPullStep {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {G : C ⥤ D} {A B L : C} {A' B' L' : D}
    (e : F.obj A ≅ A') (g : G.obj B ≅ B') (hG : G = F)
    (hL : L = A ⊗ B) (hL' : A' ⊗ B' = L') : F.obj L ≅ L' :=
  F.mapIso (eqToIso hL) ≪≫ (Functor.Monoidal.μIso F A B).symm ≪≫
    tensorIso e (eqToIso (congrArg (fun H : C ⥤ D => H.obj B) hG.symm) ≪≫ g) ≪≫
      eqToIso hL'

/-- The degree-zero case of `linePull`: the unit comparison of inverse image.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: def-pur-supported-cup). -/
def linePullZero {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y Nat.zero) ≅
      c.line ell X Nat.zero :=
  (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) f)).symm

/-- The successor step of `linePull`: the monoidal comparison of inverse image on
line r ⊗ line 1, the given comparison `e` in degree r, and the degree-one comparison
`extendedLinePull`. Split off from `linePull` so that the kernel checks the recursion
against this name only.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: def-pur-supported-cup). -/
def linePullSucc {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (r : ℕ)
    (e : (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y r) ≅ c.line ell X r) :
    (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y r.succ) ≅
      c.line ell X r.succ :=
  monoidalPullStep (CondensedRing.upperStar (c.obj ell) f) e
    (extendedLinePull ell (ring ell c) (Mon.Hom.mk (c.integralMap ell)) f)
    (by rfl) (by rfl) (by rfl)

/-- Pullback of the positive Tate lines: the generator-normalized comparison in degree one,
and the monoidal structure of inverse image on tensor powers.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: def-pur-supported-cup). -/
def linePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] : (r : ℕ) →
    (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y r) ≅ c.line ell X r :=
  fun r => Nat.rec
    (motive := fun r =>
      (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y r) ≅ c.line ell X r)
    (linePullZero ell c f) (fun r e => linePullSucc ell c f r e) r

/-- Derived pullback of the shifted Tate line, by the shift commutation of the left
derived inverse image, its single-complex comparison, and `linePull`.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: def-pur-supported-cup). -/
def targetPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (a : ℤ) (r : ℕ) :
    (CondensedRing.moduleObjectDerivedPullback (c.obj ell) f).obj (target ell c Y a r) ≅
      target ell c X a r :=
  (Functor.commShiftIso (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor
    (self :=
      (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) f).leftAdjointCommShift ℤ)
      a).app _ ≪≫
    (shiftFunctor _ a).mapIso
      (((CondensedRing.upperStar (c.obj ell) f).singleFunctorCompLeftDerivedFunctorIso).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (linePull ell c f r))

/-- For a Cartesian square of a closed immersion the closed-source pullback is invertible.
Source: closed base change, det-sf-open-closed-sequence-ring-sheaf(4)
(blueprint: def-pur-supported-cup).
Proof: the closed base-change map `lowerStarBaseChange` is an isomorphism for closed
immersions (proper base change in degree zero, exact closed direct image); inverse image
is exact, so the derived comparison factors are isomorphisms. -/
theorem closedSourcePull_isIso {D X D' X' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
    {d : D' ⟶ D} {g : X' ⟶ X} [IsClosedImmersion i] (sq : IsPullback d i' i g) :
    IsIso (closedSourcePull (ring ell c) sq.toCommSq) := by
  sorry

/-- Pullback of a supported class along a Cartesian square.
Source: def-pur-supported-class-operations, pullback (blueprint: def-pur-supported-cup). -/
def pullback {D X D' X' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
    {d : D' ⟶ D} {g : X' ⟶ X} [IsClosedImmersion i] (sq : IsPullback d i' i g)
    [∀ x : X', Invertible (ell : X'.residueField x)]
    [∀ y : X, Invertible (ell : X.residueField y)] (a : ℤ) (r : ℕ)
    (α : H ell c i a r) : H ell c i' a r :=
  letI := closedSourcePull_isIso ell c sq
  inv (closedSourcePull (ring ell c) sq.toCommSq) ≫
    (CondensedRing.moduleObjectDerivedPullback (c.obj ell) g).map α ≫ (targetPull ell c g a r).hom

end AlgebraicGeometry.ProEtale.NativeSupportedCup
