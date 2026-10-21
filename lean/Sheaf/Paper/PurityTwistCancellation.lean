/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.PurityCoprojection
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.TateTwistLocallyFree
public import Sheaf.Paper.CartesianCoefficientTwists
public import Sheaf.Paper.SupportedCup
public import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-! # Cancellation of Tate shifts in a specified purity composite

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
Step 2 (blueprint: lem-pur-twist-cancellation).

## Main definitions
- `purityCancellationLine`, `purityCancellationTate`: the signed finite Tate lines and shifts.
- `PurityCancellationComparisons`: the normalized structural identifications.
- `purityTwistCancellationComposite`: the specified four-arrow composite.

## Main statements
- `purity_twist_cancellation`: invertibility, untwisting, and degree-zero cohomology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Fixed-scalar coordinates for the actual unbounded pro-etale category.
Source: blueprint Step 2 (blueprint: lem-pur-twist-cancellation). -/
abbrev PurityCancellationCategory (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))

/-- The published signed root line, in fixed-scalar coordinates. The inverse is that
of the specified associated-module-sheaf equivalence, so no line is chosen.
Source: blueprint Step 2, T_S(r) (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationLine (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℤ) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI := (finiteCoefficientIntrinsicRealization_exact T P.Ring).1
  (finiteCoefficientIntrinsicRealization T P.Ring).asEquivalence.inverse.obj
    (WeilConjectures.coefficientTwistLine T
      (Scheme.tateFiniteLine T P.coefficients.l P.Coefficient (P.level - 1)
        (Scheme.finiteEtaleTwistScalar _ P.Coefficient
          (WeilConjectures.PurityConventions.defaultAnnihilator P))) r)

/-- T_S(r) = A_S(r)[2r], using the existing signed tensor/dual powers in degree zero.
Source: blueprint Step 2 (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationTate (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℤ) : PurityCancellationCategory P T :=
  ((DerivedCategory.singleFunctor _ 0).obj (purityCancellationLine P T r))⟦2 * r⟧

/-- The recorded derived tensor, with coefficient category fixed once.
Source: blueprint Step 2 (blueprint: lem-pur-twist-cancellation). -/
@[implicit_reducible]
def purityCancellationTensor (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) := derivedTensor (ModuleCat.{u + 1} P.Coefficient) T

/-- F_S(r)(K) = K tensor A_S(r)[2r], on objects and arrows.
Source: blueprint Step 2 (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationTwist (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℤ) :
    PurityCancellationCategory P T ⥤ PurityCancellationCategory P T :=
  (purityCancellationTensor P T).flip.obj (purityCancellationTate P T r)

/-- The coefficient sheaf in degree zero, in the same fixed-scalar coordinates.
Source: blueprint Step 2 (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) : PurityCancellationCategory P T :=
  (DerivedCategory.singleFunctor _ 0).obj (P.constant T)

/-- The published derived inverse image with its two coefficient categories explicit.
Source: blueprint Step 2, restriction of twists (blueprint: lem-pur-twist-cancellation). -/
@[implicit_reducible]
def purityCancellationPullback (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor

/-- The actual finite root line, before the fixed-scalar realization.
Source: blueprint Step 2, signed tensor calculation
(blueprint: lem-pur-twist-cancellation). -/
abbrev purityCancellationFiniteLine (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) :=
  Scheme.tateFiniteLine T P.coefficients.l P.Coefficient (P.level - 1)
    (Scheme.finiteEtaleTwistScalar _ P.Coefficient
      (WeilConjectures.PurityConventions.defaultAnnihilator P))

/-- The precise finite signed comparison used in `spFiniteTwists_cartesian`.
Its first-degree root normalization is retained separately below.
Source: blueprint Step 2, restriction of roots
(blueprint: lem-pur-twist-cancellation). -/
abbrev PurityCancellationFiniteComparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  SpSignedComparison i (Scheme.tateFiniteCoefficient X P.Coefficient)
    (Scheme.tateFiniteCoefficient Z P.Coefficient)
    (StrictTower.constantRingIso P.Coefficient i)
    (purityCancellationFiniteLine P X) (purityCancellationFiniteLine P Z)

/-- The specified associated-module-sheaf equivalence, with quotient finiteness supplied.
Source: blueprint Step 2, constant coefficient coordinates
(blueprint: lem-pur-twist-cancellation). -/
def purityCancellationRealization (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  Scheme.sfIntrinsicModuleEquivalence T P.Ring

/-- A fixed-scalar section in the actual signed line, using the sheafification unit
and the counit of the specified realization; no section identification is chosen.
Source: blueprint Step 2, local-generator normalization
(blueprint: lem-pur-twist-cancellation). -/
def purityCancellationSection (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℤ) (V : T.ProEt)
    (x : (purityCancellationLine P T r).obj.obj (op V)) :
    (WeilConjectures.coefficientTwistLine T (purityCancellationFiniteLine P T) r).val.obj
      (op V) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  ((purityCancellationRealization P T).counitIso.hom.app
    (WeilConjectures.coefficientTwistLine T (purityCancellationFiniteLine P T) r)).val.app
      (op V) (Scheme.sfIntrinsicRealizationUnit T P.Ring
        (purityCancellationLine P T r) (op V) x)

/-- A coherent signed basis on one trivializing object: zero is 1, positive powers
concatenate, and negative basis vectors evaluate to 1 on the positive basis vector.
These equations express precisely the signed-generator prescription of the source.
Source: blueprint Step 2, signed tensor calculation, substep 1
(blueprint: lem-pur-twist-cancellation). -/
structure PurityCancellationFrame (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (V : T.ProEt) where
  basis : ∀ r : ℤ, Module.Basis (Fin 1)
    ((Scheme.tateFiniteCoefficient T P.Coefficient).obj.obj (op V))
    ((WeilConjectures.coefficientTwistLine T (purityCancellationFiniteLine P T) r).val.obj
      (op V))
  zero : basis 0 0 =
    (1 : (Scheme.tateFiniteCoefficient T P.Coefficient).obj.obj (op V))
  positive : ∀ n : ℕ, basis (n + 2) 0 =
    SheafOfModules.siteSheafTensorTmul
      (WeilConjectures.coefficientTwistPower T (purityCancellationFiniteLine P T) (n + 1))
      (purityCancellationFiniteLine P T) (op V) (basis (n + 1) 0) (basis 1 0)
  negative : ∀ n : ℕ,
    ((basis (Int.negSucc n) 0).app (op (Over.mk (𝟙 V)))) (basis (n + 1) 0) =
      (1 : (Scheme.tateFiniteCoefficient T P.Coefficient).obj.obj (op V))

/-- The ordinary fixed-scalar pure tensor, using the canonical lax tensorator of
sheaf inclusion. Source: blueprint Step 2, local-generator calculation
(blueprint: lem-pur-twist-cancellation). -/
def purityCancellationTensorSection (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r s : ℤ) (V : T.ProEt)
    (x : (purityCancellationLine P T r).obj.obj (op V))
    (y : (purityCancellationLine P T s).obj.obj (op V)) :
    (purityCancellationLine P T r ⊗ purityCancellationLine P T s).obj.obj (op V) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))
      (purityCancellationLine P T r) (purityCancellationLine P T s)).app (op V)) (x ⊗ₜ y)

section SignedProduct

variable {C : Type v} [Category.{w} C] [Abelian C]
  [IsGrothendieckAbelian.{z} C] [HasDerivedCategory.{z} C]
  [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The canonical degree-zero tensor comparison followed by even shifts, with the
categorical instances shared before specialization.
Source: blueprint Step 2, signed tensor calculation, substep 1
(blueprint: lem-pur-twist-cancellation). -/
def purityCancellationSingleProduct
    [(DerivedCategory.Qh (C := C)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ))]
    (L M K : C) (μ : L ⊗ M ⟶ K) (r s : ℤ) :
    ((DerivedCategory.singleFunctor C 0).obj L)⟦2 * r⟧ ⊗
        ((DerivedCategory.singleFunctor C 0).obj M)⟦2 * s⟧ ⟶
      ((DerivedCategory.singleFunctor C 0).obj K)⟦2 * (r + s)⟧ :=
  (DerivedCategory.shiftTensorShiftIso C
    ((DerivedCategory.singleFunctor C 0).obj L)
    ((DerivedCategory.singleFunctor C 0).obj M) (2 * r) (2 * s)).hom ≫
  (shiftFunctor _ (2 * r + 2 * s)).map
    (cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map μ) ≫
  eqToHom (congrArg
    (fun d : ℤ ↦ ((DerivedCategory.singleFunctor C 0).obj K)⟦d⟧) (mul_add 2 r s).symm)


/-- A determining equation for the actual single/shift product above, stated before
specializing the coefficient category. Its heterogeneous form only avoids expensive
conversion of definitionally identical tensor presentations on the same scheme.
The right side is a constructed morphism, not another free comparison field.
Source: blueprint Step 2, signed tensor calculation, substep 1
(blueprint: lem-pur-twist-cancellation). -/
abbrev purityCancellationProductNormalized
    [(DerivedCategory.Qh (C := C)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ))]
    (L M K : C) (μ : L ⊗ M ⟶ K) (r s : ℤ) {α : Type z} (f : α) : Prop :=
  HEq f (purityCancellationSingleProduct L M K μ r s)

end SignedProduct

/-- Section-normalized signed contractions on a single scheme. The normalization is
an equation for the product map itself on every coherent local basis, and determines
it because those basis tensors locally generate. The derived isomorphism is pinned to
that actual degree-zero/even-shift transport by a determining equation. HEq only
bridges the two definitionally equal tensor presentations on this same scheme.
Source: blueprint Step 2, signed tensor calculation, substep 1
(blueprint: lem-pur-twist-cancellation). -/
structure PurityCancellationContractions
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) where
  line_add : ∀ r s : ℤ,
    purityCancellationLine P T r ⊗ purityCancellationLine P T s ≅
      purityCancellationLine P T (r + s)
  section_normalized : ∀ (r s : ℤ) (V : T.ProEt) (e : PurityCancellationFrame P T V)
    (x : (purityCancellationLine P T r).obj.obj (op V))
    (y : (purityCancellationLine P T s).obj.obj (op V)),
    purityCancellationSection P T r V x = e.basis r 0 →
    purityCancellationSection P T s V y = e.basis s 0 →
    purityCancellationSection P T (r + s) V
      ((line_add r s).hom.hom.app (op V) (purityCancellationTensorSection P T r s V x y)) =
        e.basis (r + s) 0
  derived : ∀ r s : ℤ,
    ((purityCancellationTensor P T).obj (purityCancellationTate P T r)).obj
      (purityCancellationTate P T s) ≅ purityCancellationTate P T (r + s)
  derived_normalized : ∀ r s : ℤ,
    purityCancellationProductNormalized (purityCancellationLine P T r)
      (purityCancellationLine P T s) (purityCancellationLine P T (r + s))
      (line_add r s).hom r s (derived r s).hom

/-- The canonical zero-line identification, using the realization counit and the
constant-generator-normalized unit comparison; then remove the zero shift.
Source: blueprint Step 2, T(0)=Lambda (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationZero (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) : purityCancellationTate P T 0 ≅ purityCancellationUnit P T :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  (shiftFunctorZero _ ℤ).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((purityCancellationRealization P T).inverse.mapIso
        (Scheme.proEtaleConstantModuleUnit T P.Ring).symm ≪≫
        (purityCancellationRealization P T).unitIso.symm.app
          (Scheme.proEtaleFixedConstantModule T P.Ring) ≪≫ (cupConstantIso P T).symm)

/-- The derived signed product, determined by the canonical single/shift map.
Source: blueprint Step 2, signed tensor calculation
(blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationContractions.product
    {P : WeilConjectures.PurityFiniteSetting.{u}} {T : Scheme.{u}}
    (D : PurityCancellationContractions P T) (r s : ℤ) :
    ((purityCancellationTensor P T).obj (purityCancellationTate P T r)).obj
      (purityCancellationTate P T s) ≅ purityCancellationTate P T (r + s) :=
  D.derived r s

/-- Cancel opposite powers on this scheme, by inverse signed product and the canonical
zero-line identification. Source: blueprint Step 2, first arrow
(blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationContractions.unit
    {P : WeilConjectures.PurityFiniteSetting.{u}} {T : Scheme.{u}}
    (D : PurityCancellationContractions P T) (m : ℕ) :
    purityCancellationUnit P T ≅
      ((purityCancellationTensor P T).obj (purityCancellationTate P T m)).obj
        (purityCancellationTate P T (-(m : ℤ))) :=
  (D.product m (-(m : ℤ)) ≪≫
    eqToIso (congrArg (purityCancellationTate P T) (add_neg_cancel (m : ℤ))) ≪≫
    purityCancellationZero P T).symm

/-- The sheaf pullback comparison with its determining equation: after the canonical
realization, its adjunct is exactly the adjunct of the signed finite comparison.
The two section maps use the specified equivalence's counit, so this condition leaves
no freedom to change the pullback map independently of the finite comparison.
Source: blueprint Step 2, substep 2 (blueprint: lem-pur-twist-cancellation). -/
structure PurityCancellationSheafPullback
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}} (i : Z ⟶ X)
    (B : PurityCancellationFiniteComparison P i) where
  signed : ∀ r : ℤ,
    (upperStar (ModuleCat.{u + 1} P.Coefficient) i).obj (purityCancellationLine P X r) ≅
      purityCancellationLine P Z r
  normalized : ∀ (r : ℤ) (V : X.ProEt)
    (x : (purityCancellationLine P X r).obj.obj (op V)),
    purityCancellationSection P Z r ((Scheme.proEtaleBaseChange i).obj V)
      ((((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i).homEquiv _ _)
        (signed r).hom).hom.app (op V) x) =
      (((Scheme.proEtaleRingModuleAdjunction i _ _ _).homEquiv _ _)
        (B.signed r).hom).val.app (op V) (purityCancellationSection P X r V x)

/-- Derive and shift the normalized sheaf comparison. This uses the exact inverse
image's canonical single comparison and its derived shift comparison, not a free
family of isomorphisms. Source: blueprint Step 2, substep 2
(blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationSheafPullback.transport
    {P : WeilConjectures.PurityFiniteSetting.{u}} {Z X : Scheme.{u}} {i : Z ⟶ X}
    {B : PurityCancellationFiniteComparison P i}
    (D : PurityCancellationSheafPullback P i B) (r : ℤ) :
    (purityCancellationPullback P i).obj (purityCancellationTate P X r) ≅
      purityCancellationTate P Z r :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient) i).app _ ≪≫
    (((upperStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory).commShiftIso
      (2 * r)).app _ ≪≫
    (shiftFunctor _ (2 * r)).mapIso
      (((upperStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategorySingleFunctor 0).app
          (purityCancellationLine P X r) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (D.signed r))

/-- Extract the specified co-projection for the two actual Tate shifts from its
published projection/counit characterization. That characterization determines
this isomorphism uniquely on the bounded constructible, etale-origin objects here.
Only proof witnesses are chosen before its unique normalized isomorphism.
Source: blueprint Step 2 and lem-pur-coprojection (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationCoprojection (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (N m : ℕ)
    (h : purityCoprojectionProperty P i aX
      (purityCancellationTate P X N) (purityCancellationTate P X (-(m : ℤ)))) :=
  h.choose_spec.choose_spec.choose

/-- The tensor identifications used to read the displayed four-arrow composite.
The co-projection is supplied by its published inverse projection/counit
characterization purityCoprojectionProperty. The coprojection_normalized field identifies
its explicit isomorphism with that characterization, using HEq only to avoid expensive
conversion between definitionally identical tensor presentations.
Unit cancellation on Z and signed addition on X are definitions from the two independent
section-normalized contraction records, through singles and even shifts. Pullback is
defined from the finite `SpSignedComparison`, whose first-degree root formula is retained,
by the section-normalized fixed-scalar sheaf comparison and then singles and shifts.
No such identification is an extra existence hypothesis in purity_twist_cancellation.
Source: blueprint Step 2, last arrow (blueprint: lem-pur-twist-cancellation). -/
structure PurityCancellationComparisons (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (N m c : ℕ) where
  contractionsX : PurityCancellationContractions P X
  contractionsZ : PurityCancellationContractions P Z
  dimension : (N : ℤ) + -(m : ℤ) = (c : ℤ)
  /-- Exactly the finite comparison type provided by `spFiniteTwists_cartesian`. -/
  pullbackComparison : PurityCancellationFiniteComparison P i
  /-- The first signed map has the root-tensor normalization in that theorem.
  Combined with its zero/positive/negative laws, this pins every signed map. -/
  root_normalized : ∀ (V : X.ProEt)
    (a : (Scheme.tateFiniteCoefficient X P.Coefficient).obj.obj (op V))
    (z : (Scheme.proEtaleRootsOfUnitySheaf X
      (P.coefficients.l ^ ((P.level - 1) + 1))).obj.obj (op V)),
    (((Scheme.proEtaleRingModuleAdjunction i _ _ _).homEquiv _ _)
      (pullbackComparison.signed 1).hom).val.app (op V)
        (Scheme.tateFiniteTensor X P.coefficients.l P.Coefficient (P.level - 1)
          (Scheme.finiteEtaleTwistScalar _ P.Coefficient
            (WeilConjectures.PurityConventions.defaultAnnihilator P)) V a z) =
      Scheme.tateFiniteTensor Z P.coefficients.l P.Coefficient (P.level - 1)
        (Scheme.finiteEtaleTwistScalar _ P.Coefficient
          (WeilConjectures.PurityConventions.defaultAnnihilator P))
        ((Scheme.proEtaleBaseChange i).obj V)
        ((Scheme.proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
          (CommRingCat.of P.Coefficient)).hom.app (op V) a)
        ((Scheme.proEtaleRootsOfUnityDirectImageMap i
          (P.coefficients.l ^ ((P.level - 1) + 1))).hom.app (op V) z)
  sheafPullback : PurityCancellationSheafPullback P i pullbackComparison
  coprojectionWitness : purityCoprojectionProperty P i aX
    (purityCancellationTate P X N) (purityCancellationTate P X (-(m : ℤ)))
  coprojection :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
      (((purityCancellationTensor P X).obj (purityCancellationTate P X N)).obj
        (purityCancellationTate P X (-(m : ℤ)))) ≅
    ((purityCancellationTensor P Z).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
        (purityCancellationTate P X N))).obj
      ((purityCancellationPullback P i).obj (purityCancellationTate P X (-(m : ℤ))))
  coprojection_normalized : HEq coprojection
    (purityCancellationCoprojection P i aX N m coprojectionWitness)

/-- Unit cancellation on Z, derived from its own normalized signed contraction.
Source: blueprint Step 2, first arrow (blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationComparisons.unitCancel
    {P : WeilConjectures.PurityFiniteSetting.{u}} {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {aX : X ⟶ Spec (.of P.field.k)}
    [LocallyOfFiniteType aX] [QuasiCompact aX] {N m c : ℕ}
    (D : PurityCancellationComparisons P i aX N m c) :=
  D.contractionsZ.unit m

/-- Signed addition on X, using the dimension equation only at the final target.
Source: blueprint Step 2, last arrow (blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationComparisons.addCancel
    {P : WeilConjectures.PurityFiniteSetting.{u}} {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {aX : X ⟶ Spec (.of P.field.k)}
    [LocallyOfFiniteType aX] [QuasiCompact aX] {N m c : ℕ}
    (D : PurityCancellationComparisons P i aX N m c) :=
  D.contractionsX.product N (-(m : ℤ)) ≪≫
    eqToIso (congrArg (purityCancellationTate P X) D.dimension)

/-- The derived family is defined from the section-normalized finite comparison.
Source: blueprint Step 2, substep 2 (blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationComparisons.pullbackTransport
    {P : WeilConjectures.PurityFiniteSetting.{u}} {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {aX : X ⟶ Spec (.of P.field.k)}
    [LocallyOfFiniteType aX] [QuasiCompact aX] {N m c : ℕ}
    (D : PurityCancellationComparisons P i aX N m c) (r : ℤ) :=
  D.sheafPullback.transport r

/-- The pullback arrow in Phi is the normalized family's value at -m.
Source: blueprint Step 2, last arrow (blueprint: lem-pur-twist-cancellation). -/
def PurityCancellationComparisons.pullback
    {P : WeilConjectures.PurityFiniteSetting.{u}} {Z X : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {aX : X ⟶ Spec (.of P.field.k)}
    [LocallyOfFiniteType aX] [QuasiCompact aX] {N m c : ℕ}
    (D : PurityCancellationComparisons P i aX N m c) :=
  D.pullbackTransport (-(m : ℤ))

/-- The displayed composite, parametrized by its actual tensor and inverse-image
functors to keep type checking independent of their constructions.
Source: blueprint Step 2 (blueprint: lem-pur-twist-cancellation). -/
def purityCancellationArrow {C D : Type (u + 2)} [Category.{u + 1} C]
    [Category.{u + 1} D] (TX : C ⥤ C ⥤ C) (TZ : D ⥤ D ⥤ D)
    (G Q : C ⥤ D) (U M L : D) (A B V omegaX : C) (omegaZ : D)
    (unit : U ≅ (TZ.obj M).obj L) (piX : omegaX ≅ A) (piZ : omegaZ ≅ M)
    (b : omegaZ ≅ G.obj omegaX) (pull : Q.obj B ≅ L)
    (cop : G.obj ((TX.obj A).obj B) ≅ (TZ.obj (G.obj A)).obj (Q.obj B))
    (add : (TX.obj A).obj B ≅ V) : U ⟶ G.obj V :=
  unit.hom ≫ (TZ.flip.obj L).map piZ.inv ≫ (TZ.flip.obj L).map b.hom ≫
    (TZ.flip.obj L).map (G.map piX.hom) ≫
    (TZ.obj (G.obj A)).map pull.inv ≫ cop.inv ≫ G.map add.hom

/-- The displayed Phi: unit cancellation, the three specified orientation arrows
under F_Z(-m), inverse co-projection, then signed addition. The pullback identification
only changes coordinates in the last arrow. All maps are explicit composites.
Source: blueprint Step 2 and pur9-rg-def-phi (blueprint: lem-pur-twist-cancellation). -/
def purityTwistCancellationComposite (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (N m c : ℕ)
    (D : PurityCancellationComparisons P i aX N m c)
    (omegaX : PurityCancellationCategory P X) (omegaZ : PurityCancellationCategory P Z)
    (piX : omegaX ≅ purityCancellationTate P X N)
    (piZ : omegaZ ≅ purityCancellationTate P Z m)
    (b : omegaZ ≅ (rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj omegaX) :
    purityCancellationUnit P Z ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
        (purityCancellationTate P X c) :=
  purityCancellationArrow (purityCancellationTensor P X) (purityCancellationTensor P Z)
    (rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i)
    (purityCancellationPullback P i)
    (purityCancellationUnit P Z) (purityCancellationTate P Z m)
    (purityCancellationTate P Z (-(m : ℤ)))
    (purityCancellationTate P X N) (purityCancellationTate P X (-(m : ℤ)))
    (purityCancellationTate P X c) omegaX omegaZ
    D.unitCancel piX piZ b D.pullback
    D.coprojection D.addCancel

/-- Cancellation in the specified purity composite, with both the untwisted and
cohomology-sheaf conclusions. Comparison existence is a conclusion, and invertibility
holds for every comparison package, including the canonical one; no normalization
of b or either orientation is imposed.
Source: blueprint main-20261015, sk-thm-regular.proof.md, Step 2
(blueprint: lem-pur-twist-cancellation).

Proof:
1. det-def-sp-tate-twist-locally-free trivializes the finite root line. On that cover
signed powers multiply by e^r tensor e^s to e^(r+s); changing e to ue changes both
sides by u^(r+s), so these identifications glue. Dual evaluation cancels opposite
powers, and shifts add. They preserve bounded constructibility and finite Tor amplitude.
2. det-prop-sfb-cartesian-coefficients-twists identifies the derived pullback of every
signed Tate shift with the same shift on Z, using restriction of roots and constants.
3. Apply F_Z(-m) to piZ inverse, b, and Ri! piX. All three arrows are isomorphisms.
4. lem-pur-coprojection with K=T_X(N), L=T_X(-m) supplies the normalized co-projection.
Its inverse followed by signed addition and N=m+c is the last arrow. This also
constructs a comparison package. Every factor of the displayed composite is invertible.
5. Apply lem-pur-coprojection with K=A_X and L=T_X(c). Tensor the inverse of the
resulting A_Z to Ri!A_X tensor T_Z(c) isomorphism with T_Z(-c), and contract opposite
powers, obtaining Ri!A_X isomorphic to T_Z(-c).
6. Apply each cohomology functor to Phi. Its source is A_Z in degree zero; hence the
target has zero cohomology outside degree zero, and H^0 is isomorphic to A_Z. -/
theorem purity_twist_cancellation (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of P.field.k))] [IsClosedImmersion i]
    (N m c : ℕ) (_hN : N = m + c)
    (omegaX : PurityCancellationCategory P X) (omegaZ : PurityCancellationCategory P Z)
    (_hX : purityCoprojectionConstructible P X omegaX)
    (_hZ : purityCoprojectionConstructible P Z omegaZ)
    (piX : omegaX ≅ purityCancellationTate P X N)
    (piZ : omegaZ ≅ purityCancellationTate P Z m)
    (b : omegaZ ≅ (rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj omegaX) :
    Nonempty (PurityCancellationComparisons P i (X ↘ Spec (.of P.field.k)) N m c) ∧
    (∀ D : PurityCancellationComparisons P i (X ↘ Spec (.of P.field.k)) N m c,
      IsIso (purityTwistCancellationComposite P i (X ↘ Spec (.of P.field.k))
        N m c D omegaX omegaZ piX piZ b)) ∧
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
      (purityCancellationUnit P X) ≅ purityCancellationTate P Z (-(c : ℤ))) ∧
    Nonempty ((DerivedCategory.homologyFunctor _ 0).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
        (purityCancellationTate P X c)) ≅ P.constant Z) ∧
    (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
        (purityCancellationTate P X c)))) := by
  sorry

end AlgebraicGeometry.ProEtale
