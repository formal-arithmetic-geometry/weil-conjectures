/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology

/-! # Root-normalized Tate pairs and native scalar Tate lines

Source: geometric-Frobenius normalization of the Tate datum, followed by the exact
heart encoding in sk-def-sf-weil-complexes.
(blueprint: lem-sf-condensed-tate-pair-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.NativeCondensedCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar k₀ ≠ ell)] (X : Scheme.{u}) [X.Over (Spec (.of k₀))]

/-- Ordinary pullback written in the closure-coefficient presentation of the Tate datum.
Source: the actual closure coefficient in def-pur-transport-concrete-coefficients.
(blueprint: def-sf-condensed-tate-pairs). -/
def tateCoordinateAction :
    (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (.of k₀)).geometricFiber) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (X ↘ Spec (.of k₀)).geometricFiber)) ⥤
    (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (.of k₀)).geometricFiber) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (X ↘ Spec (.of k₀)).geometricFiber)) :=
  CondensedRing.upperStar (PurityTransport.Coefficient.obj ell .closure)
    (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom

omit [Fact (ringChar k₀ ≠ ell)] in
/-- The closure-coefficient presentation is the native ordinary Frobenius pullback.
Source: def-pur-transport-concrete-coefficients, closure coefficient.
(blueprint: def-sf-condensed-tate-pairs).
Proof: use congruence for upperStar; its two ring presentations agree by definition. -/
theorem tateCoordinateAction_eq : tateCoordinateAction k₀ ell X = action k₀ ell X := by
  unfold tateCoordinateAction action
  congr 1

/-- The actual positive condensed Tate line with its root-normalized Frobenius map.
Source: def-pur-tate-datum, positive tensor powers.
(blueprint: def-sf-condensed-tate-pairs). -/
def tatePair
    (p : PurityTransport.LinePullCoordinates ell .closure
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom) (d : ℕ) :
    IsoAlgebra (action k₀ ell X) :=
  let L := PurityTransport.Coefficient.line ell .closure
    (X ↘ Spec (.of k₀)).geometricFiber d
  IsoAlgebra.mk (F := action k₀ ell X) L
    ((eqToIso (congrArg (fun F ↦ F.obj L) (tateCoordinateAction_eq k₀ ell X))).symm ≪≫
      p.power d)

/-- The root-normalized Tate pair shifted by twice its twist.
Source: smooth purity at the coefficient unit, with its cohomological shift.
(blueprint: def-sf-condensed-tate-pairs). -/
def tateDerivedPair
    (p : PurityTransport.LinePullCoordinates ell .closure
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom) (d : ℕ) :
    IsoAlgebra (action k₀ ell X).mapDerivedCategory :=
  (IsoAlgebra.mapOfNatIso
    ((action k₀ ell X).mapDerivedCategory.commShiftIso (2 * (d : ℤ)))).obj
      ((IsoAlgebra.mapOfNatIso
        ((action k₀ ell X).mapDerivedCategorySingleFunctor 0)).obj
          (tatePair k₀ ell X p d))

/-- The root-normalized positive Tate pair is the encoded native scalar constant.

Source: thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1, the
root-normalized Tate datum; sk-def-sf-weil-complexes, exact heart encoding;
def-wf-tate-twist, the cyclotomic normalization.
(blueprint: lem-sf-condensed-tate-pair-encoding).

Proof in words. Choose compatible primitive ell-power roots over the algebraic
closure. The associated projection-normalized basis identifies the integral Tate
module with the regular integral coefficient module. On each root projection,
geometric Frobenius acts by the cyclotomic character. These identities commute with
root transitions, hence determine the identity on the inverse limit. Extend the
basis and identity along the specified integral-to-closure coefficient map.
The normalization fields of p identify its first comparison with this scalar
extension and its d-th comparison with the monoidal d-th power, including the unit
comparison at d = 0. Thus the scalar is cyclotomicUnit to the d-th power.
The coefficient isomorphism defining NativeEncoding identifies the encoded native
unit with the same regular condensed module and intertwines the specified
pullbacks. It preserves scalar multiplication on the underlying abelian sheaves.
This gives an isomorphism of Frobenius pairs. No smoothness, exceptional functor,
cohomology, or nonempty/connected hypothesis is used.
-/
theorem condensed_tate_pair_encoding
    (p : PurityTransport.LinePullCoordinates ell .closure
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom) (d : ℕ) :
    Nonempty (tatePair k₀ ell X p d ≅
      (encode k₀ ell X).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ ell X
          (WeilSheaf.cyclotomicUnit k₀ ell ^ (d : ℤ))).obj
            (ProEtaleWeilSheaf.adicConstant k₀ ell X))) := by
  sorry

end WeilConjectures.NativeCondensedCohomology
