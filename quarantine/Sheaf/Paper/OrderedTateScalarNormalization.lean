/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.AlgebraicGeometry.AffineTraceTower
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.FiniteTateScalarSourceNormalization
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Paper.CochainPullbackTensorShift

/-! # Ordered Tate right comparisons and canonical scalar extension

Source: main-20261015 blueprint, sk-lem-sp-reduction-exceptional.proof.md,
Charts, iterated projective-line integration, retained affine-counit Step 4
(blueprint: lem-sp-ordered-tate-scalar-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale


attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

set_option backward.isDefEq.respectTransparency true


/-- The direct scalar comparison of an ordered Tate power, using the uniquely
specified generator balancing from the published scalar/single normalization theorem.
Source: Stacks 03EK, 07A4; blueprint Charts, ordered Tate normalization
(blueprint: lem-sp-ordered-tate-scalar-normalization). -/
@[irreducible]
def orderedTateScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf A N T hA (d : ℤ))) ≅
    (_root_.DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf B N T hB (d : ℤ)) :=
  let hstalk : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦
    (map_natCast (T.presheaf.germ ⊤ x (by trivial)).hom N) ▸
      hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  let normalization :=
    WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization
      φ N hN hA hB T hstalk
  @asIso _ _ _ _
    (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
      (Scheme.finiteEtaleTateTwist T N A hA d))
    (normalization.1 _
      ((ObjectProperty.flat_iff_preservesFiniteLimits _).2
        (Scheme.finite_etale_torsion_twist_line T N hN hstalk A hA d).2.2.1).2).2 ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (normalization.2.exists.choose d)

/-- The direct scalar/pullback/Tate/shift comparison, normalized to identity at zero.
The construction never passes through the affine-line adjunction tower.
Source: Stacks 07A4, 0D6D, 0FNH; blueprint Charts, direct comparison a_d
(blueprint: lem-sp-ordered-tate-scalar-normalization). -/
@[irreducible]
def orderedAffineDirectScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (K : DerivedCategoryModule A S) :
    (scalarExtension φ (affineTraceTower S d)).obj
      ((orderedAffineRight A N hA S d).obj K) ≅
    (orderedAffineRight B N hB S d).obj ((scalarExtension φ S).obj K) :=
  Nat.casesOn (motive := fun r ↦
    (scalarExtension φ (affineTraceTower S r)).obj
      ((orderedAffineRight A N hA S r).obj K) ≅
    (orderedAffineRight B N hB S r).obj ((scalarExtension φ S).obj K)) d
    (Iso.refl _) (fun d ↦
    (FiniteSmoothPurity.scalarShiftIso φ (affineTraceTower S (d + 1))
      (2 * ((d + 1 : ℕ) : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ))).mapIso
      ((ExceptionalCoefficients.tensorIso φ (affineTraceTower S (d + 1))).app
        ((ordinaryFinitePullback A (affineTraceProjection S (d + 1))).obj K,
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateSheaf A N (affineTraceTower S (d + 1)) hA
              ((d + 1 : ℕ) : ℤ))) ≪≫
      (Functor.uncurry.obj (ordinaryFiniteTensor B (affineTraceTower S (d + 1)))).mapIso
        (Iso.prod ((scalarPullbackIso φ (affineTraceProjection S (d + 1))).symm.app K)
          (orderedTateScalarIso φ N hN hA hB (affineTraceTower S (d + 1))
            (affineTraceInvertible N S hS (d + 1)) (d + 1)))))


/-- The specified ordered affine right comparison equals the direct scalar comparison
under the specified ordered normal forms, as actual derived-category morphisms.
Source: main-20261015 blueprint, sk-lem-sp-reduction-exceptional.proof.md, Charts,
iterated projective-line integration; retained affine-counit proof Step 4
(blueprint: lem-sp-ordered-tate-scalar-normalization).

Proof:
1. Choose a common flat-term K-flat resolution of K by lem-pc-kflat-resolution.
   Ringed pullback preserves it by lem-weil-pbc-ringed-pullback-preserves-kflat,
   including scalar pullback for a nonflat coefficient map. The flat finite Tate
   lines and lem-pur-kflat-total-tensor-model keep all the displayed tensors K-flat.
   Thus lem-pur-derived-change-of-rings and the canonical ringed tensor comparison
   compute every named map on these representatives, without resolving B boundedly.
2. The balanced root map sends (t tensor a) tensor b to t tensor phi(a)b; its
   inverse inserts 1. Iterating keeps the roots in their specified order and
   multiplies b by the product of the phi(a_i). At zero it is the scalar unit.
   The sheaf tensor bilinear universal property determines these maps, including
   zero rings. Root pullback commutes with this formula by
   lem-asd-etale-finite-twist-pullback; no global primitive root is chosen.
3. Apply lem-sfb-ringed-derived-monoidal-comparisons to geometric and coefficient
   pullbacks. The coefficient square commutes on constant sections. The composition
   and tensor equations of lem-pur-cochain-pullback-tensor-coherence identify the
   pasted open/projective comparison with the one for their composite u_r.
4. Keep the integer shift comparisons of lem-weil-pbc-total-tensor-integer-shifts.
   Their second-factor signs are (-1)^(2rm)=1 and mixed signs (-1)^(4r)=1.
   Lem-weil-pbc-cochain-pullback-tensor-shift preserves these maps under both kinds
   of pullback. Hence combining shifts leaves no sign or orientation factor.
5. Unpack the existing recursive normal form: its successor J first composes the
   two pullbacks, moves through the old tensor and shift, pulls back the old Tate
   power, appends the new root factor, reassociates, and adds the even shifts.
   The coefficient formulas and coherence from steps 2--4 show that the successor
   J-square commutes: both paths pull back the same representative element, keep
   the ordered roots, and multiply by the same b times product phi(a_i).
   The bilinear universal property gives equality of chain maps, hence of their
   localized derived morphisms.
6. Induct along the tower. At zero all normalized maps are identity. At a
   successor expand A and I; use the induction hypothesis, naturality of the line
   comparison at the preceding I, then the J-square of step 5. The resulting
   composite is precisely a_(r+1) followed after T(I_(r+1)). Evaluate on the
   bounded constructible finite-Tor inputs. No flatness of phi is needed. -/
theorem ordered_tate_scalar_normalization
    (ell p n : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
    ∃ hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)),
    ∀ (d : ℕ) (K : DerivedCategoryModule A S)
      (_hK : ProEtale.AdjunctionTransfer.etaleProperty A S K),
      (ProEtale.reductionEtaleAffineScalarIso φ S (ell ^ n) hA hB hS d K).hom ≫
        (orderedAffineRightIso B (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
          hB S hS d).hom.app ((scalarExtension φ S).obj K) =
      (scalarExtension φ (affineTraceTower S d)).map
        ((orderedAffineRightIso A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
          hA S hS d).hom.app K) ≫
        (orderedAffineDirectScalarIso φ (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
          hA hB S hS d K).hom := by
  sorry

end AlgebraicGeometry.Etale
