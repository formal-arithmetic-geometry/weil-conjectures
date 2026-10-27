/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
public import Sheaf.Paper.PointTateRootCoordinates
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Compatible primitive-root bases of finite signed Tate twists

Source: Stacks Project, Etale Cohomology, Section 03PK (Kummer theory);
blueprint sk-prop-a1-kummer, Coefficients and Reduction to a geometric fibre
(blueprint: lem-pur-finite-twist-root-trivialization).

The structures below package the conclusion, including its canonical-map equations.
They add no coefficient, root, tensor or signed-line construction. A finite quotient
level is indexed by its predecessor n, so the quotient is O_E/(varpi_E^(n+1)).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures
namespace FiniteTwistRootTrivialization

/-- The published signed finite line, restricted to its constant scalar action.
This extends finiteTateProSheaf's nonnegative indexing without changing its object.
Source: coefficient-twist definition, signed cases
(blueprint: lem-pur-finite-twist-root-trivialization). -/
abbrev proSigned (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (T : Scheme.{u}) (s : ℤ) :=
  (finiteTateConstantRestriction l E n T).obj (finiteCoefficientTwist l E T n s)

/-- The conclusions for one coefficient quotient, one annihilating root exponent,
one primitive root, and one k-scheme. The degree-one tensor presentation is normalized
on every root-limit section, and the signed bases are normalized by tensor and evaluation.
Source: Stacks 03PK; blueprint Coefficients, signed powers
(blueprint: lem-pur-finite-twist-root-trivialization). -/
structure SignedBasis (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (T : Over (Spec (CommRingCat.of k)))
    (root : SheafOfModules.unit (purTwistRing T.left (purTwistFiniteRing T.left l r)) ≅
      purTwistRootsModule T.left l r)
    (etaleRoot : T.left.constantZMod (l ^ (r + 1)) ≅
      T.left.rootsOfUnitySheaf (l ^ (r + 1))) where
  invertible : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T.left, ⊤))
  presentation : finiteRootProTensor (finiteTateCoefficient l E n) (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) hA T.left ≅ proSigned l E n T.left 1
  presentation_projection : ∀ (U : T.left.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
    (x : (purTwistZlOne T.left l).obj.obj U),
    presentation.inv.hom.app U (finiteTateProGenerator l E n T.left U a x) =
      finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA T.left U a
        ((limit.π (proEtaleRootsOfUnityTower T.left l Fact.out) (op r)).hom.app U x)
  pro : ∀ s : ℤ, SheafOfModules.unit (integralCoefficientSheaf l E T.left n) ≅
    finiteCoefficientTwist l E T.left n s
  pro_signed : IsPurPointSignedCoordinates T.left
    (integralCoefficientCommRingSheaf l E T.left n) (purTwistFiniteOne T.left l E n) pro
  pro_one : ∀ U : T.left.ProEtᵒᵖ,
    (pro 1).hom.val.app U (1 : (integralCoefficientSheaf l E T.left n).obj.obj U) =
      presentation.hom.hom.app U
        (finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) hA T.left U 1
          (root.hom.val.app U
            (purPointConstant T.left (ZMod (l ^ (r + 1))) U 1)))
  etale : ∀ s : ℤ,
    finiteEtaleTateSheaf (finiteTateCoefficient l E n) (l ^ (r + 1)) T.left hA 0 ≅
      finiteEtaleTateSheaf (finiteTateCoefficient l E n) (l ^ (r + 1)) T.left hA s
  etale_zero : etale 0 = Iso.refl _
  etale_one : ∀ (U : T.left.Etaleᵒᵖ) (a : finiteTateCoefficient l E n),
    (etale 1).hom.hom.app U
      ((toSheafify T.left.smallEtaleTopology
        ((Functor.const T.left.Etaleᵒᵖ).obj
          (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)))).app
            U a) = finiteEtaleTateOneGenerator _ _ T.left hA U a
      (etaleRoot.hom.hom.app U
        ((toSheafify T.left.smallEtaleTopology
          ((Functor.const T.left.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (r + 1))))))).app U (ULift.up 1)))
  etale_positive : ∀ d : ℕ,
    etale (.ofNat (d + 2)) =
      (λ_ (finiteEtaleTateSheaf (finiteTateCoefficient l E n)
        (l ^ (r + 1)) T.left hA 0)).symm ≪≫
      tensorIso (etale (.ofNat (d + 1))) (etale 1)
  etale_dual : ∀ d : ℕ,
    tensorHom (etale (.ofNat (d + 1))).hom (etale (.negSucc d)).hom ≫
      (ihom.ev (finiteEtaleTateSheaf (finiteTateCoefficient l E n)
        (l ^ (r + 1)) T.left hA (.ofNat (d + 1)))).app
          (finiteEtaleTateSheaf (finiteTateCoefficient l E n) (l ^ (r + 1)) T.left hA 0) =
      (λ_ (finiteEtaleTateSheaf (finiteTateCoefficient l E n)
        (l ^ (r + 1)) T.left hA 0)).hom
  comparison : ∀ s : ℤ,
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
      T.left).obj (finiteEtaleTateSheaf (finiteTateCoefficient l E n)
        (l ^ (r + 1)) T.left hA s) ≅ proSigned l E n T.left s
  comparison_positive : ∀ d : ℕ,
    IsFiniteTateSiteComparison l E n T.left r hA d (comparison (.ofNat d))
  comparison_basis : ∀ s : ℤ,
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
      T.left).mapIso (etale s) ≪≫ comparison s =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
      T.left).mapIso (etale 0) ≪≫ comparison 0 ≪≫
        (finiteTateConstantRestriction l E n T.left).mapIso (pro s)

/-- One system for every scheme, root exponent and finite coefficient quotient.
The maps between signed lines are fixed by the displayed basis squares and the
canonical inverse-image and scalar-extension units, including at negative degrees.
Source: Stacks 03PK; blueprint Coefficients and geometric-fibre reduction
(blueprint: lem-pur-finite-twist-root-trivialization). -/
structure CompatibleBases (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] where
  root : ∀ (r : ℕ) (ζ : k), IsPrimitiveRoot ζ (l ^ (r + 1)) →
    ∀ T : Over (Spec (CommRingCat.of k)),
      SheafOfModules.unit (purTwistRing T.left (purTwistFiniteRing T.left l r)) ≅
        purTwistRootsModule T.left l r
  root_formula : ∀ (r : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ (l ^ (r + 1)))
    (T : Over (Spec (CommRingCat.of k))) (U : T.left.ProEtᵒᵖ)
    (j : ZMod (l ^ (r + 1))),
    (proEtaleRootsOfUnitySections T.left (l ^ (r + 1)) U
      ((root r ζ hζ T).hom.val.app U
        (purPointConstant T.left (ZMod (l ^ (r + 1))) U j))).toMul.val.val =
    U.unop.hom.appTop.hom
      ((T.hom.appTop.hom.comp (ΓSpecIso (CommRingCat.of k)).inv.hom) (ζ ^ j.val))
  root_quotient : ∀ (r : ℕ) (T : Over (Spec (CommRingCat.of k))),
    ∃ q : cokernel ((l ^ (r + 1)) • 𝟙 (purTwistZlOne T.left l)) ≅
        proEtaleRootsOfUnitySheaf T.left (l ^ (r + 1)),
      cokernel.π ((l ^ (r + 1)) • 𝟙 (purTwistZlOne T.left l)) ≫ q.hom =
        limit.π (proEtaleRootsOfUnityTower T.left l Fact.out) (op r)
  root_site : ∀ (r : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ (l ^ (r + 1)))
    (T : Over (Spec (CommRingCat.of k)))
    (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T.left, ⊤)))
    (U : T.left.Etaleᵒᵖ) (W : T.left.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T.left).obj U.unop) (j : ZMod (l ^ (r + 1))),
    (ProEtale.cartierRootsIso T.left (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T.left).obj
          (T.left.rootsOfUnitySheaf (l ^ (r + 1)))).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T.left).unit.app
              (T.left.rootsOfUnitySheaf (l ^ (r + 1)))).hom.app U
                ((T.left.constantZModIsoRootsOfUnitySheaf (l ^ (r + 1)) T.hom hζ).hom.hom.app U
                  ((toSheafify T.left.smallEtaleTopology
                    ((Functor.const T.left.Etaleᵒᵖ).obj
                      (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (r + 1))))))).app
                        U (ULift.up j))))) =
    (root r ζ hζ T).hom.val.app W
      (purPointConstant T.left (ZMod (l ^ (r + 1))) W j)
  root_power : ∀ (r r' : ℕ) (h : r ≤ r') (ζ η : k)
    (hζ : IsPrimitiveRoot ζ (l ^ (r' + 1)))
    (hη : IsPrimitiveRoot η (l ^ (r + 1))), η = ζ ^ (l ^ (r' - r)) →
    ∀ (T : Over (Spec (CommRingCat.of k))) (U : T.left.ProEtᵒᵖ) (j : ℕ),
      (proEtaleRootsOfUnityTransition T.left (l ^ (r + 1)) (l ^ (r' + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.add_le_add_right h 1))).hom.app U
          ((root r' ζ hζ T).hom.val.app U
            (purPointConstant T.left (ZMod (l ^ (r' + 1))) U j)) =
      (root r η hη T).hom.val.app U
        (purPointConstant T.left (ZMod (l ^ (r + 1))) U j)
  basis : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (ζ : k) (hζ : IsPrimitiveRoot ζ (l ^ (r + 1)))
    (T : Over (Spec (CommRingCat.of k))),
    SignedBasis k l E n r hA T (root r ζ hζ T)
      (T.left.constantZModIsoRootsOfUnitySheaf (l ^ (r + 1)) T.hom hζ)
  exponent_basis : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n r r' : ℕ) (_h : r ≤ r')
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (ζ η : k) (hζ : IsPrimitiveRoot ζ (l ^ (r' + 1)))
    (hη : IsPrimitiveRoot η (l ^ (r + 1))), η = ζ ^ (l ^ (r' - r)) →
    ∀ (T : Over (Spec (CommRingCat.of k))) (s : ℤ),
      (basis E n r' hA' ζ hζ T).pro s = (basis E n r hA η hη T).pro s ∧
      ∀ (U : T.left.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
        (z' : (T.left.rootsOfUnitySheaf (l ^ (r' + 1))).obj.obj U)
        (z : (T.left.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U),
        finiteTateEtaleRootValue T.left (l ^ (r + 1)) U z =
          finiteTateEtaleRootValue T.left (l ^ (r' + 1)) U z' ^ (l ^ (r' - r)) →
        (((basis E n r' hA' ζ hζ T).etale 1).symm ≪≫
          (basis E n r hA η hη T).etale 1).hom.hom.app U
            (finiteEtaleTateOneGenerator _ _ T.left hA' U a z') =
          finiteEtaleTateOneGenerator _ _ T.left hA U a z
  etale_pullback : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (ζ : k) (hζ : IsPrimitiveRoot ζ (l ^ (r + 1)))
    (T T' : Over (Spec (CommRingCat.of k))) (v : T' ⟶ T) (s : ℤ),
    (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v.left).map
        ((basis E n r hA ζ hζ T).etale s).hom ≫
      ((finiteEtaleTwistPullbackData _ (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA).c v.left
          (basis E n r hA ζ hζ T).invertible
          (basis E n r hA ζ hζ T').invertible s).hom =
    ((finiteEtaleTwistPullbackData _ (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA).c v.left
        (basis E n r hA ζ hζ T).invertible
        (basis E n r hA ζ hζ T').invertible 0).hom ≫
      ((basis E n r hA ζ hζ T').etale s).hom
  pro_pullback : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (ζ : k) (hζ : IsPrimitiveRoot ζ (l ^ (r + 1)))
    (T T' : Over (Spec (CommRingCat.of k))) (v : T' ⟶ T),
    ∃ d : ∀ s : ℤ,
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v.left).obj
        (proSigned l E n T.left s) ≅ proSigned l E n T'.left s,
    (∀ s : ℤ,
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v.left).map
        ((finiteTateConstantRestriction l E n T.left).map
          ((basis E n r hA ζ hζ T).pro s).hom) ≫ (d s).hom =
      (d 0).hom ≫ (finiteTateConstantRestriction l E n T'.left).map
        ((basis E n r hA ζ hζ T').pro s).hom) ∧
    (∀ a : ℕ, IsFiniteTateProPullback l E n T.left v.left a (d (.ofNat a))) ∧
    ∀ s : ℤ,
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v.left).map
        ((basis E n r hA ζ hζ T).comparison s).hom ≫ (d s).hom =
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v.left).hom.app
          (finiteEtaleTateSheaf _ (l ^ (r + 1)) T.left hA s) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
        T'.left).map
          (((finiteEtaleTwistPullbackData _ (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) hA).c v.left
              (basis E n r hA ζ hζ T).invertible
              (basis E n r hA ζ hζ T').invertible s).hom) ≫
      ((basis E n r hA ζ hζ T').comparison s).hom
  coefficient : ∀ (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (n n' r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (hB : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l F n') = 0)
    (φ : finiteTateCoefficient l E n →+* finiteTateCoefficient l F n')
    (ζ : k) (hζ : IsPrimitiveRoot ζ (l ^ (r + 1)))
    (T : Over (Spec (CommRingCat.of k))),
    ∃ (e : ∀ s : ℤ,
      (ProEtale.etaleSheafExtendScalars φ T.left).obj
        (finiteEtaleTateSheaf _ (l ^ (r + 1)) T.left hA s) ≅
          finiteEtaleTateSheaf _ (l ^ (r + 1)) T.left hB s)
      (d : ∀ s : ℤ, (ProEtale.sheafExtendScalars φ T.left).obj
        (proSigned l E n T.left s) ≅ proSigned l F n' T.left s),
    (∀ (U : T.left.Etaleᵒᵖ) (a : finiteTateCoefficient l E n),
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T.left).homEquiv _ _
        (e 0).hom).hom.app U
          ((toSheafify T.left.smallEtaleTopology
            ((Functor.const T.left.Etaleᵒᵖ).obj
              (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)))).app
                U a) =
      (toSheafify T.left.smallEtaleTopology
        ((Functor.const T.left.Etaleᵒᵖ).obj
          (ModuleCat.of (finiteTateCoefficient l F n') (finiteTateCoefficient l F n')))).app
            U (φ a)) ∧
    (∀ (U : T.left.ProEtᵒᵖ) (a : finiteTateCoefficient l E n),
      ((ProEtale.sheafExtendScalarsAdjunction φ T.left).homEquiv _ _
        (d 0).hom).hom.app U
          ((realizationRingUnit (ProEt.topology T.left) (finiteTateCoefficient l E n)).app
            U a) =
      (realizationRingUnit (ProEt.topology T.left) (finiteTateCoefficient l F n')).app
        U (φ a)) ∧
    (∀ s : ℤ,
      (ProEtale.etaleSheafExtendScalars φ T.left).map
        ((basis E n r hA ζ hζ T).etale s).hom ≫ (e s).hom =
      (e 0).hom ≫ ((basis F n' r hB ζ hζ T).etale s).hom) ∧
    (∀ s : ℤ,
      (ProEtale.sheafExtendScalars φ T.left).map
        ((finiteTateConstantRestriction l E n T.left).map
          ((basis E n r hA ζ hζ T).pro s).hom) ≫ (d s).hom =
      (d 0).hom ≫ (finiteTateConstantRestriction l F n' T.left).map
        ((basis F n' r hB ζ hζ T).pro s).hom) ∧
    (∀ s : ℤ,
      (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ T.left).inv.app
          (finiteEtaleTateSheaf _ (l ^ (r + 1)) T.left hA s) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n'))
          T.left).map (e s).hom ≫ ((basis F n' r hB ζ hζ T).comparison s).hom =
      (ProEtale.sheafExtendScalars φ T.left).map
        ((basis E n r hA ζ hζ T).comparison s).hom ≫ (d s).hom) ∧
    (∀ (U : T.left.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
      (z : (T.left.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U),
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T.left).homEquiv _ _
        (e 1).hom).hom.app U (finiteEtaleTateOneGenerator _ _ T.left hA U a z) =
      finiteEtaleTateOneGenerator _ _ T.left hB U (φ a) z) ∧
    ∀ (U : T.left.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
      (x : (purTwistZlOne T.left l).obj.obj U),
      ((ProEtale.sheafExtendScalarsAdjunction φ T.left).homEquiv _ _
        (d 1).hom).hom.app U (finiteTateProGenerator l E n T.left U a x) =
      finiteTateProGenerator l F n' T.left U (φ a) x

/-- Finite signed Tate twists have root bases in both topologies, with their
canonical quotient, tensor, signed, pullback, comparison and coefficient normalizations.
Source: Stacks Project, Etale Cohomology, Section 03PK; current blueprint
sk-prop-a1-kummer, Coefficients and final twist sentence of Reduction to a geometric fibre
(blueprint: lem-pur-finite-twist-root-trivialization).

Proof:
1. The extension-integers DVR theorem and finite-quotient theorem give finiteness.
   Ell lies in the maximal ideal (varpi), so ell^(n+1) vanishes in A_(E,n+1).
2. The additive-group assertion of lem-pur-affine-line-finite-group-devissage shows
   that its cardinality is an ell power; no cohomological assertion is needed.
3. Lem-pur-primitive-root-etale-basis gives the map j to zeta^j on the etale site.
   Lem-amb-finite-root-site-comparison gives precisely the same map pro-etale locally.
4. Extend zeta to compatible primitive roots. The sectionwise limit identifies the
   root limit with the limit of constant cyclic groups. Projection is locally onto;
   a sequence with zero r-coordinate is uniquely divisible by ell^(r+1) after
   shifting its labels. Thus its kernel is ell^(r+1) times the limit, giving the
   displayed cokernel comparison, independent of the auxiliary root extensions.
5. Expand def-coefficient-twists-detailed. The two scalar extensions associate by
   (x tensor u) tensor a to x tensor ua. Since mA=0, the root projection descends
   to the tensor over Z/m. Lift roots locally for the inverse; changing a lift
   by my changes x tensor a by y tensor ma=0. This needs no flatness.
6. Extend the root basis to A, take its tensor powers, and evaluate negative
   functionals on the positive generator. Evaluation has inverse a to (be to ab).
7. The canonical root pullback fixes constant roots. Lem-amb-finite-tate-site-descent
   identifies positive comparisons with the detailed twist. Evaluation determines
   negative comparisons. All squares hold on the indicated generating bases.
8. For two coefficients use one annihilating exponent and a primitive root there.
   Power transitions reduce the labels. Scalar extension sends ae tensor b to
   phi(a)be; its tensor powers and evaluation duals preserve the signed generators.
   These formulas give isomorphisms even for coefficient quotients. They commute
   with scheme pullback, site comparison, identities and composition on generators.
-/
theorem finite_twist_root_trivialization (P : PurityFiniteSetting.{u}) :
    Finite P.Ring ∧ ((P.coefficients.l ^ P.level : ℕ) : P.Ring) = 0 ∧
    (∃ b : ℕ, Nat.card P.Ring = P.coefficients.l ^ b) ∧
    Nonempty (CompatibleBases P.field.k P.coefficients.l) := by
  sorry

end FiniteTwistRootTrivialization
end WeilConjectures
