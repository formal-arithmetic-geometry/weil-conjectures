/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
/-! Intermediate base package for finite Tate pullback.
(blueprint: lem-asd-etale-finite-twist-pullback). -/
/-- Strict intermediate package for the finite Tate pullback theorem. The construction first
chooses the primitive-root etale cover, identifies the roots sheaf there with the constant
cyclic sheaf, extends scalars to `A`, and forms signed tensor powers and duals. The normalized
adjunction, unit, tensor, evaluation, identity, composition and local-trivialization equations
are then checked on the local basis and descend by etale-cover detection. This intermediate
package is used by the parent theorem; its proof is the corresponding group of steps in the
parent blueprint and remains available as a named proof obligation.
Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM.
(blueprint: lem-asd-etale-finite-twist-pullback-base). -/
theorem etaleFiniteTwistPullback_base (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) :
    ∃ (r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m))
      (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
      (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)),
    (∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
        Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
          upperStarGmSheafToGmSheaf v =
        (r v hT).hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf m).obj.obj W),
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
        (c v hT hT' 1).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (r v hT).hom).hom.app W z)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))),
      c v hT hT' 0 = (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      c v hT hT' (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1))) (finiteEtaleTateLine T m A hA)) ≪≫
          tensorIso (c v hT hT' (.ofNat (n + 1))) (c v hT hT' 1)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map
          ((ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T hA 0)) ≫ (c v hT hT' 0).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
          (finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
          tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' (.negSucc n)).hom ≫
          (ihom.ev (finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T' hA 0)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a)) ∧
    (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
        (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
        (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ),
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app
          (finiteEtaleTateSheaf A m T hA a) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT 0 a = λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT a 0 = ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      p T hT (.ofNat (n + 1)) 1 = Iso.refl _) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b d : ℤ),
      (p T hT a b).hom ▷ finiteEtaleTateSheaf A m T hA d ≫ (p T hT (a + b) d).hom =
        (α_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)
          (finiteEtaleTateSheaf A m T hA d)).hom ≫
        finiteEtaleTateSheaf A m T hA a ◁ (p T hT b d).hom ≫
          (p T hT a (b + d)).hom ≫
            eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_assoc a b d).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b : ℤ),
      (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
          (p T hT b a).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        (p T hT a b).hom) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      (p T hT (.ofNat (n + 1)) (.negSucc n)).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
            (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (finiteEtaleTateSheaf A m T hA 0)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map (p T hT a b).hom ≫
          (c v hT hT' (a + b)).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b) ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫ (p T' hT' a b).hom) := by
  sorry

end AlgebraicGeometry.Scheme
