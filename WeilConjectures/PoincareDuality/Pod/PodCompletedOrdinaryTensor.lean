/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import all WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedModuleTensorTransport
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax

/-! # Completed coefficient reindexing on tensor representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open SemilinearSections CategoryTheory.MonoidalCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Reindexing completed coefficient modules preserves the ordinary tensor, with its
natural pure-tensor normalization. No residue-characteristic hypothesis is required.
Source: blueprint prop-pod-dual-tate-data-compatibility Step 5; Stacks 03EL and 07A4.
(blueprint: lem-pod-completed-ordinary-tensor).
Proof: postcomposition by g and its inverse give inverse equivalences of the pro-etale
sites. Transport the scalar action through the completed coefficient isomorphism,
whose projections are the specified quotient coefficient maps. On presheaf tensors
send x tensor y to x tensor y, using the inverse coefficient isomorphism to check the
balancing relation. The reverse rule is inverse on both pure tensors. The site
equivalence commutes with sheafification by its universal property, so these maps
sheafify to the asserted isomorphisms. Both composites in the naturality equation
send x tensor y to f(x) tensor h(y); generation by local pure tensors proves equality.
The same construction works on the empty site and for zero modules. -/
theorem podCompletedOrdinaryTensor_exists :
    ∃ e : ∀ M N : integralTowerModules l E Y,
      (podCompletedModuleInverseImage l E g).obj
          (ordinaryTensor.{u + 1, u, u} (Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) M N) ≅
        ordinaryTensor.{u + 1, u, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)
          ((podCompletedModuleInverseImage l E g).obj M)
          ((podCompletedModuleInverseImage l E g).obj N),
      (∀ {M M' N N' : integralTowerModules l E Y} (a : M ⟶ M') (b : N ⟶ N'),
        (podCompletedModuleInverseImage l E g).map
            (ordinaryTensorHom.{u + 1, u, u} (Scheme.ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) a b) ≫
            (e M' N').hom =
          (e M N).hom ≫ ordinaryTensorHom.{u + 1, u, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            ((podCompletedModuleInverseImage l E g).map a)
            ((podCompletedModuleInverseImage l E g).map b)) ∧
      (∀ (M N : integralTowerModules l E Y) (U : X.ProEt)
        (x : M.val.obj (op ((Scheme.proEtaleIsoPostcompose g).obj U)))
        (y : N.val.obj (op ((Scheme.proEtaleIsoPostcompose g).obj U))),
        (e M N).hom.val.app (op U)
          (tensorSection.{u + 1, u, u} (Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) M N
            (op ((Scheme.proEtaleIsoPostcompose g).obj U)) x y) =
          tensorSection.{u + 1, u, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            ((podCompletedModuleInverseImage l E g).obj M)
            ((podCompletedModuleInverseImage l E g).obj N) (op U) x y) := by
  let RX := completedIntegralCommRingSheafUnrestricted l E X
  let RY := completedIntegralCommRingSheafUnrestricted l E Y
  let V := Scheme.proEtaleIsoPostcompose g
  let c := inv (podCompletedRingMap l E g)
  let F := podCompletedModuleInverseImage l E g
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let := SheafOfModules.isMonoidal_W_independentCoefficients RY
  let := SheafOfModules.monoidalCategory RX
  let := SheafOfModules.monoidalCategory RY
  let : V.IsCocontinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) := by
    let he := Scheme.proEtaleIsoPostcompose_equivalence g
    let e : X.ProEt ≌ Y.ProEt := CategoryTheory.Equivalence.mk
      V (Scheme.proEtaleIsoPostcompose (inv g)) he.2.1.some.symm he.2.2.1.some
    exact (e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 he.2.2.2.2.some
  obtain ⟨L, hL, _, _⟩ :=
    SheafOfModules.exists_unique_ringedPushforward_laxMonoidal V RX RY c
  let : F.LaxMonoidal := L
  have hi (M N) : IsIso (Functor.LaxMonoidal.μ F M N) :=
    pushforward_tensor_isIso V RX RY c (fun U ↦ by
      change IsIso (c.hom.app U)
      infer_instance) L hL M N
  let t (M N) := @asIso _ _ _ _ (Functor.LaxMonoidal.μ F M N) (hi M N)
  refine ⟨fun M N ↦ (t M N).symm, ?_, ?_⟩
  · intro M M' N N' a b
    change F.map (a ⊗ₘ b) ≫ (t M' N').inv =
      (t M N).inv ≫ (F.map a ⊗ₘ F.map b)
    apply (cancel_epi (t M N).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    change Functor.LaxMonoidal.μ F M N ≫ F.map (a ⊗ₘ b) ≫
      (t M' N').inv = _
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    change (F.map a ⊗ₘ F.map b) ≫ (t M' N').hom ≫ (t M' N').inv = _
    simp
  · intro M N U x y
    have h := hL M N (op U) x y
    have h' := congrArg ((t M N).inv.val.app (op U)) h
    have hc := congrArg (fun f ↦ f.val.app (op U)
      (tensorSection.{u + 1, u, u} (Scheme.ProEt.topology X) RX
        (F.obj M) (F.obj N) (op U) x y)) (t M N).hom_inv_id
    exact h'.symm.trans hc

end WeilConjectures
