/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1CompactificationFibre.P1CompactificationFibre
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Polynomial.Laurent
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.SetTheory.Cardinal.Finite
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.AlgebraicGeometry.AffinePuncturedLine.AffinePuncturedLineAlgebra
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
public import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

/-!
# Origin-normalized compact support for arbitrary finite coefficient rings

Source: blueprint sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2; released repair note of 2026-11-01
(blueprint: lem-pur-finite-origin-forget-support).

The definitions use the published Kummer splice, compactification and comparison
maps. The coefficient ring is an arbitrary finite commutative ring; no
PurityFiniteSetting is used in these statements.
The origin-normalized proof route retains its recorded BLUEPRINT QUESTION.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale AlgebraicGeometry.Etale.P1CompactificationFibre

namespace AlgebraicGeometry.Etale.FiniteRingOrigin


/-- Restriction along the etale subsite identifies the two supported-section
kernels, uniquely compatibly with their inclusions into global sections.
Source: Stacks 099R and 09XP, blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support).
Proof: comparison direct image is restriction to the etale subsite. The terminal
object and the open complement are unchanged. The global-sections comparison
intertwines their restriction maps. Kernel functoriality gives an isomorphism;
the monic kernel inclusion determines it uniquely and proves naturality. -/
theorem supportKernelComparison_existsUnique (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ∃! e : ProEtale.comparisonLowerStar (C A) T ⋙ globalSectionsWithSupport (C A) i ≅
        ProEtale.globalSectionsWithSupport (C A) i,
      ∀ G : Sheaf (Scheme.ProEt.topology T) (C A),
        e.hom.app G ≫ (Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
          (op (Scheme.ProEt.mk i.openComplement.ι))).app G =
        (Sheaf.ΓSupportι T.smallEtaleTopology (C A)
          (op (Scheme.Etale.mk i.openComplement.ι))).app
            ((ProEtale.comparisonLowerStar (C A) T).obj G) ≫
          (ProEtale.comparisonLowerStarCompGlobalSectionsIso (C A) T).hom.app G := by
  let R := AlgebraicGeometry.ProEtale.comparisonLowerStar (C A) T
  let r := Sheaf.natTransΓRes T.smallEtaleTopology (C A)
    (op (Scheme.Etale.mk i.openComplement.ι))
  let r' := Sheaf.natTransΓRes (Scheme.ProEt.topology T) (C A)
    (op (Scheme.ProEt.mk i.openComplement.ι))
  let W := (Functor.whiskeringLeft _ _ (C A)).obj R
  let e := AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso (C A) T
  have he : W.map r ≫ (Iso.refl _).hom = e.hom ≫ r' := by
    apply NatTrans.ext
    funext G
    simp only [W, r, r', NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app, Iso.refl_hom, Category.comp_id,
      Sheaf.natTransΓRes_app]
    let eE := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (C A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
    let eP := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) (C A)
      (Scheme.ProEt.isTerminalMkId T)
    have hE := Sheaf.ΓRes_map (R.obj G)
      (MorphismProperty.Over.homMk i.openComplement.ι
        (by change i.openComplement.ι ≫ 𝟙 T = _; simp) :
          Scheme.Etale.mk i.openComplement.ι ⟶ Scheme.Etale.mk (𝟙 T)).op
    have hP := Sheaf.ΓRes_map G
      (MorphismProperty.Over.homMk i.openComplement.ι
        (by change i.openComplement.ι ≫ 𝟙 T = _; simp) :
          Scheme.ProEt.mk i.openComplement.ι ⟶ Scheme.ProEt.mk (𝟙 T)).op
    rw [← evaluation_eq_ΓRes _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T) A (R.obj G)] at hE
    rw [← evaluation_eq_ΓRes _ (Scheme.ProEt.isTerminalMkId T) A G] at hP
    simp only [e, AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso,
      Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Category.id_comp,
      Category.assoc]
    change _ = eE.hom.app (R.obj G) ≫ eP.inv.app G ≫ _
    rw [← hP, ← Category.assoc (eP.inv.app G), Iso.inv_hom_id_app,
      Category.id_comp]
    exact hE.symm
  let b : R ⋙ globalSectionsWithSupport (C A) i ≅
      AlgebraicGeometry.ProEtale.globalSectionsWithSupport (C A) i :=
    PreservesKernel.iso W r ≪≫ kernel.mapIso (W.map r) r' e (Iso.refl _) he
  have hb : b.hom ≫ Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
      (op (Scheme.ProEt.mk i.openComplement.ι)) =
    Functor.whiskerLeft R (Sheaf.ΓSupportι T.smallEtaleTopology (C A)
      (op (Scheme.Etale.mk i.openComplement.ι))) ≫ e.hom := by
    dsimp only [b, Iso.trans_hom, Sheaf.ΓSupportι]
    rw [Category.assoc, kernel.mapIso_hom, kernel.lift_ι]
    rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  refine ⟨b, fun G ↦ NatTrans.congr_app hb G, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply (cancel_mono ((Sheaf.ΓSupportι (Scheme.ProEt.topology T) (C A)
    (op (Scheme.ProEt.mk i.openComplement.ι))).app G)).mp
  exact (hb' G).trans (NatTrans.congr_app hb G).symm

end AlgebraicGeometry.Etale.FiniteRingOrigin
