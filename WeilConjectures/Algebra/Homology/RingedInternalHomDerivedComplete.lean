/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-!
# Derived internal Hom into a locally derived complete object

Source: Stacks Project, algebraization.tex, Lemma 099A and Definition 0999
(blueprint: lem-sf-ringed-rhom-derived-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

private theorem isZero_nestedHom
    {D : Type*} [Category* D] [HasZeroMorphisms D]
    (H : Dᵒᵖ × D ⥤ D) (S : WeilConjectures.CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal) (A B N : D)
    (h : IsZero (H.obj (op A, N))) :
    IsZero (H.obj (op A, H.obj (op B, N))) := by
  let := S.monoidal
  let := β
  let X := H.obj (op A, H.obj (op B, N))
  let t : (X ⊗ B) ⊗ A ≅ (X ⊗ A) ⊗ B :=
    (α_ X B A) ≪≫ ((tensorLeft X).mapIso (β_ B A)) ≪≫ (α_ X A B).symm
  -- Adjunction and symmetry move A past B. The last Hom set has a zero target.
  let e : (X ⟶ X) ≃ (X ⊗ B ⟶ H.obj (op A, N)) :=
    ((S.adjunction A).homEquiv X (H.obj (op B, N))).symm |>.trans
      (((S.adjunction B).homEquiv (X ⊗ A) N).symm) |>.trans
      (Iso.homCongr t.symm (Iso.refl N)) |>.trans
      ((S.adjunction A).homEquiv (X ⊗ B) N)
  exact (IsZero.iff_id_eq_zero X).mpr (e.injective (h.eq_of_tgt _ _))

/-- Derived internal Hom with arbitrary source preserves local derived ideal completeness.
The ideal subsheaf is presented by the monomorphism `ι` into the rank-one module sheaf.
There are no boundedness, finite-generation, finite-type-ideal, or flatness assumptions.

Source: Stacks Project, algebraization.tex, Lemma 099A and Definition 0999
(blueprint: lem-sf-ringed-rhom-derived-complete).

Proof:
1. Fix an object U and a section f of the ideal on U. Exact slice restriction identifies
   RHom(K,N)|_U with RHom(K|_U,N|_U), by
   lem-weil-pbc-ringed-internal-hom-exact-restriction (Stacks 08JB).
2. Use the closed symmetric monoidal structure on the slice (Stacks 0FPT and 08J9).
   Write A = O_U[1/f], B = K|_U and M = N|_U. For any test object X, adjunction,
   reassociation and symmetry give bijections
   Hom(X,RHom(A,RHom(B,M))) = Hom((X tensor A) tensor B,M)
     = Hom((X tensor B) tensor A,M) = Hom(X tensor B,RHom(A,M)).
3. Completeness of N says RHom(A,M) is zero, so the last Hom set is a singleton.
   Take X = RHom(A,RHom(B,M)). Its identity equals its zero endomorphism, hence
   X is zero. Transport this vanishing through the restriction comparison.
4. This holds for every U and f in the ideal, exactly the defining local completeness
   criterion. No localization change of rings is needed. -/
theorem isLocallyDerivedRingedIdealComplete_derivedInternalHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] (K N : ringedSiteDerived O)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι
      ((derivedInternalHomOfUniverses.{u, u, u, w} J O).obj (op K, N)) := by
  classical
  have hHom : derivedInternalHomOfUniverses.{u, u, u, w} J O =
      derivedInternalHom.{u, w} J O := by rfl
  intro U f hf
  have hNU := hN U f hf
  let : ∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over V)) :=
    fun V ↦ inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))))
  obtain ⟨e, _, _⟩ := ringedInternalHom_restriction J O
  obtain ⟨S, _, β, _⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u, u, u, w} (J.over U) (O.over U)
  let A := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))
  let KU := (ringedDerivedRestriction O U).obj K
  let NU := (ringedDerivedRestriction O U).obj N
  have hSlice : derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (O.over U) =
      derivedInternalHom.{u, w} (J.over U) (O.over U) := by rfl
  have hz := isZero_nestedHom
    (derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (O.over U)) S β A KU NU
    (by simpa only [hSlice] using hNU)
  have er : (ringedDerivedRestriction O U).obj
        ((derivedInternalHomOfUniverses.{u, u, u, w} J O).obj (op K, N)) ≅
      (derivedInternalHom.{u, w} (J.over U) (O.over U)).obj (op KU, NU) := by
    rw [hHom]
    exact (e U).app (op K, N)
  rw [hSlice] at hz
  exact hz.of_iso ((derivedInternalHom.{u, w} (J.over U) (O.over U)).mapIso
    ((Iso.refl (op A)).prod er))

end CategoryTheory
