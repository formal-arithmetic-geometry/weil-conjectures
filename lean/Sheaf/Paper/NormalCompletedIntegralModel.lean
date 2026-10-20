/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Integral models of lisse rational sheaves on normal schemes

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10 and Proposition 6.8.4(1),(4)
(blueprint: lem-a1-normal-completed-integral-model).

This assertion constructs an abstract locally free integral model. It does not assert
that the model embeds in the original rational sheaf. The latter assertion requires
injectivity of the coefficient localization and is proved separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- Forgetting abelian groups preserves the smaller filtered colimits used on this site.
Source: the size convention in Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-normal-completed-integral-model). -/
instance (priority := 100000) normalModelForgetAbFiltered [UnivLE.{u + 1, w}] :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget AddCommGrpCat.{w}) :=
  preservesFilteredColimitsOfSize_of_univLE.{w, w, u + 1, u + 1}
    (forget AddCommGrpCat.{w})

/-- Sheafification in any universe containing the pro-etale site, by transport of
the existing Grothendieck-abelian construction on a small model.
Source: Bhatt--Scholze, Definition 6.8.3, size convention
(blueprint: lem-a1-normal-completed-integral-model). -/
instance (priority := 100000) normalModelSiteAbSheafify (T : Scheme.{u})
    [Small.{w} T.ProEt] [LocallySmall.{w} T.ProEt] :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} T.ProEt := inferInstance
  letI : HasSheafify ((equivSmallModel.{w} T.ProEt).inverse.inducedTopology
      (Scheme.ProEt.topology T)) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite.{u, w, u + 1, w + 1, w} _ _

/-- Sheafification on each slice in the common coefficient universe. This transports
the existing small-site construction without identifying object and arrow universes.
Source: the size convention for Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-normal-completed-integral-model). -/
instance (priority := 100000) normalModelSliceAbSheafify (T : Scheme.{u}) (U : T.ProEt)
    [Small.{w} (Over U)] [LocallySmall.{w} (Over U)] :
    HasSheafify ((Scheme.ProEt.topology T).over U) AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} (Over U) := inferInstance
  letI : HasSheafify
      ((equivSmallModel.{w} (Over U)).inverse.inducedTopology
        ((Scheme.ProEt.topology T).over U)) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite.{u, w, u + 1,
    w + 1, w} _ _

/-- Local bijectivity on the same slices supplies the ordinary module sheafification API.
Source: the size convention for Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-normal-completed-integral-model). -/
instance (priority := 100000) normalModelSliceAbLocallyBijective
    (T : Scheme.{u}) (U : T.ProEt)
    [Small.{w} (Over U)] [LocallySmall.{w} (Over U)] :
    ((Scheme.ProEt.topology T).over U).WEqualsLocallyBijective
      AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} (Over U) := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Local bijectivity for the base site in the common coefficient universe.
Source: Bhatt--Scholze, Definition 6.8.3, size convention
(blueprint: lem-a1-normal-completed-integral-model). -/
instance (priority := 100000) normalModelSiteAbLocallyBijective (T : Scheme.{u})
    [Small.{w} T.ProEt] [LocallySmall.{w} T.ProEt] :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} T.ProEt := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- On a normal Noetherian separated scheme, every lisse rational sheaf is the
rationalization of a locally finite free integral model. The prescribed section is
exactly the constant uniformizer in the completed coefficient ring.

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10 and Proposition 6.8.4(1),(4), pp. 59--71
(blueprint: lem-a1-normal-completed-integral-model).

Proof. Decompose the Noetherian scheme into its finitely many clopen connected
components. On a nonempty component choose a geometric point. Normality implies
geometric unibranchness, so the pro-etale monodromy group is the profinite etale
fundamental group by Lemma 7.4.10. Lemma 7.4.7 realizes the given lisse sheaf by a
continuous finite-dimensional representation. A compact group preserves a finite free
lattice: the span of the translates of any lattice is bounded, finitely generated,
and invariant, and freeness follows over the discrete valuation ring. Its finite
quotients form a normalized tower of finite free continuous representations. The finite
Galois correspondence realizes this tower by finite locally constant etale sheaves.
Proposition 6.8.4(1) realizes the inverse limit as an integral lisse sheaf, and the
normalized rational monodromy comparison identifies its rationalization with the
original sheaf. Lemma 6.8.2 identifies these coefficients with the displayed completed
ring and its localization, respecting the constant uniformizer. Glue the integral
models and their isomorphisms over the disjoint clopen components. Rank zero gives
the zero model; the empty scheme gives the empty gluing. Universe lifts and small
models transport the same sheaves and maps, without identifying the site and
coefficient universes. No integral embedding or choice of an image is used. -/
theorem exists_normal_completed_integral_model
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T] [T.IsSeparated]
    (hnormal : ∀ x : T,
      IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    (hl : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (s : ((WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat).sections)
    (hs : ∀ U : T.ProEtᵒᵖ, s.val U =
      ((WeilConjectures.integralConstantToCompletionOfUniverses l E T).hom.app U)
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              (ULift.up (Padic.coefficientExtensionUniformizer l E))))
    (L : ringedSiteModules.{max v (u + 1)}
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).obj
        (ringedLocalizationRingOfUniverses.{max v (u + 1), u + 1, u}
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T) s)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ M : ringedSiteModules.{max v (u + 1)}
        (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T),
      M.IsFiniteLocallyFree ∧
      Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1,
        max v (u + 1), max v (u + 1)}
        (ringedLocalizationRingUnitOfUniverses.{max v (u + 1), u + 1, u}
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T) s) M ≅ L) := by
  sorry

end AlgebraicGeometry.ProEtale
