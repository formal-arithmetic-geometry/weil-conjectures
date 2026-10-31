/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackModuleInjectiveTransport
public import WeilConjectures.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import WeilConjectures.CategoryTheory.SiteAugmentationSpectralSequence
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.AlgebraicGeometry.AlgebraicStackFibreProducts
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-! # Smooth-atlas Cech spectral sequence for arbitrary module sheaves

Source: Stacks Project, stacks-sheaves.tex, Tag 072G (1)(b), through Tag 072E;
homology.tex, Tags 0130 and 0132
(blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence).

Pages, their first-page identifications and abutment filtrations live in the
functor category of all source modules. This includes naturality on coefficients.
The first differential uses the canonical restrictions on compatible families,
transported through the injective-resolution comparisons, with alternating signs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {S : AlgebraicGeometry.Scheme.{u}}
    {U X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}

/-- The actual higher direct image from the p-th nerve, after precomposition.
Source: Stacks 072G (1)(b)
(blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence). -/
def stackCechModuleDerivedTerm
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (a : BasedFunctor U X) (f : BasedFunctor X Y)
    (p q : ℕ) :=
  moduliBigEtalePrecomposition.{u, v, max (u + 1) v w}
    (fibredModuleCechLevel_isFibred.{u, v, w} hU.1.1 hX.1.1 a p)
    hX.1.1 (fibredModuleCechProjection.{u, v, w} a p) ⋙
    moduliBigEtaleHigherImage.{u, v, max (u + 1) v w}
      (fibredModuleCechLevel_isFibred.{u, v, w} hU.1.1 hX.1.1 a p) hY.1.1
      ((fibredModuleCechProjection.{u, v, w} a p).comp f) q

/-- Canonical comparison, computed on the pulled-back injective resolution.
Source: Stacks 072E and 06X2
(blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence). -/
def stackCechModuleDerivedComparisonApp
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (a : BasedFunctor U X)
    (ha : IsRepresentableByAlgebraicSpaces a) (f : BasedFunctor X Y) (p q : ℕ)
    (M : ModuliBigEtaleModules.{u, v, max (u + 1) v w} X hX.1.1) :
    ((fibredModuleCechTerm.{u, v, w} hU.1.1 hX.1.1 hY.1.1 a f p).rightDerived q).obj M ≅
      (stackCechModuleDerivedTerm.{u, v, w} hU hX hY a f p q).obj M :=
  let hP := fibredModuleCechLevel_algebraic.{u, v, w} hU hX a ha p
  let hT := stack_module_injective_transport.{u, v, w} hP.1 hX
    (fibredModuleCechProjection.{u, v, w} a p)
  letI := hT.1
  letI := hT.2.1
  letI := hT.2.2.2.2 hP.2
  let G := moduliBigEtaleDirectImage.{u, v, max (u + 1) v w}
    (fibredModuleCechLevel_isFibred.{u, v, w} hU.1.1 hX.1.1 a p) hY.1.1
    ((fibredModuleCechProjection.{u, v, w} a p).comp f)
  Functor.compRightDerivedObjIso _ G
    (fun I _ ↦ Functor.rightAcyclic_of_injective
      ((moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} _ hX.1.1
        (fibredModuleCechProjection.{u, v, w} a p)).obj I)) q M

/-- The canonical derived comparison is natural in every module morphism.
Source: Stacks 072E and derived.tex, Tags 013P and 013S
(blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence).
Proof: lift a coefficient map to injective resolutions. Its precomposition is a
map of injective resolutions by the transport theorem. The two comparisons are
induced by these same complexes and maps, so their cohomology squares commute.
Two choices of lift are homotopic by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy,
and have the same cohomology map. -/
theorem stackCechModuleDerivedComparison_naturality
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (a : BasedFunctor U X)
    (ha : IsRepresentableByAlgebraicSpaces a) (f : BasedFunctor X Y) (p q : ℕ)
    {M N : ModuliBigEtaleModules.{u, v, max (u + 1) v w} X hX.1.1} (k : M ⟶ N) :
    ((fibredModuleCechTerm.{u, v, w} hU.1.1 hX.1.1 hY.1.1 a f p).rightDerived q).map k ≫
        (stackCechModuleDerivedComparisonApp.{u, v, w} hU hX hY a ha f p q N).hom =
      (stackCechModuleDerivedComparisonApp.{u, v, w} hU hX hY a ha f p q M).hom ≫
        (stackCechModuleDerivedTerm.{u, v, w} hU hX hY a f p q).map k := by
  sorry

/-- The natural comparison is specified by its actual resolution comparisons.
Source: Stacks 072E (blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence). -/
def stackCechModuleDerivedComparison
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (a : BasedFunctor U X)
    (ha : IsRepresentableByAlgebraicSpaces a) (f : BasedFunctor X Y) (p q : ℕ) :
    (fibredModuleCechTerm.{u, v, w} hU.1.1 hX.1.1 hY.1.1 a f p).rightDerived q ≅
      stackCechModuleDerivedTerm.{u, v, w} hU hX hY a f p q :=
  NatIso.ofComponents (stackCechModuleDerivedComparisonApp.{u, v, w} hU hX hY a ha f p q)
    (fun k ↦ stackCechModuleDerivedComparison_naturality.{u, v, w} hU hX hY a ha f p q k)

/-- The higher-direct-image face map, with its canonical resolution normalization.
Source: Stacks 072E (blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence). -/
def stackCechModuleDerivedCoface
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (a : BasedFunctor U X)
    (ha : IsRepresentableByAlgebraicSpaces a) (f : BasedFunctor X Y)
    (p q : ℕ) (j : Fin (p + 2)) :
    stackCechModuleDerivedTerm.{u, v, w} hU hX hY a f p q ⟶
      stackCechModuleDerivedTerm.{u, v, w} hU hX hY a f (p + 1) q :=
  (stackCechModuleDerivedComparison.{u, v, w} hU hX hY a ha f p q).inv ≫
    NatTrans.rightDerived
      (fibredModuleCechCoface.{u, v, w} hU.1.1 hX.1.1 hY.1.1 a f p j) q ≫
      (stackCechModuleDerivedComparison.{u, v, w} hU hX hY a ha f (p + 1) q).hom

/-- Natural first-quadrant Cech spectral sequence for every structure-sheaf module.
Source: Stacks 072G (1)(b), 072E and homology.tex, Tags 0130 and 0132
(blueprint: lem-sfb-stack-smooth-cech-module-spectral-sequence).

Proof:
1. Representable smooth surjectivity gives etale-local lifts of every object by
   lem-sfb-stack-smooth-presentation-criterion and
   lem-sfb-smooth-stack-family-etale-object-lifts. This includes the empty scheme.
2. The module category is Grothendieck abelian by prop-pur-kinjective-resolutions-exist.
   Lemma lem-sp-grothendieck-enough-injectives supplies a nonnegative resolution I.
   Nerve levels are algebraic by lem-sfb-algebraic-stack-fibre-products and their
   projections representable by lem-sfb-fibred-groupoid-representable-smooth-calculus.
   Lemma lem-sfb-stack-representable-module-injective-transport makes each pullback
   of I an injective resolution and each direct-image term injective.
3. Apply lem-sfb-stack-relative-cech-module-augmentation-exact to every I^q.
   Each exact row splits successively, since its terms and first object are
   injective. Applying additive f_* preserves these splitting identities.
   Direct-image composition is the canonical identification of right adjoints
   to equal precomposition functors.
4. Form C^(p,q) = (f u_p)_* u_p^* I^q. The alternating cofaces square to zero
   by pairing omissions of distinct entries, and commute with the vertical
   differential. The total differential is delta + (-1)^p d_I, as in
   def-sp-double-complex-total. The augmented row calculation and
   lem-sc-first-quadrant-column-augmentation identify its total cohomology
   with R^n f_* M.
5. Apply thm-sp-double-complex-spectral-sequences to the column filtration.
   Column cohomology gives exactly the displayed first page and its first
   differential, via the specified pulled-back-resolution comparison. The
   theorem gives the bidegrees, stabilization and finite abutment filtration.
6. Lift a module map using lem-weil-pbc-injective-resolution-lift-exists.
   Precomposition, direct image and face restriction give a double-complex map.
   Two lifts are homotopic by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.
   Column homotopies give the same E1 maps. On totals the homotopy is (-1)^p h
   in column p; horizontal terms cancel and it preserves the column filtration.
   Thus pages and filtrations are natural in M and independent of resolution.
-/
theorem stack_smooth_cech_module_spectral_sequence
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (f : BasedFunctor X Y) (a : BasedFunctor U X)
    (ha : IsRepresentableByAlgebraicSpaces a)
    (hsmooth : ModuliSpaceTest (@AlgebraicGeometry.Smooth) a)
    (hsurj : IsSurjectiveModuliMap a) :
    ∃ (E : CohomologicalSpectralSequenceNat
        (ModuliBigEtaleModules.{u, v, max (u + 1) v w} X hX.1.1 ⥤
          ModuliBigEtaleModules.{u, v, max (u + 1) v w} Y hY.1.1) 1)
      (e₁ : ∀ p q : ℕ, (E.page 1).X (p, q) ≅
        stackCechModuleDerivedTerm.{u, v, w} hU hX hY a f p q),
      (∀ p q : ℕ, (E.page 1).d (p, q) (p + 1, q) ≫ (e₁ (p + 1) q).hom =
        (e₁ p q).hom ≫ ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          stackCechModuleDerivedCoface.{u, v, w} hU hX hY a ha f p q j) ∧
      (∀ (p q : ℕ) (r : ℤ) (hr : 1 ≤ r), max (p : ℤ) ((q : ℤ) + 1) < r →
        Nonempty ((E.page r hr).X (p, q) ≅
          (SimplicialSlice.augmentationPagesFromTwo E).pageInfinity (p, q))) ∧
      (SimplicialSlice.augmentationPagesFromTwo E).AbutsTo
        (fun n : ℕ ↦ moduliBigEtaleHigherImage.{u, v, max (u + 1) v w} hX.1.1 hY.1.1 f n) := by
  sorry

end CategoryTheory
