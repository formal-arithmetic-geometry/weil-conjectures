/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible
import Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Constructible cohomology under quasi-finite lower shriek

Source: Stacks Project, More on Etale Cohomology, Tags 0GK3 and 0GKM,
finite-ring bounded-below specialization
(blueprint: lem-weil-pbc-etale-quasifinite-shriek-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Quasi-finite finitely presented lower shriek preserves constructible cohomology.
Source: Stacks Project, Tags 0GK3 and 0GKM
(blueprint: lem-weil-pbc-etale-quasifinite-shriek-constructible).

Proof plan:
1. Use `lem-weil-pbc-quasifinite-fp-finite-factorization` to factor the morphism
   as a quasi-compact open immersion followed by a finite finitely presented morphism.
   The latter is proper by `lem-weil-pbc-finite-morphism-permanence`.
2. Extension by zero preserves constructibility: transport the given strata through the
   open immersion and add its closed complement with constant zero value. The old parts
   remain constructible by retrocompactness. The restrictions are identified using
   `lem-weil-pbc-extension-by-zero-unit-iso`, `lem-weil-pbc-extension-by-zero-stalks`,
   `lemma-openclosed-stalk-upperstar`, and
   `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`.
3. Finite direct image and open extension by zero are exact by
   `lemma-weil-pbc-finite-direct-image-exact` and
   `lem-weil-pbc-extension-by-zero-exact`. Thus cohomology in degree q is the finite
   pushforward of the extension by zero of the original cohomology in degree q.
   Exactness preserves the lower bound and needs no upper bound or Tor hypothesis.
4. Apply `lem-weil-pbc-finite-fp-pushforward-constructible` in each degree, then
   `lem-weil-pbc-etale-shriek-compactification-independence` to pass to every compactification.
-/
theorem constructibleCohomology_lowerShriek_of_quasiFinite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace B] [QuasiSeparatedSpace B] (h : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [QuasiSeparated h] [LocallyOfFinitePresentation h] (hqf : h.IsQuasiFinite)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (c : Compactification h) [QuasiCompact c.i] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  obtain ⟨T₁, a, g, ha, hac, hg, hgfp, hgqc, hgqs, hag, hT₁, hT₁qs⟩ :=
    h.exists_qcqs_finitePresentation_factorization hqf
  have := ha
  have := hac
  have := hg
  have := hgfp
  have := hgqc
  have := hgqs
  have := hT₁
  have := hT₁qs
  let d : Compactification h :=
    { Z := T₁, i := a, g := g, comm := hag.symm,
      isProper := inferInstance, isOpenImmersion := ha }
  have : QuasiCompact d.i := hac
  intro q
  let F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff F).mp (hK q)
  have hzero : Scheme.IsConstructibleEtaleModuleSheaf
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj F) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff _).mpr
      (Scheme.IsConstructibleSheaf.openImmersionLowerShriek
        a a.closedComplement a.range_closedComplement F)
  have hfinite :=
    Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation g _ hzero
  have : Scheme.IsConstructibleSheaf
      ((lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj F)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff _).mp hfinite
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj K
  let e₁ := (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app J)
    ≪≫ ((lowerStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app J
  let e₂ := (lowerStar (ModuleCat.{u + 1} Λ) g).mapIso
    ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a) q).symm.app K)
  let e₃ := (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((rightDerivedLowerShriekOfCompactificationPlusIso Λ c d).app K)
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff _).mpr
    (Scheme.IsConstructibleSheaf.of_iso
      (F := (lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj F))
      (e₃ ≪≫ e₁ ≪≫ e₂).symm)

/-- The closed-immersion consequence of quasi-finite constructibility.
Source: Stacks Project, Tags 035C, 01TD, 0GK3 and 0GKM
(blueprint: lem-weil-pbc-etale-quasifinite-shriek-constructible).

Proof plan (step 5 of the node): a closed immersion is finite by
`lem-weil-pbc-closed-immersion-finite`, hence of finite type and separated. Its fibres are
empty or spectra of residue fields, so every fibre point is isolated. Apply the preceding
quasi-finite statement, retaining finite presentation and the qcqs scheme assumptions. -/
theorem constructibleCohomology_lowerShriek_of_isClosedImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace B] [QuasiSeparatedSpace B] (h : T ⟶ B)
    [IsClosedImmersion h] [LocallyOfFinitePresentation h]
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (c : Compactification h) [QuasiCompact c.i] :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  apply constructibleCohomology_lowerShriek_of_quasiFinite Λ h _ K hK c
  refine ⟨inferInstance, inferInstance, fun x ↦ ?_⟩
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (h.quasiFiniteAt x)

end AlgebraicGeometry.Etale
