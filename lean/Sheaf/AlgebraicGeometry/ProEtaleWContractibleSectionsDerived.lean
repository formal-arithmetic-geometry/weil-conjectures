/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Derived sections over a w-contractible affine pro-etale object

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-wc-sections/det-pe-wc-sections-derived.md;
Stacks Project, Tags 079P, 070K and 070Y (blueprint: det-pe-wc-sections-derived).
-/

@[expose] public section

set_option autoImplicit false

universe t u v wA wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Evaluation is the composite of the existing additive forgetful and presheaf
evaluation functors. Source: the blueprint's sectionwise module category,
Stacks Project, Modules on Sites (blueprint: det-pe-wc-sections-derived). -/
instance moduleEvaluation_additive (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt) :
    (SheafOfModules.evaluation.{max u v (t + 1)} R (op U)).Additive :=
  inferInstanceAs ((SheafOfModules.forget.{max u v (t + 1)} R ⋙
    PresheafOfModules.evaluation R.obj (op U)).Additive)

/-- The K-injective resolution hypothesis for the recorded unbounded right derived
functor, on the original pro-etale module category. This only forgets the additional
monomorphism property of the existing K-injective resolution theorem.
Source: Stacks Project, Tag 079P (blueprint: det-pe-wc-sections-derived). -/
abbrev moduleQuasiIsoKInjectiveResolutions (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) :
    ∀ K : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ,
      ∃ (I : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, u, v} (topology X) R
  fun K ↦ (Abelian.HasKInjectiveResolutions.exists_isKInjective K).elim
    (fun I hI ↦ hI.elim (fun hKI hs ↦ hs.elim (fun s hs ↦ ⟨I, s, hKI, hs.2⟩)))

/-- The natural derived-sections unit is invertible on every unbounded complex, and
positive-degree cohomology of every module sheaf vanishes. The unit is evaluated on
the homotopy class of K: its source is termwise sections localized in the derived
category, via mapHomotopyCategory and quotientCompQhIso. The two derived-category
instances choose their morphism universes; they impose no boundedness condition.

Source: Weil conjectures blueprint, snapshot main-20261015,
det-pe-wc-sections-derived.md and its proof; Stacks Project, Tags 079P, 015F, 070K and
070Y (blueprint: det-pe-wc-sections-derived).

Proof:
1. By lem-weil-pbc-ring-sheaves-grothendieck, the module-sheaf category is Grothendieck
abelian in the common universe of def-weil-size-convention. Apply
lem-sfb-grothendieck-k-injective to obtain K-injective resolutions. ModuleCat is
abelian by lem-weil-pbc-ring-modules-enough-injectives. Evaluation is additive because
module morphisms are added sectionwise (def-weil-sheaf-of-modules-category).
2. By det-pe-wc-sections-exact, evaluation E is exact. Apply E to the short exact
sequences of cycles, boundaries and cohomology. Kernels and images are preserved,
so H^n(E(C)) = E(H^n(C)), naturally in every complex C. Thus evaluating a K-injective
quasi-isomorphism s : K → I gives a quasi-isomorphism, without boundedness.
3. The recorded def-sfb-right-derived-functor supplies its unit eta, invertible at I.
The resolution comparison c_s is RF(Q(s)) followed by eta_I inverse. Naturality
says eta_K followed by c_s is Q(E(s)). Both c_s and Q(E(s)) are invertible, by the
localization of def-weil-abstract-derived-category. Hence eta_K is invertible.
4. Take K = F[0]. The comparison identifies derived sections with F(U)[0]. Its
cohomology in every positive integer degree is zero, giving the second clause. -/
theorem wContractible_sections_derived
    (X : Scheme.{t}) (D : Type t) [CommRing D] [IsWContractibleRing D]
    (f : Spec (CommRingCat.of D) ⟶ X) [WeaklyEtale f]
    (R : Sheaf (topology X) RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{max u v (t + 1)} R)]
    [HasDerivedCategory.{wB}
      (ModuleCat.{max u v (t + 1)} (R.obj.obj (op (ProEt.mk f))))] :
    (∀ K : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ,
      IsIso ((Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (SheafOfModules.evaluation.{max u v (t + 1)} R (op (ProEt.mk f)))
        (moduleQuasiIsoKInjectiveResolutions X R)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
    ∀ (F : ringedSiteModules.{max u v (t + 1)} R) (q : ℤ), 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v (t + 1)} (R.obj.obj (op (ProEt.mk f)))) q).obj
          ((Functor.rightDerivedFunctorOfQuasiIsoResolutions
            (SheafOfModules.evaluation.{max u v (t + 1)} R (op (ProEt.mk f)))
            (moduleQuasiIsoKInjectiveResolutions X R)).obj
                ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
