/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingHomExtensionDefsSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import WeilConjectures.Algebra.Homology.BoundedAboveRHomHyperExt

/-! # Coherent derived Hom for one-sided bounded complexes

Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom,
the algebra assertion in its proof
(blueprint: lem-trf-bounded-above-coherent-rhom).

The existing one-object site with only identity coverings presents ordinary A-modules.
Cohomology is evaluated at its unique object to express finite generation over A.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Derived Hom from a bounded-above coherent complex to a bounded-below coherent
complex has finite cohomology, vanishing below the difference of their bounds.
Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom, proof
(blueprint: lem-trf-bounded-above-coherent-rhom).

Proof:
1. Over the Noetherian ring A, submodules of finite modules are finite by
   lem-weil-pbc-noetherian-submodule-finite. Quotients are generated by the images of
   generators. An extension of finite modules is generated by generators of its submodule
   and lifts of generators of its quotient. Thus finite filtrations with finite graded
   pieces have finite underlying modules.
2. For a finite module N in degree zero, lem-trf-source-hyperext-module-target gives
   E2^{i,j} = Ext^i_A(H^{-j}(K),N), supported in i >= 0 and j >= -a.
   Lem-sc-ext-noetherian-finite makes these terms finite.
3. Every later page is a subquotient of the preceding page. Step 1 makes every finite
   page finite; eventual stabilization makes each E-infinity term finite. The finite
   abutment filtration in degree p has -a <= j <= p. Step 1 proves finiteness of
   H^p RHom(K,N[0]), including its vanishing for p < -a.
4. Apply lem-per-bounded-above-rhom-hyperext to the one-object site with r=a and c=b.
   It gives E2^{p,q} = H^p RHom(K,H^q(L)[0]) abutting to H^{p+q} RHom(K,L),
   supported in p >= -a and q >= b, with finite exhaustive separated filtrations.
5. Step 3 makes every E2 term finite. Step 1 propagates finiteness to later pages.
   At (p,q), incoming differentials vanish for s > p+a and outgoing ones for
   s > q-b+1, so the stable term is a finite-page term. In degree n only
   b <= q <= n+a contribute; the finite filtration and Step 1 give finite generation.
   For n < b-a this interval is empty, so its finite exhaustive separated filtration
   has zero graded pieces and zero abutment. This proves the asserted lower bound.
-/
theorem boundedAbove_coherent_rhom
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    (K L : DerivedCategory (RingSiteModules A)) (a b : ℤ)
    (hK : ∀ j : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) j).obj K).val.obj (op ⟨PUnit.unit⟩)))
    (hL : ∀ j : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) j).obj L).val.obj (op ⟨PUnit.unit⟩)))
    (hKa : ∀ j : ℤ, a < j → IsZero ((homologyFunctor (RingSiteModules A) j).obj K))
    (hLb : ∀ j : ℤ, j < b → IsZero ((homologyFunctor (RingSiteModules A) j).obj L)) :
    (∀ r : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) r).obj
        ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
          (CochainComplex.onePointRingSheaf A)).obj (op K, L))).val.obj
            (op ⟨PUnit.unit⟩))) ∧
    (∀ r : ℤ, r < b - a → IsZero
      ((homologyFunctor (RingSiteModules A) r).obj
        ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
          (CochainComplex.onePointRingSheaf A)).obj (op K, L)))) := by
  sorry

end DerivedCategory
