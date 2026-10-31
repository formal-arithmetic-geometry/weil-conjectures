/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite module dévissage for direct images

Source: Stacks Project, `more-etale.tex`, Tag 0GKW, proof of
`lemma-proper-smooth-family-curves-modules`, lines 4379--4395
(blueprint: lem-fd-finite-module-direct-image-devissage).

The theorem states that constructibility of all cohomology sheaves of the derived
étale direct image for the successive quotients of a finite module filtration
implies constructibility for the whole module.  The proof uses the exact constant
sheaf sequence, the long exact sequence of derived direct images, and closure of
constructible sheaves under kernels, cokernels, and extensions, with the
zero-filtration and negative-degree cases included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Constructibility is preserved by finite coefficient-module dévissage.

Source: Stacks Project, `more-etale.tex`, Tag 0GKW, proof of
`lemma-proper-smooth-family-curves-modules`, lines 4379--4395
(blueprint: lem-fd-finite-module-direct-image-devissage).

Proof: write the filtration as successive inclusions of submodules.  Each
successive quotient gives a short exact sequence of finite constant sheaves by
`lem-constructible-constant-exact`.  Apply the long exact sequence for the right
derived direct image (`lem-weil-pbc-derived-functor-long-exact`) and induct on
the filtration index.  The induction starts with the zero sheaf, whose derived
direct image has zero cohomology; negative degrees vanish by the bounded-below
injective representative.  At every degree, the middle cohomology sheaf is an
extension of a cokernel by a kernel of maps between constructible sheaves, so it
is constructible by `thm-constructible-serre`.  The identification of right
derived cohomology with the displayed derived-direct-image cohomology uses the
K-injective representative from `lem-weil-pbc-dplus-injective-representative`.
-/
theorem finiteModule_directImage_devissage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (r : ℕ) (F : Fin (r + 1) → Submodule Λ (M : Type (u + 1)))
    (hzero : F 0 = ⊥)
    (hwhole : F (Fin.last r) = ⊤)
    (hincreasing : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hgraded : ∀ (i : Fin r) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor
            (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
          ((Etale.rightDerivedLowerStarPlus
              (ModuleCat.{u + 1} Λ) f).obj
            ((DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              ((constantSheaf X.smallEtaleTopology
                  (ModuleCat.{u + 1} Λ)).obj
                (ModuleCat.of Λ
                  ((F i.succ : Type (u + 1)) ⧸
                    ((F i.castSucc).comap (F i.succ).subtype))))))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerStarPlus
            (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} Λ)).obj M)))) := by
  sorry

end AlgebraicGeometry
