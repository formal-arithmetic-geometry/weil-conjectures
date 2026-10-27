/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.DerivedSectionsScalarCoherence
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-! # Natural Leray spectral sequence on ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 0732 and 0733; Derived Categories,
Tag 015N (blueprint: lem-sfb-ringed-site-leray-spectral-sequence).

All pages and filtration objects live in the functor category on source module sheaves.
The global-sections comparison is normalized by the geometric adjunction on global elements.
The edge formula holds for every injective resolution, using its canonical derived comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CoefficientDerivedSections

-- This existing theorem supplies the intrinsic Grothendieck structure, hence resolutions.
attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace CategoryTheory

/-- The natural first-quadrant module Leray sequence with its finite abutment filtration
and resolution-independent left edge.
Source: Stacks Project, Tags 0732, 0733 and 015N
(blueprint: lem-sfb-ringed-site-leray-spectral-sequence).

Proof:
1. Module sheaves are Grothendieck abelian by lem-weil-pbc-ring-sheaves-grothendieck;
   lem-sp-grothendieck-enough-injectives supplies their injective resolutions. Work in
   the common coefficient universe; abelian groups are Grothendieck as well.
2. The module adjunction (lem-weil-pbc-ringed-topoi-module-adjunction) makes f.modules
   left exact, and its given scalar action makes it additive. Global sections is additive
   and left exact. The geometric adjunction and preservation of the terminal sheaf identify
   target global sections after direct image with source global sections. Normalize this
   identification on global elements by adjunction, as in the first three equations below.
3. Lemma lem-sfb-ringed-topos-injective-pushforward-global-acyclic supplies precisely
   the composite acyclicity condition (def-sp-composite-acyclicity). No injectivity of
   pushed-forward modules and no exact tensor pullback is asserted.
4. Apply thm-sp-grothendieck to f.modules and target global sections. Its second page
   is R^a Gamma_D(R^b f_*), naturally in the source module. Identify the abutment with
   R^(a+b) Gamma_C using the normalized global-sections comparison from step 2.
   Lemma lem-pc-grothendieck-ss-double-complex-model identifies the CE model and edges.
5. The first-quadrant double-complex convergence theorem
   thm-sp-double-complex-spectral-sequences gives the decreasing finite image filtration:
   top at zero, bottom at n+1, and graded pieces the stable pages. All constructions are
   natural, so the filtration and graded isomorphisms lie in the functor category.
6. There are no incoming differentials in column zero. The cycles-to-homology projection
   and the spectral sequence's page isomorphism therefore define the canonical inclusions
   of successive column-zero terms. Iteration gives j, with j_2 the identity. The edge
   is the quotient to the zeroth graded piece followed by its stable-page inclusion.
7. Lemma lem-pc-grothendieck-edge-cocycle describes the same edge by applying global
   sections to cycles and their homology quotient. Lemma lem-sp-derived-well-defined
   supplies the canonical comparisons for every injective resolution. The final equations
   therefore express exactly the global-cocycle formula and resolution independence.
-/
theorem exists_ringedSite_leray_spectralSequence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) :
    ∃ (t : f.modules ⋙ coefficientSections B ≅ coefficientSections A)
      (zC : ∀ M : coefficientModules A,
        (coefficientSections A).obj M →
          (⊤_ (Sheaf J (Type u)) ⟶
            (sheafCompose J (forget AddCommGrpCat)).obj ((SheafOfModules.toSheaf _).obj M)))
      (zD : ∀ M : coefficientModules B,
        (coefficientSections B).obj M →
          (⊤_ (Sheaf K (Type u)) ⟶
            (sheafCompose K (forget AddCommGrpCat)).obj ((SheafOfModules.toSheaf _).obj M))),
      (∀ (M : coefficientModules A) (x : (coefficientSections A).obj M)
        (U : Cᵒᵖ) (s : (⊤_ (Sheaf J (Type u))).obj.obj U),
        (zC M x).hom.app U s =
          (Sheaf.ΓRes ((SheafOfModules.toSheaf _).obj M) U) x) ∧
      (∀ (M : coefficientModules B) (x : (coefficientSections B).obj M)
        (U : Dᵒᵖ) (s : (⊤_ (Sheaf K (Type u))).obj.obj U),
        (zD M x).hom.app U s =
          (Sheaf.ΓRes ((SheafOfModules.toSheaf _).obj M) U) x) ∧
      (∀ (M : coefficientModules A) (x : (coefficientSections B).obj (f.modules.obj M)),
        (f.adj.homEquiv _ _)
          (terminal.from (f.inverse.obj (⊤_ (Sheaf K (Type u)))) ≫
            zC M (t.hom.app M x)) =
          zD (f.modules.obj M) x ≫ f.underlying.hom.app M) ∧
      ∃ (E : E₂CohomologicalSpectralSequenceNat (coefficientModules A ⥤ AddCommGrpCat.{u}))
        (e₂ : ∀ a b : ℕ, (E.page 2).X (a, b) ≅
          f.modules.rightDerived b ⋙ (coefficientSections B).rightDerived a)
        (T : ∀ n : ℕ, DecreasingFiltration ((coefficientSections A).rightDerived n)),
        (∀ n : ℕ, (T n).step 0 = ⊤ ∧ (T n).step (n + 1) = ⊥) ∧
        (∀ a b : ℕ, ∀ (r : ℤ) (hr : 2 ≤ r),
          max (a : ℤ) ((b : ℤ) + 1) < r →
            Nonempty ((E.page r hr).X (a, b) ≅ E.pageInfinity (a, b))) ∧
        ∃ (g : ∀ (n a b : ℕ), a + b = n →
            ((T n).gradedPiece (a : ℤ) ≅ E.pageInfinity (a, b)))
          (j : ∀ (n : ℕ) (r : ℤ) (_hr : 2 ≤ r),
            (E.page r).X (0, n) ⟶ (E.page 2).X (0, n)),
          (∀ n : ℕ, j n 2 (by omega) = 𝟙 _) ∧
          (∀ (n : ℕ) (r : ℤ) (hr : 2 ≤ r), Mono (j n r hr)) ∧
          (∀ (n : ℕ) (r : ℤ) (hr : 2 ≤ r),
            (E.page r).homologyπ (0, n) ≫ (E.iso r (r + 1) (0, n)).hom ≫
                j n (r + 1) (by omega) =
              (E.page r).iCycles (0, n) ≫ j n r hr) ∧
          ∃ (q : ∀ n : ℕ,
              (coefficientSections A).rightDerived n ⟶ (T n).gradedPiece 0)
            (edge : ∀ n : ℕ,
              (coefficientSections A).rightDerived n ⟶
                f.modules.rightDerived n ⋙ coefficientSections B),
            (∀ n : ℕ, ((T n).step 0).arrow ≫ q n =
              cokernel.π (Subobject.ofLE ((T n).step 1) ((T n).step 0)
                ((T n).antitone_step (by omega)))) ∧
            (∀ n : ℕ, edge n = q n ≫ (g n 0 n (by omega)).hom ≫
              j n (0 + n + 2 : ℕ) (by omega) ≫ (e₂ 0 n).hom ≫
                Functor.whiskerLeft (f.modules.rightDerived n)
                  (coefficientSections B).rightDerivedZeroIsoSelf.hom) ∧
            (∀ (M : coefficientModules A) (I : InjectiveResolution M) (n : ℕ),
              ∃ c : (coefficientSections B).obj
                  (((f.modules.mapHomologicalComplex (ComplexShape.up ℕ)).obj
                    I.cocomplex).cycles n) ⟶
                  (((coefficientSections A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                    I.cocomplex).cycles n,
                c ≫ (((coefficientSections A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                    I.cocomplex).iCycles n =
                  (coefficientSections B).map
                    (((f.modules.mapHomologicalComplex (ComplexShape.up ℕ)).obj
                      I.cocomplex).iCycles n) ≫ t.hom.app (I.cocomplex.X n) ∧
                c ≫ (((coefficientSections A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                    I.cocomplex).homologyπ n ≫
                    (I.isoRightDerivedObj (coefficientSections A) n).inv ≫
                    (edge n).app M ≫
                    (coefficientSections B).map (I.isoRightDerivedObj f.modules n).hom =
                  (coefficientSections B).map
                    (((f.modules.mapHomologicalComplex (ComplexShape.up ℕ)).obj
                      I.cocomplex).homologyπ n)) := by
  sorry

end CategoryTheory
