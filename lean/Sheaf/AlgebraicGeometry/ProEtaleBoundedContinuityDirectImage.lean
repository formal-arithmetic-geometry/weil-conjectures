/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Bounded-below filtered-colimit continuity of pro-etale direct images

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
`det-pe-bounded-continuity-direct-image.md` (blueprint:
`det-pe-bounded-continuity-direct-image`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The standard localization of module complexes at quasi-isomorphisms, as in the
recorded derived category of an abelian category.
Source: Stacks Project, Tag 05RU (blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable instance ringModuleSheaves_hasDerivedCategory {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The module direct image over the direct-image coefficient sheaf.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable def ringModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ⥤
      SheafOfModules.{u + 1} ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := topology Y) (K := topology X)
    (S := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
    (R := R) (𝟙 _)

noncomputable instance ringModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (ringModuleDirectImage f R).Additive :=
  ⟨by intros; rfl⟩

/-- K-injective resolutions exist for sheaves of modules over the pro-etale ringed site.
Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: det-pe-bounded-continuity-direct-image).
Proof: transport the site to `proEtaleSiteModel X`, which only enlarges the Hom universe.
There `SheafOfModules.isGrothendieckAbelian` applies to the transported ring sheaf, so
`CochainComplex.kInjectiveResolutionFunctor` gives K-injective quasi-isomorphic
resolutions. Transport back along the inverse sectionwise equivalence, which preserves
acyclicity, homotopies and quasi-isomorphisms. No commutativity, boundedness or
finiteness condition is imposed. -/
theorem ringModuleDirectImage_hasKInjectiveResolutions {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    ∀ L : CochainComplex (SheafOfModules.{u + 1} R) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u + 1} R) ℤ) (s : L ⟶ I),
        I.IsKInjective ∧ QuasiIso s := by
  sorry

/-- The right derived module direct image.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable abbrev ringDerivedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)) :=
  Functor.rightDerivedFunctorOfQuasiIsoResolutions (ringModuleDirectImage f R)
    (by
      let h := ringModuleDirectImage_hasKInjectiveResolutions R
      exact fun L : CochainComplex (SheafOfModules.{u + 1} R) ℤ ↦
        h L)

/-- The higher direct image in degree `q`.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable abbrev ringHigherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤
      SheafOfModules.{u + 1}
        ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  ringDerivedDirectImage f R ⋙
    DerivedCategory.homologyFunctor _ q

/-- For a quasi-compact, quasi-separated morphism, higher direct images commute with
filtered colimits of complexes sharing a common lower bound.
Source: the Weil conjectures blueprint, snapshot main-20261015,
`det-pe-bounded-continuity-direct-image.md` (blueprint: det-pe-bounded-continuity-direct-image).
Proof:
1. Fix `q`. For a complex `L` vanishing below `a` put `P_L(V) = H^q(X ×_Y V, L)`, an
   abelian presheaf on `Y_proet`, with base change and direct image those of
   det-pe-topos-functoriality-inverse-image. By lem-pe-bounded-complex-direct-image-presheaf,
   `P_L^# ≅ R^q f_* L` as abelian sheaves, naturally in `L`.
2. For affine `V` in `Y_proet`, `V` is qcqs (lem-weil-pbc-affine-scheme-qcqs); the base
   change `U = X ×_Y V → V` is qcqs and so `U` is qcqs
   (lem-weil-pbc-qcqs-morphism-permanence, parts (3) and (2)).
3. The termwise colimit `K` of the diagram vanishes below `a`; module-sheaf colimits have
   the abelian-sheaf colimits as underlying sheaves
   (lem-weil-pbc-module-sheaves-colimits-forgetful). Functoriality gives
   `φ : colim_i P_{K_i} ⟶ P_K` (sectionwise colimit); on affine `V`, `φ(V)` is the
   comparison of det-pe-bounded-continuity-sections at `U`, hence bijective.
4. Affine objects cover every object (det-pe-wcb-cover), so `φ` is locally injective and
   locally surjective and `φ^#` is an isomorphism
   (lem-weil-pbc-site-sheafification-iso-locally-bijective). Sheafification commutes with
   colimits (lem-weil-pbc-site-module-presheaf-sheafification-exact, constant ring `Z`);
   via Step 1, `φ^#` is on each colimit leg the map induced by `K_i ⟶ K`, i.e. the
   canonical comparison displayed below. -/
theorem boundedContinuityDirectImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (R : Sheaf (topology X) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (SheafOfModules.{u + 1} R) ℤ)
    (a : ℤ) (hD : ∀ i : I, ∀ n : ℤ, n < a → IsZero ((D.obj i).X n)) (q : ℤ) :
    IsIso (colimit.desc
      ((D ⋙ DerivedCategory.Q) ⋙ ringHigherDirectImage f R q)
      ((ringHigherDirectImage f R q).mapCocone
        (DerivedCategory.Q.mapCocone (colimit.cocone D)))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
