/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Formal closed support for arbitrary condensed rings

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-adjunction, clauses (1)--(4)
(blueprint: det-lem-formal-closed-support-adjunction).

The inverse coefficient comparison is used to transport the module action. In particular
no commutativity, constructibility or boundedness hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- Modules over the actual pulled-back coefficient ring, including noncommutative rings.
Source: blueprint opening paragraph (blueprint: det-lem-formal-closed-support-adjunction). -/
abbrev FormalSupportModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The module category is Grothendieck abelian without a commutativity hypothesis.
Source: blueprint proof Step 6 (blueprint: det-lem-formal-closed-support-adjunction). -/
instance formalSupportModules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (FormalSupportModules Λ X) :=
  Mod.isGrothendieckAbelian.{u + 1} (condensedRingObj Λ X)

/-- Inverse image followed by transport of the action along the canonical coefficient iso.
Source: blueprint opening paragraph and proof Steps 1--2
(blueprint: det-lem-formal-closed-support-adjunction). -/
def formalSupportPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormalSupportModules Λ Y ⥤ FormalSupportModules Λ X :=
  (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse

/-- The canonical module adjunction, obtained by lifting the sheaf adjunction and
transporting scalars. Source: blueprint proof Step 2
(blueprint: det-lem-formal-closed-support-adjunction). -/
def formalSupportPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    formalSupportPullback Λ f ⊣ lowerStar Λ f :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).comp
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm.toAdjunction).ofNatIsoRight
      (comapPullbackHomCompIso Λ f)

/-- The transported inverse image is additive.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
instance formalSupportPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (formalSupportPullback Λ f).Additive :=
  inferInstanceAs ((_ ⋙ Mod.comap (asIso (condensedPullbackHom Λ f)).inv).Additive)

/-- Exactness of inverse image on the underlying abelian sheaves and scalar transport.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
instance formalSupportPullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (formalSupportPullback Λ f) :=
  inferInstanceAs (PreservesFiniteLimits (_ ⋙
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse))

/-- Cokernels commute with inverse image and scalar transport.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
instance formalSupportPullback_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (formalSupportPullback Λ f) :=
  inferInstanceAs (PreservesFiniteColimits (_ ⋙
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).inverse))

/-- The kernel of the open adjunction unit, on objects and morphisms.
Source: blueprint clause (1), generalizing def-exc-proetale-sections-with-support
(blueprint: det-lem-formal-closed-support-adjunction). -/
def formalSupportKernel {V X : Scheme.{u}} (j : V ⟶ X) :
    FormalSupportModules Λ X ⥤ FormalSupportModules Λ X where
  obj M := kernel ((formalSupportPullbackAdjunction Λ j).unit.app M)
  map f := kernel.map _ _ f
    ((lowerStar Λ j).map ((formalSupportPullback Λ j).map f))
    ((formalSupportPullbackAdjunction Λ j).unit.naturality f).symm
  map_id M := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- The support kernel respects addition, by the universal property of the kernel.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
instance formalSupportKernel_additive {V X : Scheme.{u}} (j : V ⟶ X) :
    (formalSupportKernel Λ j).Additive where
  map_add := equalizer.hom_ext (by simp [formalSupportKernel])

/-- The closed support functor is exactly i* ker(id → j*j*).
Source: blueprint opening formula (blueprint: det-lem-formal-closed-support-adjunction). -/
def formalClosedSupport {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    FormalSupportModules Λ X ⥤ FormalSupportModules Λ Z :=
  formalSupportKernel Λ j ⋙ formalSupportPullback Λ i

/-- Additivity of the displayed support formula.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
instance formalClosedSupport_additive {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    (formalClosedSupport Λ i j).Additive :=
  inferInstanceAs ((formalSupportKernel Λ j ⋙ formalSupportPullback Λ i).Additive)

/-- The canonical support-kernel inclusion.
Source: blueprint clause (1) (blueprint: det-lem-formal-closed-support-adjunction). -/
def formalSupportKernelInclusion {V X : Scheme.{u}} (j : V ⟶ X) :
    formalSupportKernel Λ j ⟶ 𝟭 (FormalSupportModules Λ X) where
  app M := kernel.ι ((formalSupportPullbackAdjunction Λ j).unit.app M)
  naturality _ _ f := by simp [formalSupportKernel]

/-- The canonical closed unit on the support kernel; clause (1) says it is invertible.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
def formalSupportKernelComparison {Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) :
    formalSupportKernel Λ j ⟶ formalClosedSupport Λ i j ⋙ lowerStar Λ i :=
  Functor.whiskerLeft (formalSupportKernel Λ j)
    (formalSupportPullbackAdjunction Λ i).unit

/-- Sections with closed support, all four clauses, for arbitrary condensed coefficients.
The Hom-complex clause uses global abelian-group-valued Hom, on K-injective targets.
The last clause describes the fibre without selecting a cone in a triangulated category:
it holds for every distinguished fibre triangle of the specified open adjunction unit.

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-adjunction (1)--(4)
(blueprint: det-lem-formal-closed-support-adjunction).

Proof:
1. Identify inverse-image coefficient rings by lem-sfb-alpha-iso. Lift inverse/direct
   image to module actions; the lifted sheaf adjunction restricts to linear maps.
   Exactness is detected on underlying abelian kernels and sheafified cokernels
   (def-weil-sheaf-of-modules-category, lem-weil-pbc-site-pullback-abelian-exact).
2. Apply lem-weil-pbc-proetale-ringed-open-closed to underlying abelian sheaves.
   Its exact closed pushforward, localization sequence and zero cross-restrictions
   lift to modules, since their maps are linear. Closed pushforward is fully faithful.
   The open slice calculation in lem-weil-proetale-weakly-etale-localization makes
   j*j_* the identity and the restricted open unit invertible.
3. The kernel of the open unit has zero open restriction. Its closed unit is therefore
   invertible by the localization sequence. Every map i_*A -> M factors uniquely
   through this kernel. Full faithfulness gives the sheaf adjunction and identifies
   its counit with the kernel inclusion under that unit. A right adjoint preserves
   finite limits, proving left exactness (clause 1).
4. Module sheaves are Grothendieck abelian (lem-weil-pbc-ring-sheaves-grothendieck).
   Use lem-pur-kinjective-degreewise-existence for unbounded K-injective resolutions
   with injective terms. Total derivation is computed there by
   lem-weil-pbc-kinjective-total-derived. The exact closed pushforward descends
   termwise by lem-sf-exact-functor-derived-triangulated; its right adjoint sends
   K-injectives to K-injectives by lem-weil-pbc-right-adjoint-preserves-kinjective.
5. The termwise Hom adjunction descends to homotopy categories by
   lem-weil-pbc-termwise-adjunction-homotopy. Compute Hom into K-injectives using
   lem-weil-pbc-kinjective-hom-derived to obtain the derived adjunction (clause 2).
   Apply the ordinary adjunction in every component of the product Hom complex.
   Naturality intertwines d_I f - (-1)^n f d_A. These are global Hom complexes,
   and K-injectivity makes them compute global derived Hom, not internal sheaf Hom.
6. For injective I, the composite j!j*I -> I -> j*j*I is monic: both its open and
   closed restricted kernels vanish. Extend j!j*I -> I across that monomorphism
   by injectivity (def-sp-injective-resolutions). Its extension is a section of
   the open unit, as can be checked after open restriction; open direct image is
   fully faithful. Hence the open unit is epi (clause 3).
7. Resolve K by K-injective I with injective terms. Exact j! makes j*I K-injective.
   The canonical degreewise sequence 0 -> i_*Gamma(I) -> I -> j*j*I -> 0 is short
   exact by steps 3 and 6. Apply lem-weil-pbc-complex-ses-triangle. Its first two
   arrows are the exceptional counit and open unit, giving clause 4.
8. The sequence and its connecting arrow are natural. Maps between K-injective
   resolutions represent all derived maps, and homotopic maps induce the same
   derived arrows (lem-weil-pbc-kinjective-hom-derived), so naturality descends.
   The canonical map from the kernel complex to Cone(I -> j*j*I)[-1], n -> (0,n),
   is a quasi-isomorphism: locally lift the first fibre coordinate, subtract its
   boundary, and obtain a kernel cocycle; the same lifting detects boundaries.
   Apply exact i* and i*i_* = id for the fibre formula. Any other distinguished
   fibre triangle is isomorphic to this one by the identity on its last two terms.
-/
theorem formal_closed_support_adjunction
    {X Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{w} (FormalSupportModules Λ X)]
    [HasDerivedCategory.{w} (FormalSupportModules Λ Z)]
    [HasDerivedCategory.{w} (FormalSupportModules Λ V)] :
    IsIso (formalSupportKernelComparison Λ i j) ∧
    PreservesFiniteLimits (formalClosedSupport Λ i j) ∧
    ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
      (∀ M : FormalSupportModules Λ X,
        (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
          (formalSupportKernelInclusion Λ j).app M) ∧
      (∀ (I : FormalSupportModules Λ X) [Injective I],
        Epi ((formalSupportPullbackAdjunction Λ j).unit.app I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        CochainComplex.IsKInjective
          (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        IsIso ((formalClosedSupport Λ i j).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ∧
      (∀ (A : CochainComplex (FormalSupportModules Λ Z) ℤ)
        (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        ∃ e : CochainComplex.HomComplex
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
          CochainComplex.HomComplex A
            (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
          ∀ (n : ℤ) (f : CochainComplex.HomComplex.Cochain
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
            (p q : ℤ) (hpq : p + n = q),
            (((e.hom.f n).hom f).v p q hpq) =
              a.homEquiv (A.X p) (I.X q) (f.v p q hpq)) ∧
      Exists fun [hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
        ∃ (b : (lowerStar Λ i).mapDerivedCategory ⊣
            (formalClosedSupport Λ i j).rightDerivedFunctor)
          (c : (formalSupportPullback Λ j).mapDerivedCategory ⊣
            (lowerStar Λ j).rightDerivedFunctor),
          ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
              (lowerStar Λ j).rightDerivedFunctor ⟶
            (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory ⋙
                shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
            b = a.mapDerivedCategoryRightDerivedAdjunction ∧
            c = (formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction ∧
            (∀ K : DerivedCategory (FormalSupportModules Λ X),
              Triangle.mk (b.counit.app K) (c.unit.app K) (δ.app K) ∈ distTriang _) ∧
            (∀ (K F : DerivedCategory (FormalSupportModules Λ X)) (s : F ⟶ K)
              (t : (lowerStar Λ j).rightDerivedFunctor.obj
                ((formalSupportPullback Λ j).mapDerivedCategory.obj K) ⟶ F⟦(1 : ℤ)⟧),
              Triangle.mk s (c.unit.app K) t ∈ distTriang _ →
              Nonempty ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K ≅
                (formalSupportPullback Λ i).mapDerivedCategory.obj F)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
