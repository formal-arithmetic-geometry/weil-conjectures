/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Sheaf.AlgebraicGeometry.FlatModulePullbackExact
public import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The flat base-change map on sections

Source: Stacks Project, Cohomology, Tags 02N7, 01E4 and 01FB
(blueprint: lem-weil-pbc-flat-base-change-map-sections).
-/

@[expose] public section

universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives


/-- Flat pullback preserves finite limits, from the recorded exactness theorem.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
instance flatBaseChangePullbackLimits {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    PreservesFiniteLimits (tensorPullback g) :=
  (flat_module_pullback_exact_pushforward_injective g).1.1

/-- Flat pullback preserves finite colimits, from the recorded exactness theorem.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
instance flatBaseChangePullbackColimits {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    PreservesFiniteColimits (tensorPullback g) :=
  (flat_module_pullback_exact_pushforward_injective g).1.2

/-- Additivity follows from preservation of finite biproducts.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
instance flatBaseChangePullbackAdditive {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    (tensorPullback g).Additive := Functor.additive_of_preserves_binary_products _

/-- The sectionwise comparison of the two composites of direct images in a square.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangePushforwardSquare {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) :
    pushforward (pullback.snd g f) ⋙ pushforward f ≅
      pushforward (pullback.fst g f) ⋙ pushforward g :=
  pushforwardComp (pullback.snd g f) f ≪≫
    pushforwardCongr (pullback.condition (f := g) (g := f)).symm ≪≫
      (pushforwardComp (pullback.fst g f) g).symm

/-- Push the augmented lift down along f, and use the sectionwise square comparison.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangeResolutionQ {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) :
    ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶
      ((pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((pushforward (pullback.fst g f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex) :=
  ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).map t ≫
    (NatIso.mapHomologicalComplex (flatBaseChangePushforwardSquare f g)
      (ComplexShape.up ℕ)).hom.app J.cocomplex

/-- The termwise adjoint c of q, with the canonical tensor-pullback adjunction.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangeResolutionC {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) :=
  ((Classical.choose (exists_tensorPullbackAdjunction g)).mapHomologicalComplex
    (ComplexShape.up ℕ)).homEquiv _ _ |>.symm (flatBaseChangeResolutionQ f g I J t)

/-- H^p(c), with exact pullback's homology comparison and the resolution comparisons.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def flatBaseChangeResolutionBeta {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (p : ℕ) :
    (tensorPullback g).obj (((pushforward f).rightDerived p).obj F) ⟶
      ((pushforward (pullback.fst g f)).rightDerived p).obj
        ((tensorPullback (pullback.snd g f)).obj F) :=
  (tensorPullback g).map (I.isoRightDerivedObj (pushforward f) p).hom ≫
    (((((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).sc p).mapHomologyIso (tensorPullback g)).inv ≫
    (HomologicalComplex.homologyFunctor S'.Modules (ComplexShape.up ℕ) p).map
      (flatBaseChangeResolutionC f g I J t) ≫
    (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv

/-- The canonical class map into R^p f_*F, using the restricted source resolution.
Source: Stacks, Tag 01E4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def FlatBaseChangeOpenChoices.sourceClass {X S S' : Scheme.{uBC}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)} {V : S.Opens}
    (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :=
  resolutionSectionClass D.source.resolution
    (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    V D.source.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V

/-- The canonical class map into R^p f'_*F', using the restricted target resolution.
Source: Stacks, Tag 01E4 (blueprint: lem-weil-pbc-flat-base-change-map-sections). -/
def FlatBaseChangeOpenChoices.targetClass {X S S' : Scheme.{uBC}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)} {V : S.Opens}
    (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :=
  resolutionSectionClass D.target.resolution
    (((pushforward (pullback.fst g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) (g ⁻¹ᵁ V) (D.target.sections ≪≫
      eqToIso (congrArg (fun U => ((RingedSpace.openModuleSections
        (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex) (flatBaseChangeOpenEquality f g V))) p ≫
    Hom.app (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv (g ⁻¹ᵁ V)

/-- The base-change map constructed from resolutions is independent of the resolutions
and augmented lifts. Its adjoint sends the canonical image of a class on f⁻¹V to the
canonical image of its pullback along g' restricted to g'⁻¹(f⁻¹V).
The local pullback is written as the recorded cohomology h-map of the restricted unit;
the unit square identifies its target with the restriction of g'^*F.
Source: Stacks, Tags 02N7, 01E4, 01FB
(blueprint: lem-weil-pbc-flat-base-change-map-sections).

Proof: (1) Injective resolutions exist by lem-weil-pbc-scheme-modules-enough-injectives.
Flat pushforward preserves injectives by
lem-weil-pbc-flat-module-pullback-exact-pushforward-injective, so
lem-weil-pbc-lift-along-injective-quasi-iso supplies t with the prescribed augmentation.
Two such t are homotopic by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.
The pushforward square is the sectionwise comparison; termwise adjunction preserves
homotopies by lem-weil-pbc-termwise-adjunction-homotopy. Comparison lifts between
resolutions and their homotopy inverses prove the first equality for every choice.
(2) Restrict I and J to U = f⁻¹V and W = g'⁻¹U. Restriction preserves resolutions by
lem-weil-pbc-module-open-restriction-injectives. Restrict the unit sectionwise;
on each open it is m ↦ 1 ⊗ m. The restricted unit square gives psi and the canonical
identification h^*(F|U) ≅ F'|W. These resolutions and the section identifications give
FlatBaseChangeOpenChoices for every V.
(3) Restrict t to U. In def-weil-pbc-module-cohomology-fmap choose a resolution lambda
of h_*(J|W) and comparison lambda times the restricted t.
By lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso, H(Γlambda) is invertible.
Thus H(Γlambda) inverse times H(Γlambda times q_V) is H(q_V), so this is the
recorded cohomology pullback. A cocycle s maps to t(s).
(4) Restrictions commute with t, hence with H(q_V). The canonical theta maps of
lem-weil-pbc-higher-direct-image-presheaf turn these into a presheaf map to
 g_*R^p f'_*F'. Sheafification gives its unique extension.
(5) q = g_*c times the unit. Exactness of g^* identifies the homology of the pulled-back
complex with g^* of its homology. Locally represent a cohomology-sheaf section by a
cocycle s: the adjoint of H(c) takes [s] to [c(unit(s))] = [q(s)]. Therefore it is
that unique extension. Substituting step (3) proves the displayed section formula. -/
theorem flatBaseChangeMap_sections {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] (F : X.Modules) (p : ℕ) :
    ∃ beta : (tensorPullback g).obj (((pushforward f).rightDerived p).obj F) ⟶
        ((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F),
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
        (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex),
        I.ι.f 0 ≫ t.f 0 =
          (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
            (pushforward (pullback.snd g f)).map (J.ι.f 0) →
        flatBaseChangeResolutionBeta f g I J t p = beta) ∧
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens),
        Nonempty (FlatBaseChangeOpenChoices f g F I J V)) ∧
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _ beta) V
          (D.sourceClass p xi) =
        D.targetClass p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
