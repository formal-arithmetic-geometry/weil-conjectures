module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Degeneration of the Leray comparison for a morphism of sites

Source: Stacks Project, Cohomology on Sites, Lemma 0733
(blueprint: lem-weil-pbc-site-leray-degenerate).

The statement records the Leray comparison in the case where all positive right
derived direct images vanish.  The comparison is represented by a family of
objectwise cohomology morphisms.

The source proof proceeds by choosing an injective resolution of `F`.  The
pushforward of that resolution is an injective resolution because pushforward
is right adjoint to the exact inverse image.  Vanishing of the positive right
derived pushforwards makes this pushed-forward complex exact.  Computing both
cohomology groups from these resolutions identifies them with the homology of
the same section complex. This gives the family of isomorphisms in the Lean
statement. Identification with a specified pullback-counit edge map is not part
of this existential statement.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Push an injective resolution through a left exact, injective-preserving functor
when its higher derived images vanish. The complex and augmentation are constructed
explicitly; kernel preservation treats degree zero, and vanishing treats positive degrees. -/
private noncomputable def mapResolution
    {A B : Type u} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasInjectiveResolutions A]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [T.PreservesInjectiveObjects] {X : A} (I : InjectiveResolution X)
    (h : ∀ q : ℕ, 0 < q → IsZero ((T.rightDerived q).obj X)) :
    InjectiveResolution (T.obj X) where
  cocomplex := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := T.injective_obj_of_injective (I.injective n)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨T.map (I.ι.f 0), by
      change T.map (I.ι.f 0) ≫ T.map (I.cocomplex.d 0 1) = 0
      rw [← T.map_comp, I.ι_f_zero_comp_complex_d, T.map_zero]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      apply (ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by
        change ((CochainComplex.single₀ B).obj (T.obj X)).d 0 1 = 0
        simp) (by
          simp [HomologicalComplex.shortComplexFunctor'])).2
      apply (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).2
      constructor
      convert KernelFork.mapIsLimit _ I.isLimitKernelFork T using 1 <;>
        simp [InjectiveResolution.kernelFork, KernelFork.map,
          HomologicalComplex.shortComplexFunctor']
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact (h (n + 1) (Nat.zero_lt_succ n)).of_iso
          (I.isoRightDerivedObj T (n + 1)).symm
      · exact CochainComplex.exactAt_succ_single_obj _ _⟩

/-- Transfer finite-limit preservation from set-valued to abelian inverse image
using the underlying-sheaf comparison and reflection by the forgetful functor. -/
private theorem pullback_preservesFiniteLimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : D ⥤ C)
    [U.IsContinuous K J]
    [PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback U (Type u) K J)] :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback U AddCommGrpCat.{u} K J) := by
  let L := Functor.sheafPullbackConstruction.sheafPullback U AddCommGrpCat.{u} K J
  let V := sheafCompose J (forget AddCommGrpCat.{u})
  have forget_preserves (T : GrothendieckTopology D) :
      PreservesFiniteLimits (sheafCompose T (forget AddCommGrpCat.{u})) := by
    let : PreservesFiniteLimits
        (sheafCompose T (forget AddCommGrpCat.{u}) ⋙ sheafToPresheaf T (Type u)) :=
      show PreservesFiniteLimits (sheafToPresheaf T AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u})) from
          comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf T (Type u))
  let := forget_preserves K
  obtain ⟨e⟩ := sitePullback_abelian_underlying K J U
  let : PreservesFiniteLimits
      (sheafCompose K (forget AddCommGrpCat.{u}) ⋙
        Functor.sheafPullbackConstruction.sheafPullback U (Type u) K J) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteLimits (L ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  let : PreservesLimitsOfSize.{0, 0} V := by
    let : PreservesLimitsOfSize.{0, 0} (V ⋙ sheafToPresheaf J (Type u)) :=
      show PreservesLimitsOfSize.{0, 0} (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u})) from
          inferInstance
    exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))
  let : ReflectsLimitsOfSize.{0, 0} V := reflectsLimits_of_reflectsIsomorphisms
  exact preservesFiniteLimits_of_reflects_of_preserves L V

/-- If the positive right derived direct images of a sheaf vanish, the Leray
comparison from the cohomology of its direct image to the cohomology upstairs is
 an isomorphism in every degree.

Source: Stacks Project, Cohomology on Sites, Lemma 0733(1), using Lemmas
072Z and 0730 (blueprint: lem-weil-pbc-site-leray-degenerate).

(blueprint: lem-weil-pbc-site-leray-degenerate) -/
theorem siteLeray_degenerate
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (U : D ⥤ C)
    [U.IsContinuous K.toGrothendieck J.toGrothendieck]
    [PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback U
      (Type u) K.toGrothendieck J.toGrothendieck)]
    [PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback U
      (Type u) K.toGrothendieck J.toGrothendieck)]
    [(Functor.sheafPullbackConstruction.sheafPullback U AddCommGrpCat.{u}
      K.toGrothendieck J.toGrothendieck).Additive]
    [(Functor.sheafPushforwardContinuous U AddCommGrpCat.{u}
      K.toGrothendieck J.toGrothendieck).Additive]
    [HasExt (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    [HasExt (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (he : ∀ (q : ℕ), 0 < q →
      IsZero (((Functor.sheafPushforwardContinuous U AddCommGrpCat.{u}
        K.toGrothendieck J.toGrothendieck).rightDerived q).obj F)) :
    ∃ e : ∀ (p : ℕ) (V : D),
      Sheaf.H' ((Functor.sheafPushforwardContinuous U AddCommGrpCat.{u}
        K.toGrothendieck J.toGrothendieck).obj F) p V ⟶
      Sheaf.H' F p (U.obj V),
      ∀ (p : ℕ) (V : D), IsIso (e p V) := by
  classical
  let T := U.sheafPushforwardContinuous AddCommGrpCat.{u}
    K.toGrothendieck J.toGrothendieck
  let L := Functor.sheafPullbackConstruction.sheafPullback U AddCommGrpCat.{u}
    K.toGrothendieck J.toGrothendieck
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U AddCommGrpCat.{u}
    K.toGrothendieck J.toGrothendieck
  let : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits J.toGrothendieck K.toGrothendieck U
  let : T.PreservesInjectiveObjects :=
    adj.preservesInjectiveObjects_of_preservesFiniteLimits
  let : PreservesLimitsOfSize.{0, 0} T := adj.rightAdjoint_preservesLimits
  let I := injectiveResolution F
  let P := mapResolution T I he
  let BigK (p : ℕ) (V : D) := Sheaf.H' (T.obj F) p V
  let BigJ (p : ℕ) (V : D) := Sheaf.H' F p (U.obj V)
  have comparison (p : ℕ) (V : D) : Nonempty (BigK p V ≅ BigJ p V) := by
    let XK := (presheafToSheaf K.toGrothendieck AddCommGrpCat.{u}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free)
    let XJ := (presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj
      (yoneda.obj (U.obj V) ⋙ AddCommGrpCat.free)
    let largeK : BigK p V ≃+ CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor _ 0).obj XK) P.cochainComplex p :=
      P.extAddEquivCohomologyClass
    let largeJ : BigJ p V ≃+ CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor _ 0).obj XJ) I.cochainComplex p :=
      I.extAddEquivCohomologyClass
    let : HasExt.{u} (Sheaf K.toGrothendieck AddCommGrpCat.{u}) :=
      hasExt_of_enoughInjectives _
    let : HasExt.{u} (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
      hasExt_of_enoughInjectives _
    let smallK : Sheaf.H'.{u} (T.obj F) p V ≃+
        CochainComplex.HomComplex.CohomologyClass
          ((CochainComplex.singleFunctor _ 0).obj XK) P.cochainComplex p :=
      P.extAddEquivCohomologyClass
    let smallJ : Sheaf.H'.{u} F p (U.obj V) ≃+
        CochainComplex.HomComplex.CohomologyClass
          ((CochainComplex.singleFunctor _ 0).obj XJ) I.cochainComplex p :=
      I.extAddEquivCohomologyClass
    let EK := sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op V)
    let EJ := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (U.obj V))
    obtain ⟨eK⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
      K.toGrothendieck V p
    obtain ⟨eJ⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
      J.toGrothendieck (U.obj V) p
    let c : T ⋙ EK ≅ EJ := Iso.refl _
    let ec := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).mapIso
      ((Functor.mapHomologicalComplexCompIso c (.up ℕ)).app I.cocomplex)
    let e := eK.app (T.obj F) ≪≫ P.isoRightDerivedObj EK p ≪≫ ec ≪≫
      (I.isoRightDerivedObj EJ p).symm ≪≫ (eJ.app F).symm
    exact ⟨(largeK.trans (smallK.symm.trans
      (e.addCommGroupIsoToAddEquiv.trans (smallJ.trans largeJ.symm)))).toAddCommGrpIso⟩
  refine ⟨fun p V => (comparison p V).some.hom, ?_⟩
  intro p V
  exact (comparison p V).some.isIso_hom

end CategoryTheory
