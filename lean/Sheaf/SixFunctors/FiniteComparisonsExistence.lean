/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData
import Sheaf.SixFunctors.FiniteOperationComparisons
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport

/-! # Section preserving finite realizations and operation comparisons

Source: Stacks 00YV and 03D7.
(blueprint: lem-sf-finite-comparisons-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace SheafOfModules.OpenTensorNormalization

/-- Restrict scalars along the locally bijective constant-section map. The
existing restriction equivalence has an additive inverse. Its counit gives the
underlying-sheaf comparison, whose componentwise A-linearity is precisely the
required constant-scalar equation. -/
private theorem finite_realization_exists (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) i]
    [Presheaf.IsLocallySurjective (ProEt.topology X) i] :
    Nonempty (FiniteRealization A X R i) := by
  let J := ProEt.topology X
  let R' := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let α := Functor.whiskerRight i (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallyInjective J α := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J (Functor.whiskerRight i
      (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  have : Presheaf.IsLocallySurjective J α := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J α).mpr
    change Presheaf.IsLocallySurjective J (Functor.whiskerRight i
      (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  let F := ringUnitRestriction A J R' α
  have : F.IsEquivalence := ringUnitRestriction_equivalence A J R' α
  have : F.Additive := { map_add := by intros; ext W m; rfl }
  have : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  let e := F.asEquivalence.symm
  have : e.functor.Additive := Equivalence.inverse_additive F.asEquivalence
  let h : e.functor ⋙ toSheaf R' ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
    Functor.isoWhiskerRight F.asEquivalence.counitIso
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))
  refine ⟨{ equivalence := e, underlying := h, scalar := ?_ }⟩
  intro M W a x
  exact ((F.asEquivalence.counitIso.hom.app M).hom.app W).hom.map_smul a x

/-- The inverse underlying-sheaf comparison also preserves constant scalars. -/
private theorem finite_inverse_scalar
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (M : FiniteModules A X) (W : X.ProEtᵒᵖ)
    (a : A) (x : M.obj.obj W) :
    (e.underlying.inv.app M).hom.app W (a • x) =
      @SMul.smul
        (((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj W)
        ((e.equivalence.functor.obj M).val.obj W) inferInstance (i.app W a)
        ((e.underlying.inv.app M).hom.app W x) := by
  apply (ConcreteCategory.bijective_of_isIso ((e.underlying.hom.app M).hom.app W)).1
  have h (y : M.obj.obj W) : (e.underlying.hom.app M).hom.app W
      ((e.underlying.inv.app M).hom.app W y) = y := by
    exact ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (e.underlying.inv_hom_id_app M)) W) y
  rw [e.scalar, h, h]
  rfl

/-- Lift the underlying direct-image comparison to module sheaves using local
surjectivity of constants, and retain its identity on underlying sections. -/
private theorem finite_direct_pin_exists (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    (k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology Y) i]
    (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology .ordinary Y) (topology .ordinary X)).obj S)
    (hc : ∀ (W : Y.ProEtᵒᵖ) (a : A),
      c.hom.app W (i.app W a) = k.app ((baseChange .ordinary f).op.obj W) a)
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k) :
    ∃ e : ProEtale.lowerStar (ModuleCat.{u + 1} A) f ⋙ eR.equivalence.functor ≅
        eS.equivalence.functor ⋙ direct .ordinary f R S c,
      ∀ (M : FiniteModules A X) (W : Y.ProEtᵒᵖ)
        (x : (eR.equivalence.functor.obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).val.obj W),
        (eS.underlying.hom.app M).hom.app ((baseChange .ordinary f).op.obj W)
          ((e.hom.app M).val.app W x) =
        (eR.underlying.hom.app
          ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).hom.app W x := by
  let L := ProEtale.lowerStar (ModuleCat.{u + 1} A) f ⋙ eR.equivalence.functor
  let G := eS.equivalence.functor ⋙ direct .ordinary f R S c
  let T := toSheaf ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let α := Functor.whiskerRight i (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallySurjective (ProEt.topology Y) α := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology Y)
      (Functor.whiskerRight i (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  have : Presheaf.IsLocallySurjective (topology .ordinary Y) α :=
    inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology Y) α)
  let h : L ⋙ T ≅ G ⋙ T :=
    Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} A) f) eR.underlying ≪≫
      Functor.isoWhiskerRight eS.underlying.symm (ProEtale.lowerStar AddCommGrpCat.{u + 1} f)
  let g (M : FiniteModules A X) : L.obj M ⟶ G.obj M :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α (G.obj M).isSheaf).symm
      (PresheafOfModules.homMk (h.hom.app M).hom (fun W a x ↦ by
        change (eS.underlying.inv.app M).hom.app ((baseChange .ordinary f).op.obj W)
          ((eR.underlying.hom.app _).hom.app W
            (@SMul.smul
              (((sheafCompose (ProEt.topology Y)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj W)
              ((L.obj M).val.obj W) inferInstance (i.app W a) x)) =
          @SMul.smul
            (((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj.obj
                ((baseChange .ordinary f).op.obj W))
            ((eS.equivalence.functor.obj M).val.obj ((baseChange .ordinary f).op.obj W))
            inferInstance (c.hom.app W (i.app W a))
            ((eS.underlying.inv.app M).hom.app ((baseChange .ordinary f).op.obj W)
              ((eR.underlying.hom.app _).hom.app W x))
        rw [eR.scalar, hc]
        exact finite_inverse_scalar eS M ((baseChange .ordinary f).op.obj W) a _))⟩
  have hg (M : FiniteModules A X) : T.map (g M) = h.hom.app M := rfl
  let t : L ⟶ G :=
    { app := g
      naturality := fun {M N} b ↦ by
        apply T.map_injective
        simp only [Functor.map_comp, hg]
        exact h.hom.naturality b }
  have ht (M : FiniteModules A X) : IsIso (t.app M) := by
    have : IsIso (T.map (t.app M)) := by
      change IsIso (T.map (g M))
      rw [hg]
      infer_instance
    exact isIso_of_reflects_iso _ T
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, ?_⟩
  intro M W x
  change (eS.underlying.hom.app M).hom.app ((baseChange .ordinary f).op.obj W)
    ((eS.underlying.inv.app M).hom.app ((baseChange .ordinary f).op.obj W)
      ((eR.underlying.hom.app _).hom.app W x)) = _
  exact ConcreteCategory.congr_hom (congr_app
    (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
      (eS.underlying.inv_hom_id_app M)) ((baseChange .ordinary f).op.obj W)) _
/-- The inverse mate of the direct comparison is invertible because both
realizations are equivalences. The general unit-mate identity supplies its pin. -/
private theorem finite_ordinary_pull_pin_exists
    {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S)
    (p : Pullback R S (direct .ordinary f R S c))
    (right : FiniteDirectPin eR eS f c) : Nonempty (FiniteOrdinaryPullPin eR eS f c p) := by
  let a := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b : TwoSquare (ProEtale.lowerStar (ModuleCat.{u + 1} A) f)
      eS.equivalence.functor eR.equivalence.functor (direct .ordinary f R S c) :=
    TwoSquare.mk _ _ _ _ right.val.hom
  have : IsIso b.natTrans := inferInstanceAs (IsIso right.val.hom)
  have : IsIso ((mateEquiv a p.adjunction).symm b).natTrans :=
    inverseMate_isIso_of_equivalences a p.adjunction b
  let ordinary := (asIso ((mateEquiv a p.adjunction).symm b).natTrans).symm
  let iso : eR.equivalence.inverse ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙ eS.equivalence.functor) ≅
      p.ordinary :=
    Functor.isoWhiskerLeft eR.equivalence.inverse ordinary ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eR.equivalence.counitIso p.ordinary ≪≫
      Functor.leftUnitor _
  have : PreservesFiniteLimits p.ordinary := preservesFiniteLimits_of_natIso iso
  have : PreservesFiniteColimits p.ordinary := preservesFiniteColimits_of_natIso iso
  have := p.universal
  let e := Functor.leftDerivedUnique p.ordinary.mapDerivedCategory p.derived p.epsilon
    p.ordinary.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (AlgebraicGeometry.Scheme.ProjectionRestriction.Mod R) (.up ℤ))
  have he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      p.ordinary.mapDerivedCategoryFactorsh.hom = p.epsilon := by
    simp [e]
  have : IsIso p.epsilon := by
    rw [← he]
    infer_instance
  refine ⟨{
    right := right
    ordinary := ordinary
    mate := ?_
    limits := inferInstance
    colimits := inferInstance
    derivedExact := inferInstance }⟩
  intro M
  exact unit_mateEquiv_symm a p.adjunction b M

/-- The canonical coefficient direct image sends a constant section to itself. -/
private theorem constant_direct_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.ProEtᵒᵖ) (a : A) :
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom.app W
      ((toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app W a) =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
        ((baseChange .ordinary f).op.obj W) a := by
  have hn := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  change _ ≫ (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
    (CommRingCat.of A)).hom = _ at hn
  exact ConcreteCategory.congr_hom (congr_app hn W) a

/-- The same constant-section identity holds for the literal corner coefficient
map, by naturality of the sheafification unit along the site comparison. -/
private theorem corner_constant_direct_unit (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    (t : SiteSquare (finiteInput A gU j' j g sq)) (W : U.ProEtᵒᵖ) (a : A) :
    (cornerCoefficient t).hom.app W
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
          ((@openInclusion .ordinary U X j sq.isOpenImmersion).op.obj W) a) =
    (toSheafify (ProEt.topology X')
      ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))).app
        ((@openInclusion .ordinary U' X' j' sq.isOpenImmersion').op.obj
          ((baseChange .ordinary gU).op.obj W)) a := by
  change (((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj
      (CommRingCat.of A)).obj.map (t.iso.inv.app W.unop).op)
    ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)).hom.app _
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app _ a)) = _
  rw [constant_direct_unit]
  have hn := (toSheafify (ProEt.topology X')
    ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))).naturality
      (t.iso.inv.app W.unop).op
  exact (ConcreteCategory.congr_hom hn a).symm


/-- Finite comparison records exist independently of the normalization assertion.

Proof: on X and X' the sheafification unit is locally bijective. Its restriction
to either open is locally bijective because open composition is cocontinuous.
Apply scalar restriction and its inverse equivalence to construct all four
realizations. The counit preserves the underlying additive sheaf and constant
scalar multiplication. Construct both direct-image comparisons by lifting their
underlying-sheaf identifications along scalar restriction. Local surjectivity
of constant sections makes the lifted maps coefficient-linear. The canonical
ambient coefficient map preserves constants by the sheafification adjunction;
its literal corner restriction does so by naturality of the sheafification unit.
The inverse underlying comparison preserves scalars, hence these maps are linear
on constants and therefore on all sections. Their normalization follows by
cancelling the underlying-sheaf isomorphisms. Take the inverse adjunction mates:
they are invertible because both realizations are equivalences, and the general
unit-mate identity gives their exact pin equations. Transporting exact fixed
inverse image through the equivalences proves exactness of both ordinary ringed
pullbacks. Uniqueness of left derived functors identifies their specified derived
counits with composites of isomorphisms, making those counits invertible on every
complex. Extend these realizations and pins to the remaining derived, open and
tensor comparisons by finite_operation_comparisons_exists.
Source: Stacks 00YV, 03D7, 0F6Z, 06YU.
(blueprint: lem-sf-finite-comparisons-existence) -/
theorem finite_comparisons_exists (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) : Nonempty (FiniteComparisons A o) := by
  have : IsOpenImmersion j := sq.isOpenImmersion
  have : IsOpenImmersion j' := sq.isOpenImmersion'
  have : (proEtaleOpenComposition j).IsCocontinuous
      (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have : (proEtaleOpenComposition j').IsCocontinuous
      (ProEt.topology U') (ProEt.topology X') :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j')
  let R := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let S := (constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let i := toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
  let k := toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))
  have : Presheaf.IsLocallyInjective (ProEt.topology U)
      (Functor.whiskerLeft (openInclusion .ordinary j).op i) :=
    Presheaf.isLocallyInjective_whisker (ProEt.topology U) (ProEt.topology X)
      (proEtaleOpenComposition j) i
  have : Presheaf.IsLocallySurjective (ProEt.topology U)
      (Functor.whiskerLeft (openInclusion .ordinary j).op i) :=
    Presheaf.isLocallySurjective_whisker (ProEt.topology U) (ProEt.topology X)
      (proEtaleOpenComposition j) i
  have : Presheaf.IsLocallyInjective (ProEt.topology U')
      (Functor.whiskerLeft (openInclusion .ordinary j').op k) :=
    Presheaf.isLocallyInjective_whisker (ProEt.topology U') (ProEt.topology X')
      (proEtaleOpenComposition j') k
  have : Presheaf.IsLocallySurjective (ProEt.topology U')
      (Functor.whiskerLeft (openInclusion .ordinary j').op k) :=
    Presheaf.isLocallySurjective_whisker (ProEt.topology U') (ProEt.topology X')
      (proEtaleOpenComposition j') k
  obtain ⟨rX⟩ := finite_realization_exists A X R i
  obtain ⟨rX'⟩ := finite_realization_exists A X' S k
  obtain ⟨rU⟩ := finite_realization_exists A U (restrictRing .ordinary j R)
    (Functor.whiskerLeft (openInclusion .ordinary j).op i)
  obtain ⟨rU'⟩ := finite_realization_exists A U' (restrictRing .ordinary j' S)
    (Functor.whiskerLeft (openInclusion .ordinary j').op k)
  obtain ⟨right, hr⟩ := finite_direct_pin_exists A g _ _ i k
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A))
    (constant_direct_unit A g) rX rX'
  obtain ⟨rightU, hrU⟩ := finite_direct_pin_exists A gU
    (restrictRing .ordinary j R) (restrictRing .ordinary j' S)
    (Functor.whiskerLeft (openInclusion .ordinary j).op i)
    (Functor.whiskerLeft (openInclusion .ordinary j').op k)
    (cornerCoefficient t) (corner_constant_direct_unit A gU j' j g sq t) rU rU'
  obtain ⟨pull⟩ := finite_ordinary_pull_pin_exists rX rX' g
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A))
    o.gPull ⟨right, hr⟩
  obtain ⟨pullU⟩ := finite_ordinary_pull_pin_exists rU rU' gU
    (cornerCoefficient t) o.gUPull ⟨rightU, hrU⟩
  obtain ⟨e, _⟩ := finite_operation_comparisons_exists A gU j' j g sq o rX rX' rU rU'
    pull pullU
  exact ⟨e⟩

end SheafOfModules.OpenTensorNormalization
