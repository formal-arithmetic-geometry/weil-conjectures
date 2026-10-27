/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Module.Torsion.Basic
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-! # Constructibility after passing to a finite quotient coefficient ring

Source: Stacks Project, Modules on Sites, Tags 093I and 093J; the quotient-label
argument in the proof of blueprint thm-exc-explicit-preservation, paragraph 2
(blueprint: lem-exc-finite-quotient-constructible-reduction).

The second conclusion preserves the specified stratification and every specified
cover member, including empty members, and uses the actual quotient label M/IM.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restriction along the canonical quotient coefficient map, with the original
sections and restriction maps. Source: Stacks 093I and the quotient-label argument
(blueprint: lem-exc-finite-quotient-constructible-reduction). -/
abbrev proEtaleQuotientRestrict (T : Scheme.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantRingMap (T := T) (Ideal.Quotient.mk I)))

/-- The actual quotient M/IM as a module over the lifted quotient ring. First restrict
M along A → ULift A, form the Mathlib quotient by I times the top submodule, and
restrict its canonical A/I-action along ULift (A/I) → A/I. Thus no action or label
is chosen from an existence theorem. Source: Stacks 093I, quotient-label construction
(blueprint: lem-exc-finite-quotient-constructible-reduction). -/
def proEtaleQuotientLabel (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    ModuleCat.{u + 1} (ULift.{u + 1, u} (A ⧸ I)) :=
  letI : Module A M := Module.compHom M ULift.ringEquiv.symm.toRingHom
  let Q := M ⧸ (I • (⊤ : Submodule A M))
  letI : Module (ULift.{u + 1, u} (A ⧸ I)) Q :=
    Module.compHom Q ULift.ringEquiv.toRingHom
  ModuleCat.of (ULift.{u + 1, u} (A ⧸ I)) Q

private theorem coefficientSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (proEtaleConstantRingMap (T := Y) a) ≫ proEtaleCoefficientInverseImageMap f B =
    proEtaleCoefficientInverseImageMap f A ≫ proEtaleConstantRingMap (T := X) a := by
  let D := CommRingCat.{u + 1}
  let q := CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} a)
  have hρ : proEtaleConstantRingMap (T := Y) a ≫ proEtaleCoefficientDirectImageMap f B =
      proEtaleCoefficientDirectImageMap f A ≫
        (proEtaleSheafDirectImage f D).map (proEtaleConstantRingMap (T := X) a) := by
    apply ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).injective
    change ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _)
        ((presheafToSheaf (ProEt.topology Y) D).map
          ((Functor.const Y.ProEtᵒᵖ).map q) ≫ proEtaleCoefficientDirectImageMap f B) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    change (Functor.const Y.ProEtᵒᵖ).map q ≫
        ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _)
          (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _) =
      ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _)
          (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _) ≫ _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (Functor.const Y.ProEtᵒᵖ).map q ≫
        Functor.whiskerLeft (proEtaleBaseChange f).op
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj _)) = _
    apply NatTrans.ext
    funext V
    exact (congrArg (fun k ↦ k.app ((proEtaleBaseChange f).op.obj V))
      (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map q)))
  apply ((proEtaleSheafAdjunction f D).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change proEtaleConstantRingMap (T := Y) a ≫
      (proEtaleSheafAdjunction f D).homEquiv _ _
        (((proEtaleSheafAdjunction f D).homEquiv _ _).symm
          (proEtaleCoefficientDirectImageMap f B)) = _
  rw [Equiv.apply_symm_apply]
  change _ = (proEtaleSheafAdjunction f D).homEquiv _ _
      (((proEtaleSheafAdjunction f D).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap f A)) ≫ _
  rw [Equiv.apply_symm_apply]
  exact hρ

private noncomputable def transportPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) :=
  (SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleConstantRingComparison.{u} f A).inv)).obj
    ((proEtaleModuleInverseImage f (proEtaleConstantRing Y A)).obj F)

private noncomputable def pullbackTransportIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    proEtaleConstantModulePullback f A F ≅ transportPullback f A F := by
  let c := proEtaleConstantRingComparison f A
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let a := proEtaleRingExtensionAdjunction f (proEtaleConstantRing Y A)
    (proEtaleConstantRing X A) c
  exact (a.leftAdjointUniq e.symm.toAdjunction).app
    ((proEtaleModuleInverseImage f (proEtaleConstantRing Y A)).obj F)

private noncomputable def pullbackRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (I : Ideal A)
    (F : proEtaleRingModules Y (proEtaleConstantRing Y (A ⧸ I))) :
    proEtaleConstantModulePullback f A ((proEtaleQuotientRestrict Y A I).obj F) ≅
      (proEtaleQuotientRestrict X A I).obj (proEtaleConstantModulePullback f (A ⧸ I) F) := by
  let qY := proEtaleConstantRingMap (T := Y) (Ideal.Quotient.mk I)
  let qX := proEtaleConstantRingMap (T := X) (Ideal.Quotient.mk I)
  let cA := proEtaleConstantRingComparison f A
  let cB := proEtaleConstantRingComparison f (A ⧸ I)
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let P := (proEtaleModuleInverseImage f (proEtaleConstantRing Y (A ⧸ I))).obj F
  let E := SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cA.inv)
  let e := E.mapIso (AlgebraicGeometry.ProEtaleTensorComparison.scalarIdentification f qY F)
  have h : cA.inv ≫ L.map qY = qX ≫ cB.inv := by
    apply (cancel_mono cB.hom).mp
    rw [Category.assoc, show L.map qY ≫ cB.hom = cA.hom ≫ qX from
      coefficientSquare f (Ideal.Quotient.mk I), ← Category.assoc, cA.inv_hom_id,
      Category.id_comp, Category.assoc, cB.inv_hom_id, Category.comp_id]
  let d : E.obj
      ((AlgebraicGeometry.ProEtaleTensorComparison.restrict (L.map qY)).obj P) ≅
      (proEtaleQuotientRestrict X A I).obj (transportPullback f (A ⧸ I) F) := by
    apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
    · let l : (E.obj
          ((AlgebraicGeometry.ProEtaleTensorComparison.restrict (L.map qY)).obj P)).val.obj U ≃ₗ[
            (proEtaleConstantRing X A).obj.obj U]
          ((proEtaleQuotientRestrict X A I).obj (transportPullback f (A ⧸ I) F)).val.obj U :=
        { toFun := id
          invFun := id
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' := by
            intro r m
            change (L.map qY).hom.app U (cA.inv.hom.app U r) • (show P.val.obj U from m) =
              cB.inv.hom.app U (qX.hom.app U r) • (show P.val.obj U from m)
            exact congrArg (fun s ↦ s • (show P.val.obj U from m))
              (ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) h) r) }
      exact l.toModuleIso
    · intros
      ext m
      rfl
  exact pullbackTransportIso f A _ ≪≫ e ≪≫ d ≪≫
    (proEtaleQuotientRestrict X A I).mapIso (pullbackTransportIso f (A ⧸ I) F).symm

private noncomputable abbrev ringUnit (T : Scheme.{u}) (A : Type u)
    [CommRing A] (U : T.ProEt) :=
  Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
private noncomputable abbrev ringMap (T : Scheme.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (U : T.ProEt) :=
  Functor.whiskerLeft (Over.forget U).op
    (((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantRingMap (T := T) (Ideal.Quotient.mk I))).hom)

private theorem ringUnit_naturality (T : Scheme.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (U : T.ProEt) (V : (Over U)ᵒᵖ)
    (a : ULift.{u + 1, u} A) :
    (ringMap T A I U).app V ((ringUnit T A U).app V a) =
      (ringUnit T (A ⧸ I) U).app V ((RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk I)) a) := by
  have h := congrArg (fun k ↦ k.app ((Over.forget U).op.obj V))
    (toSheafify_naturality (J := ProEt.topology T) (D := CommRingCat.{u + 1})
      ((Functor.const T.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk I)))))
  exact (ConcreteCategory.congr_hom h a).symm

set_option maxHeartbeats 700000 in
-- Elaborate both restricted actions and the two sheafification adjunctions.
private theorem quotientChart (T : Scheme.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (G : proEtaleRingModules T (proEtaleConstantRing T (A ⧸ I))) (U : T.ProEt)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (e : ((proEtaleQuotientRestrict T A I).obj G).over U ≅
      proEtaleConstantModuleSheafOver T A U M) :
    Nonempty (G.over U ≅ proEtaleConstantModuleSheafOver T (A ⧸ I) U
      (proEtaleQuotientLabel.{u} A I M)) := by
  let J := (ProEt.topology T).over U
  let R := ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)).over U
  let B := ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing T (A ⧸ I))).over U
  let α := ringUnit T A U
  let β := ringUnit T (A ⧸ I) U
  let q := ringMap T A I U
  let : EssentiallySmall.{u + 1} (Over U) := essentiallySmallSelf.{0} _
  let : HasSheafify J AddCommGrpCat.{u + 1} := hasSheafifyEssentiallySmallSite _ _
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := (proEtaleConstantRingUnit_over_locallyBijective T A U).1
  have := (proEtaleConstantRingUnit_over_locallyBijective T A U).2
  have := (proEtaleConstantRingUnit_over_locallyBijective T (A ⧸ I) U).1
  have := (proEtaleConstantRingUnit_over_locallyBijective T (A ⧸ I) U).2
  let P := proEtaleConstantModulePresheaf (Over U) A M
  let Q := proEtaleConstantModulePresheaf (Over U) (A ⧸ I)
    (proEtaleQuotientLabel.{u} A I M)
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} (J := J) (R := R) α).unit.app P
  let k := η ≫ (PresheafOfModules.restrictScalars α).map e.inv.val
  let : Module A M := Module.compHom M ULift.ringEquiv.symm.toRingHom
  let N := I • (⊤ : Submodule A M)
  have hk (V : (Over U)ᵒᵖ) (a : A) (m : M) :
      k.app V (ULift.up.{u + 1} a • m) =
        β.app V (ULift.up.{u + 1} (Ideal.Quotient.mk I a)) •
          (show (G.over U).val.obj V from k.app V m) := by
    have h := (k.app V).hom.map_smul (ULift.up.{u + 1} a) m
    change k.app V (ULift.up.{u + 1} a • m) =
      q.app V (α.app V (ULift.up.{u + 1} a)) • (show (G.over U).val.obj V from k.app V m) at h
    rw [ringUnit_naturality] at h
    exact h
  let kA (V : (Over U)ᵒᵖ) := (k.app V).hom.toAddMonoidHom
  have hN (V : (Over U)ᵒᵖ) : N.toAddSubgroup ≤ (kA V).ker := by
    intro m hm
    change k.app V m = 0
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro a ha m _
      change k.app V (ULift.up.{u + 1} a • m) = 0
      rw [hk, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      change β.app V 0 • (show (G.over U).val.obj V from k.app V m) = 0
      rw [map_zero, zero_smul]
    · intro x y hx hy
      simp only [map_add, hx, hy, add_zero]
  let t (V : (Over U)ᵒᵖ) := QuotientAddGroup.lift N.toAddSubgroup (kA V) (hN V)
  let g : Q ⟶ (PresheafOfModules.restrictScalars β).obj (G.over U).val :=
    { app V := ModuleCat.ofHom (X := Q.obj V)
        (Y := ((PresheafOfModules.restrictScalars β).obj (G.over U).val).obj V)
        { toFun := t V
          map_add' := (t V).map_add
          map_smul' := by
            intro b x
            obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
            obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N x
            obtain ⟨b⟩ := b
            dsimp at ha
            subst ha
            exact hk V a m }
      naturality := by
        intro V W f
        ext x
        obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N x
        exact PresheafOfModules.naturality_apply k f m }
  let γ := (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (J := J) (R := B) (P := Q) (F := G.over U) β).symm g
  let c : P.presheaf ⟶ Q.presheaf :=
    { app _ := AddCommGrpCat.ofHom N.mkQ.toAddMonoidHom
      naturality := by intros; rfl }
  have hfac : c ≫ (PresheafOfModules.toPresheaf _).map g =
      (PresheafOfModules.toPresheaf _).map k := rfl
  have : Presheaf.IsLocallySurjective J c :=
    Presheaf.isLocallySurjective_of_surjective J c (fun _ ↦ N.mkQ_surjective)
  have he : IsIso ((PresheafOfModules.toPresheaf _).map e.inv.val) := by
    change IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map e.inv)
    infer_instance
  have hk' : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map k) ∧
      Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map k) := by
    change Presheaf.IsLocallyInjective J
        (toSheafify J P.presheaf ≫ (PresheafOfModules.toPresheaf _).map e.inv.val) ∧
      Presheaf.IsLocallySurjective J
        (toSheafify J P.presheaf ≫ (PresheafOfModules.toPresheaf _).map e.inv.val)
    constructor <;> infer_instance
  have := hk'.1
  have := hk'.2
  have : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map g) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J _ hfac
  have : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map g) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have hg : J.W ((PresheafOfModules.toPresheaf _).map g) := J.W_of_isLocallyBijective _
  have : IsIso γ := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf B)]
    dsimp only [γ]
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
      Adjunction.homEquiv_counit]
    have : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
        ((PresheafOfModules.toPresheaf _).map g)) := by
      rw [J.W_eq_inverseImage_isomorphisms] at hg
      exact hg
    exact IsIso.comp_isIso' this
      (isIso_sheafificationAdjunction_counit (J := J) (D := AddCommGrpCat.{u + 1})
        ((SheafOfModules.toSheaf B).obj (G.over U)))
  exact ⟨(asIso γ).symm⟩

private theorem quotientLabelFinite (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) [Finite M] :
    Finite (proEtaleQuotientLabel A I M) := by
  let : Module A M := Module.compHom M ULift.ringEquiv.symm.toRingHom
  exact Finite.of_surjective (I • (⊤ : Submodule A M)).mkQ
    (Submodule.mkQ_surjective _)

private theorem restrictStalkFinite (T : Scheme.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (F : proEtaleRingModules T (proEtaleConstantRing T (A ⧸ I)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T)
    (h : Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T A)
      ((proEtaleQuotientRestrict T A I).obj F))) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T (A ⧸ I)) F) := by
  exact h

set_option linter.unusedVariables false in
/-- A quotient-module sheaf constructible over A is intrinsically constructible over
A/I. Every witnessing stratification and chosen finite-label trivializing cover gives
quotient-label charts over A/I on the very same members.
Source: Stacks 093J, lemma-constant-exact; blueprint thm-exc-explicit-preservation,
proof paragraph 2 (blueprint: lem-exc-finite-quotient-constructible-reduction).

Proof: (1) For each stratum immersion, the canonical constant-ring comparisons are
isomorphisms by lem-pur-proetale-constant-coefficient-comparison. They commute with
A → A/I since both adjoint maps send a constant a to its quotient constant section;
use def-weil-pbc-sheafification. The action formula in def-weil-proetale-inverse-image
then identifies pullback of scalar restriction with scalar restriction of pullback.
Localization commutes with scalar restriction sectionwise.
(2) Retain the given strata and covers from def-weil-proetale-constructible-sheaf
and def-weil-proetale-locally-constant-sheaf. For a chart with label M set Q = M/IM,
with its canonical quotient-ring action.
(3) The chart kills each constant sum of elements a*m with a in I, since its image
is the sum of q(a) times the corresponding sections. Sheafification uniqueness shows
that the inclusion of the constant sheaf of IM is zero. This does not say IM = 0.
(4) On the localized site identify its own constant ring with the restricted ring,
using lem-pur-ring-presheaf-sheafification-localization. Apply
lem-weil-pbc-finite-type-constant-exact to 0 → IM → M → Q → 0. The first arrow is
zero by (3), so the constant quotient map is an isomorphism of A-module sheaves.
The underlying abelian constant sheaf of Q is independent of the coefficient ring,
by lem-cbc-sieve-module-sheafification.
(5) On constant units define [m] ↦ alpha(m). This is well defined by (3) and
A/I-linear by lifting a scalar to A. The module-sheafification adjunction extends
it to an A/I-linear map; uniqueness identifies its underlying map with the
isomorphism of (4). Its inverse is linear as well.
(6) Repeat on the original covers. Restriction of scalars preserves underlying
geometric stalk sets by def-weil-proetale-geometric-stalk, hence their finiteness.
The same finite partition proves constructibility. Each Q is finite as a quotient
of finite M. On empty members the same maps are maps of zero sheaves, so arbitrary
labels are permitted there without asserting IM = 0. No Tor or complex is used. -/
theorem finiteQuotient_constructible_reduction
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] (I : Ideal A)
    (F : proEtaleRingModules T (proEtaleConstantRing T (A ⧸ I)))
    (hF : IsConstructibleProEtaleModuleSheaf T A
      ((proEtaleQuotientRestrict T A I).obj F)) :
    @IsConstructibleProEtaleModuleSheaf T (A ⧸ I) _
      (Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective) F ∧
    ∀ (S : Stratification T), 0 < S.n →
      (∀ (i : Fin S.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A
            ((proEtaleQuotientRestrict T A I).obj F)))) →
      ∀ (J : Fin S.n → Type (u + 1))
        (U : ∀ i : Fin S.n, J i → (S.domain i).ProEt)
        (f : ∀ (i : Fin S.n) (j : J i), U i j ⟶ ProEt.mk (𝟙 (S.domain i))),
        (∀ i : Fin S.n,
          Presieve.ofArrows (U i) (f i) ∈ (ProEt.precoverage (S.domain i)).coverings _) →
        ∀ (M : ∀ (i : Fin S.n) (j : J i), ModuleCat.{u + 1} (ULift.{u + 1, u} A)),
          (∀ (i : Fin S.n) (j : J i), Finite (M i j)) →
          (∀ (i : Fin S.n) (j : J i),
            Nonempty ((proEtaleConstantModulePullback (S.immersion i) A
              ((proEtaleQuotientRestrict T A I).obj F)).over (U i j) ≅
                proEtaleConstantModuleSheafOverOfUniverses (S.domain i) A (U i j) (M i j))) →
          ∀ (i : Fin S.n) (j : J i),
            Finite (proEtaleQuotientLabel A I (M i j)) ∧
            Nonempty ((proEtaleConstantModulePullback (S.immersion i) (A ⧸ I) F).over
              (U i j) ≅ proEtaleConstantModuleSheafOverOfUniverses (S.domain i) (A ⧸ I)
                (U i j) (proEtaleQuotientLabel A I (M i j))) := by
  have charts (S : Stratification T) (i : Fin S.n) (U : (S.domain i).ProEt)
      (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (e : (proEtaleConstantModulePullback (S.immersion i) A
          ((proEtaleQuotientRestrict T A I).obj F)).over U ≅
        proEtaleConstantModuleSheafOver (S.domain i) A U M) :
      Nonempty ((proEtaleConstantModulePullback (S.immersion i) (A ⧸ I) F).over U ≅
        proEtaleConstantModuleSheafOver (S.domain i) (A ⧸ I) U
          (proEtaleQuotientLabel A I M)) := by
    let p := pullbackRestrictIso (S.immersion i) A I F
    let e' := (SheafOfModules.overFunctor _ U).mapIso p.symm ≪≫ e
    exact quotientChart (S.domain i) A I _ U M e'
  constructor
  · obtain ⟨S, hn, hdata⟩ := hF
    refine ⟨S, hn, fun i ↦ ⟨?_, ?_⟩⟩
    · obtain ⟨J, U, f, hc, hm⟩ := (hdata i).1
      refine ⟨J, U, f, hc, fun j ↦ ?_⟩
      obtain ⟨M, ⟨e⟩⟩ := hm j
      exact ⟨proEtaleQuotientLabel A I M, charts S i (U j) M e⟩
    · intro Ω _ _ y
      let p := pullbackRestrictIso (S.immersion i) A I F
      let E := geometricRingModuleStalkFunctor y (proEtaleConstantRing (S.domain i) A)
      have hsrc : Finite (E.obj (proEtaleConstantModulePullback (S.immersion i) A
          ((proEtaleQuotientRestrict T A I).obj F))) := (hdata i).2 Ω y
      have h : Finite (E.obj ((proEtaleQuotientRestrict (S.domain i) A I).obj
          (proEtaleConstantModulePullback (S.immersion i) (A ⧸ I) F))) :=
        Finite.of_injective (E.mapIso p.symm).toLinearEquiv
          (E.mapIso p.symm).toLinearEquiv.injective
      exact restrictStalkFinite (S.domain i) A I _ y h
  · intro S hn hst J U f hc M hm he i j
    have := hm i j
    exact ⟨quotientLabelFinite A I (M i j), charts S i (U i j) (M i j) (he i j).some⟩

end AlgebraicGeometry.Scheme
