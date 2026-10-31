/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Meromorphic modules

Source: Stacks Project, Divisors, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module).

We sheafify the localizations of module sections at sections regular at every stalk.
For an invertible module this is canonically the tensor product with the meromorphic sheaf.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing Mathlib submonoid of sections whose germs are non-zero-divisors.
Source: Stacks, Tag 01X2 (blueprint: def-sc-meromorphic-module). -/
noncomputable abbrev meromorphicDenominators (X : Scheme.{u}) (U : X.Opens) :=
  (X.presheaf.submonoidPresheafOfStalk fun x ↦ nonZeroDivisors (X.presheaf.stalk x)).obj (op U)

/-- Restriction in Mathlib's existing submonoid presheaf. Source: Stacks, Tag 01X2
(blueprint: def-sc-meromorphic-module). -/
noncomputable def restrictMeromorphicDenominator (X : Scheme.{u}) {U V : X.Opens}
    (i : V ⟶ U) (b : meromorphicDenominators X U) : meromorphicDenominators X V :=
  ⟨X.presheaf.map i.op b.val,
    (X.presheaf.submonoidPresheafOfStalk fun x ↦ nonZeroDivisors (X.presheaf.stalk x)).map
      i.op b.property⟩

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: restriction preserves regular denominators. The localization universal property extends
restriction uniquely, sending m/b to res(m)/res(b); equality of fractions is preserved since
its annihilating denominator restricts to a regular denominator. -/
theorem exists_meromorphicRestriction (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    ∃ f : LocalizedModule (meromorphicDenominators X U) Γ(M, U) →ₛₗ[
        (X.presheaf.map i.op).hom]
        LocalizedModule (meromorphicDenominators X V) Γ(M, V),
      ∀ (m : Γ(M, U)) (b : meromorphicDenominators X U),
        f (LocalizedModule.mk m b) =
          LocalizedModule.mk (M.presheaf.map i.op m) (restrictMeromorphicDenominator X i b) := by
  let f : LocalizedModule (meromorphicDenominators X U) Γ(M, U) →
      LocalizedModule (meromorphicDenominators X V) Γ(M, V) := fun z ↦
    LocalizedModule.liftOn z
      (fun p ↦ LocalizedModule.mk (M.presheaf.map i.op p.1)
        (restrictMeromorphicDenominator X i p.2)) (by
      rintro ⟨m, b⟩ ⟨n, c⟩ ⟨a, h⟩
      apply LocalizedModule.mk_eq.mpr
      refine ⟨restrictMeromorphicDenominator X i a, ?_⟩
      have h' := congrArg (M.presheaf.map i.op) h
      simpa only [Submonoid.smul_def, AlgebraicGeometry.Scheme.Modules.map_smul,
        restrictMeromorphicDenominator] using h')
  have hf (m : Γ(M, U)) (b : meromorphicDenominators X U) :
      f (LocalizedModule.mk m b) =
        LocalizedModule.mk (M.presheaf.map i.op m)
          (restrictMeromorphicDenominator X i b) := by
    exact LocalizedModule.liftOn_mk _ _ _
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro z w
    induction z using LocalizedModule.induction_on with | h m b =>
      induction w using LocalizedModule.induction_on with | h n c =>
        simp only [LocalizedModule.mk_add_mk, hf]
        congr 1
        · change M.val.map i.op ((c : Γ(X, U)) • m + (b : Γ(X, U)) • n) = _
          rw [map_add, M.val.map_smul, M.val.map_smul]
          rfl
        · apply Subtype.ext
          exact map_mul _ _ _
  · intro r z
    induction z using LocalizedModule.induction_on with | h m b =>
      simp only [LocalizedModule.smul'_mk, hf]
      congr 1
      exact M.val.map_smul i.op r m

/-- The canonical restriction of localized sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicRestriction (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (exists_meromorphicRestriction X M i).choose

private theorem meromorphicRestriction_mk (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U))
    (b : meromorphicDenominators X U) :
    meromorphicRestriction X M i (LocalizedModule.mk m b) =
      LocalizedModule.mk (M.presheaf.map i.op m)
        (restrictMeromorphicDenominator X i b) :=
  (exists_meromorphicRestriction X M i).choose_spec m b

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: on m/b, restriction by the identity fixes numerator and denominator; every localized
section is a fraction. -/
theorem meromorphicRestriction_id (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (z : LocalizedModule (meromorphicDenominators X U) Γ(M, U)) :
    meromorphicRestriction X M (𝟙 U) z = z := by
  induction z using LocalizedModule.induction_on with | h m b =>
    rw [meromorphicRestriction_mk]
    congr 1
    · simp
    · apply Subtype.ext
      simp [restrictMeromorphicDenominator]

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: both maps send m/b to its iterated restriction, by the presheaf laws for M and O_X;
every localized section is a fraction. -/
theorem meromorphicRestriction_comp (X : Scheme.{u}) (M : X.Modules)
    {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (z : LocalizedModule (meromorphicDenominators X U) Γ(M, U)) :
    meromorphicRestriction X M (j ≫ i) z =
      meromorphicRestriction X M j (meromorphicRestriction X M i z) := by
  induction z using LocalizedModule.induction_on with | h m b =>
    simp only [meromorphicRestriction_mk]
    congr 1
    · exact M.val.map_comp_apply i.op j.op m
    · apply Subtype.ext
      simp [restrictMeromorphicDenominator, ← CommRingCat.comp_apply,
        ← Functor.map_comp]

/-- The presheaf of localized module sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicPresheaf (X : Scheme.{u}) (M : X.Modules) :
    X.PresheafOfModules where
  obj U := ModuleCat.of Γ(X, U.unop)
    (LocalizedModule (meromorphicDenominators X U.unop) Γ(M, U.unop))
  map {U V} i := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, U.unop)
      (LocalizedModule (meromorphicDenominators X U.unop) Γ(M, U.unop)))
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of Γ(X, V.unop)
        (LocalizedModule (meromorphicDenominators X V.unop) Γ(M, V.unop))))
    { toFun := meromorphicRestriction X M i.unop
      map_add' := (meromorphicRestriction X M i.unop).map_add
      map_smul' := (meromorphicRestriction X M i.unop).map_smul' }
  map_id U := by
    ext z
    exact meromorphicRestriction_id X M U.unop z
  map_comp i j := by
    ext z
    exact meromorphicRestriction_comp X M i.unop j.unop z

/-- The meromorphic module is the associated sheaf of localized sections.
Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicModule (X : Scheme.{u}) (M : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (meromorphicPresheaf X M)

/-- Fractions map into the associated sheaf. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicFraction (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    LocalizedModule (meromorphicDenominators X U) Γ(M, U) →ₗ[Γ(X, U)]
      Γ(meromorphicModule X M, U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (meromorphicPresheaf X M)).app (op U) |>.hom

/-- Source: Stacks, Tags 01X2 and 01X4 (blueprint: def-sc-meromorphic-module).
Proof: restriction sends m/1 to res(m)/1, by the defining fraction formula. Thus localization
of ordinary sections is a natural transformation of presheaves of modules. -/
theorem meromorphicLocalization_natural (X : Scheme.{u}) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    meromorphicRestriction X M i (LocalizedModule.mkLinearMap _ _ m) =
      LocalizedModule.mkLinearMap _ _ (M.presheaf.map i.op m) := by
  change meromorphicRestriction X M i (LocalizedModule.mk m 1) =
    LocalizedModule.mk (M.presheaf.map i.op m) 1
  rw [meromorphicRestriction_mk]
  congr 1
  apply Subtype.ext
  exact map_one _

/-- Ordinary sections as meromorphic presheaf sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicLocalization (X : Scheme.{u}) (M : X.Modules) :
    M.val ⟶ meromorphicPresheaf X M where
  app U := ModuleCat.ofHom (X := M.val.obj U) (Y := (meromorphicPresheaf X M).obj U)
    { toFun := LocalizedModule.mkLinearMap (meromorphicDenominators X U.unop) Γ(M, U.unop)
      map_add' := (LocalizedModule.mkLinearMap
        (meromorphicDenominators X U.unop) Γ(M, U.unop)).map_add
      map_smul' := (LocalizedModule.mkLinearMap
        (meromorphicDenominators X U.unop) Γ(M, U.unop)).map_smul' }
  naturality i := by
    ext m
    exact (meromorphicLocalization_natural X M i.unop m).symm

/-- The canonical map from ordinary to meromorphic sections. Source: Stacks, Tags 01X2 and 01X4
(blueprint: def-sc-meromorphic-module). -/
noncomputable def toMeromorphicModule (X : Scheme.{u}) (M : X.Modules) :
    M ⟶ meromorphicModule X M :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimage
    (meromorphicLocalization X M ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (meromorphicPresheaf X M))

/-- The fraction-tensor isomorphism of presheaves, before sheafification.
Source: Stacks, Modules, Tag 01D1 (blueprint: def-sc-meromorphic-module). -/
private noncomputable def meromorphicPresheafTensorIso (X : Scheme.{u}) (M : X.Modules) :
    meromorphicPresheaf X (unit X) ⊗ M.val ≅ meromorphicPresheaf X M := by
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact ((LocalizedModule.equivTensorProduct
      (meromorphicDenominators X U.unop) Γ(M, U.unop)).symm.restrictScalars
        Γ(X, U.unop)).toModuleIso
  · intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro z m
    induction z using LocalizedModule.induction_on with | h a b =>
      change (LocalizedModule.equivTensorProduct
        (meromorphicDenominators X V.unop) Γ(M, V.unop)).symm
          (meromorphicRestriction X (unit X) i.unop (LocalizedModule.mk a b) ⊗ₜ
            M.val.map i m) =
        meromorphicRestriction X M i.unop
          ((LocalizedModule.equivTensorProduct
            (meromorphicDenominators X U.unop) Γ(M, U.unop)).symm
              (LocalizedModule.mk a b ⊗ₜ m))
      rw [meromorphicRestriction_mk]
      change (LocalizedModule.equivTensorProduct
        (meromorphicDenominators X V.unop) Γ(M, V.unop)).symm
          (Localization.mk (X.presheaf.map i a)
            (restrictMeromorphicDenominator X i.unop b) ⊗ₜ M.val.map i m) = _
      rw [LocalizedModule.equivTensorProduct_symm_apply_tmul]
      change _ = meromorphicRestriction X M i.unop
        ((LocalizedModule.equivTensorProduct
          (meromorphicDenominators X U.unop) Γ(M, U.unop)).symm
            (Localization.mk a b ⊗ₜ m))
      rw [LocalizedModule.equivTensorProduct_symm_apply_tmul, map_smulₛₗ,
        meromorphicRestriction_mk]
      rfl

/-- Source: Stacks, Tag 01X4 and Modules, Tag 01D1
(blueprint: def-sc-meromorphic-module).
Proof: sectionwise localization is tensoring with the localized scalar ring, naturally under
restriction. Sheafify this presheaf isomorphism, use the monoidal sheafification tensorator,
and identify the sheafification of M with M by the counit. -/
theorem meromorphicModule_tensor_iso (X : Scheme.{u}) (M : X.Modules) [M.IsInvertible] :
    Nonempty ((meromorphicModule X (unit X) ⊗ M) ≅ meromorphicModule X M) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let : MonoidalCategory (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.monoidalCategory X.sheaf
  let : S.Monoidal := SheafOfModules.sheafificationMonoidal X.sheaf
  exact ⟨(Iso.refl _ ⊗ᵢ
      (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app M).symm ≪≫
    Functor.Monoidal.μIso S (meromorphicPresheaf X (unit X)) M.val ≪≫
    S.mapIso (meromorphicPresheafTensorIso X M)⟩

/-- An invertible presheaf map descends invertibly across a locally bijective map to a sheaf.
The inverse descends by the same universal property as the original map. -/
private theorem iso_of_locallyBijective_square
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{u}} {P Q : _root_.PresheafOfModules.{u} R}
    (e : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q.presheaf)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PresheafOfModules.IsLocallyInjective J e]
    [PresheafOfModules.IsLocallySurjective J e]
    (a : P ⟶ P) (b : Q ⟶ Q) [IsIso a] (h : e ≫ b = a ≫ e) : IsIso b := by
  let E := PresheafOfModules.homEquivOfIsLocallyBijective e hQ
  let c := E.symm (inv a ≫ e)
  have hc : e ≫ c = inv a ≫ e := E.apply_symm_apply _
  refine ⟨⟨c, ?_, ?_⟩⟩
  · apply E.injective
    change e ≫ (b ≫ c) = e ≫ 𝟙 Q
    rw [← Category.assoc, h, Category.assoc, hc]
    simp
  · apply E.injective
    change e ≫ (c ≫ b) = e ≫ 𝟙 Q
    rw [← Category.assoc, hc, Category.assoc, h]
    simp

/-- Regular denominators remain invertible on sections after sheafification.
Restrict to Over U, descend the inverse there, and evaluate at U.
Source: Stacks, Tag 01X4 (blueprint: def-sc-meromorphic-module). -/
private theorem meromorphic_denominator_isUnit (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (b : meromorphicDenominators X U) :
    IsUnit (algebraMap Γ(X, U)
      (Module.End Γ(X, U) Γ(meromorphicModule X M, U)) b.val) := by
  let J := Opens.grothendieckTopology X
  let F := Over.forget U
  let P := (PresheafOfModules.restrictOver X.presheaf U).obj (meromorphicPresheaf X M)
  let Q := (PresheafOfModules.restrictOver X.presheaf U).obj (meromorphicModule X M).val
  let e : P ⟶ Q := (PresheafOfModules.restrictOver X.presheaf U).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (meromorphicPresheaf X M))
  have he_inj : PresheafOfModules.IsLocallyInjective (J.over U) e :=
    Presheaf.isLocallyInjective_whisker (J.over U) J F
      (CategoryTheory.toSheafify J (meromorphicPresheaf X M).presheaf)
  have he_surj : PresheafOfModules.IsLocallySurjective (J.over U) e :=
    Presheaf.isLocallySurjective_whisker (J.over U) J F
      (CategoryTheory.toSheafify J (meromorphicPresheaf X M).presheaf)
  let r := PresheafOfModules.overSections (R := X.presheaf) U b.val
  let a := PresheafOfModules.sectionsSMul P r
  let c := PresheafOfModules.sectionsSMul Q r
  have ha : IsIso a := by
    have : IsIso ((PresheafOfModules.toPresheaf _).map a) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro W
      apply (ConcreteCategory.isIso_iff_bijective _).2
      change Function.Bijective (fun z : LocalizedModule
        (meromorphicDenominators X W.unop.left) Γ(M, W.unop.left) ↦
          (X.presheaf.map W.unop.hom.op b.val) • z)
      exact (Module.End.isUnit_iff _).1
        (IsLocalizedModule.map_units
          (LocalizedModule.mkLinearMap (meromorphicDenominators X W.unop.left)
            Γ(M, W.unop.left)) (restrictMeromorphicDenominator X W.unop.hom b))
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have hQ : Presheaf.IsSheaf (J.over U) Q.presheaf :=
    ((meromorphicModule X M).over U).isSheaf
  have hc : IsIso c := iso_of_locallyBijective_square e hQ a c
    (PresheafOfModules.sectionsSMul_naturality e r)
  have hc' : IsIso ((PresheafOfModules.toPresheaf _).map c) := inferInstance
  have hc'' := (ConcreteCategory.isIso_iff_bijective
    (((PresheafOfModules.toPresheaf _).map c).app (op (Over.mk (𝟙 U))))).1
      (inferInstance : IsIso
        (((PresheafOfModules.toPresheaf _).map c).app (op (Over.mk (𝟙 U)))))
  apply (Module.End.isUnit_iff _).2
  change Function.Bijective (fun z : Γ(meromorphicModule X M, U) ↦ b.val • z)
  change Function.Bijective (fun z : Γ(meromorphicModule X M, U) ↦
    (X.presheaf.map (𝟙 U).op b.val) • z) at hc''
  simpa using hc''

/-- Source: Stacks, Tags 01X4 and 02OX (blueprint: def-sc-meromorphic-module).
Proof: locally a meromorphic scalar is a/b. Send it to a times s divided by b in the
localized module. This is independent of representatives, because b acts invertibly there.
The local maps agree under restriction and glue. Uniqueness follows since multiplication
by every regular denominator is invertible in the meromorphic module. -/
theorem exists_meromorphicSectionMap (X : Scheme.{u}) (M : X.Modules)
    (s : unit X ⟶ meromorphicModule X M) :
    ∃! f : meromorphicModule X (unit X) ⟶
        meromorphicModule X M,
      toMeromorphicModule X (unit X) ≫ f = s := by
  let N : X.Modules := meromorphicModule X M
  let g (U : X.Opens) : Γ(X, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    (s.val.app (op U)).hom
  let t (U : X.Opens) :
      LocalizedModule (meromorphicDenominators X U) Γ(X, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    LocalizedModule.lift _ (g U) (meromorphic_denominator_isUnit X M U)
  have ht (U : X.Opens) (a : Γ(X, U)) (b : meromorphicDenominators X U) :
      b.val • t U (LocalizedModule.mk a b) = g U a := by
    rw [← (t U).map_smul, LocalizedModule.smul'_mk]
    change t U (LocalizedModule.mk (b • a) b) = _
    rw [LocalizedModule.mk_cancel]
    exact LocalizedModule.lift_mk_one _ _ _ a
  let T : meromorphicPresheaf X (unit X) ⟶ N.val :=
    { app U := ModuleCat.ofHom (X := (meromorphicPresheaf X (unit X)).obj U)
        (Y := N.val.obj U) (t U.unop)
      naturality := by
        intro U V i
        ext z
        induction z using LocalizedModule.induction_on with | h a b =>
          change t V.unop (meromorphicRestriction X (unit X) i.unop
            (LocalizedModule.mk a b)) = N.val.map i (t U.unop (LocalizedModule.mk a b))
          apply ((Module.End.isUnit_iff _).1
            (meromorphic_denominator_isUnit X M V.unop
              (restrictMeromorphicDenominator X i.unop b))).1
          let : Module Γ(X, V.unop) Γ(N, V.unop) := (N.val.obj V).isModule
          change ((X.presheaf.map i b.val : Γ(X, V.unop)) • t V.unop
              (meromorphicRestriction X (unit X) i.unop (LocalizedModule.mk a b)) :
                Γ(N, V.unop)) =
            ((X.presheaf.map i b.val : Γ(X, V.unop)) •
              N.presheaf.map i (t U.unop (LocalizedModule.mk a b)) : Γ(N, V.unop))
          rw [meromorphicRestriction_mk]
          change (restrictMeromorphicDenominator X i.unop b).val • t V.unop
              (LocalizedModule.mk (X.presheaf.map i a)
                (restrictMeromorphicDenominator X i.unop b)) = _
          erw [ht, ← N.map_smul i.unop, ht]
          exact PresheafOfModules.naturality_apply s.val i a }
  have hT : meromorphicLocalization X (unit X) ≫ T = s.val := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact LocalizedModule.lift_mk_one _ (g U.unop)
      (meromorphic_denominator_isUnit X M U.unop) a
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let f : meromorphicModule X (unit X) ⟶ N := (adj.homEquiv _ N).symm T
  have hf : adj.unit.app (meromorphicPresheaf X (unit X)) ≫ f.val = T :=
    (adj.homEquiv _ N).apply_symm_apply T
  have hloc : (toMeromorphicModule X (unit X)).val =
      meromorphicLocalization X (unit X) ≫
        adj.unit.app (meromorphicPresheaf X (unit X)) :=
    (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage _
  refine ⟨f, ?_, ?_⟩
  · apply (SheafOfModules.forget X.ringCatSheaf).map_injective
    change (toMeromorphicModule X (unit X)).val ≫ f.val = s.val
    rw [hloc, Category.assoc, hf, hT]
  · intro f' hf'
    apply (adj.homEquiv _ N).injective
    change adj.unit.app (meromorphicPresheaf X (unit X)) ≫ f'.val =
      adj.unit.app (meromorphicPresheaf X (unit X)) ≫ f.val
    rw [hf]
    have hf'' : meromorphicLocalization X (unit X) ≫
        (adj.unit.app (meromorphicPresheaf X (unit X)) ≫ f'.val) = s.val := by
      have h := congrArg (fun k ↦ k.val) hf'
      change (toMeromorphicModule X (unit X)).val ≫ f'.val = s.val at h
      rw [hloc, Category.assoc] at h
      exact h
    ext U z
    let l := ((adj.unit.app (meromorphicPresheaf X (unit X)) ≫ f'.val).app U).hom
    have hl : l.comp (LocalizedModule.mkLinearMap _ Γ(X, U.unop)) = g U.unop := by
      apply LinearMap.ext
      intro a
      exact congrArg (fun k ↦ (k.app U).hom a) hf''
    exact congrArg (fun k ↦ k z)
      (LocalizedModule.lift_unique _ (g U.unop)
        (meromorphic_denominator_isUnit X M U.unop) l hl).symm

/-- Multiplication by a meromorphic section, extended from ordinary scalars by localization.
Source: Stacks, Tags 01X4 and 02OX (blueprint: def-sc-meromorphic-module). -/
noncomputable def meromorphicSectionMap (X : Scheme.{u}) (M : X.Modules)
    (s : unit X ⟶ meromorphicModule X M) :
    meromorphicModule X (unit X) ⟶ meromorphicModule X M :=
  (exists_meromorphicSectionMap X M s).exists.choose

end AlgebraicGeometry.Scheme.Modules
