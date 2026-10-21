/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.CompleteCoefficientDatum
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProEtaleConstantReductionTower
import Sheaf.Paper.CompletionFiniteReduction
import Sheaf.Paper.ReductionPullFiniteEvaluation
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # The completion unit and completed pullback on strict quotient towers

Source: smooth-purity blueprint, fix-lem-exchanges, Proof Steps 2 and 5;
Stacks Tags 099M and 099N (blueprint: lem-sf-cbc-completed-pullback-unit-tower).

The canonical small model of the original pro-etale site only enlarges its Hom
universe. Its topology and base-change functor are the published transports of
those on the original site. All coefficient rings are constant sheaves, with no
finiteness assumption on their underlying sets. Level n means exponent n+1.
The existing quotient presentation fixes every strict transition and its K-flat
computation; the existing reduction/pullback comparison fixes tensor reassociation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AdicSites
namespace AlgebraicGeometry.Scheme.CompletedPullbackUnitTower

/-- The published small model, with precisely the original pro-etale topology.
Source: Stacks 09A5 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def site (T : Scheme.{t}) : Site.{t + 1} where
  objects := proEtaleSiteModel T
  topology := proEtaleModelTopology T

/-- The canonical geometric inverse image on the published small models.
Source: Stacks 00VC and 099N (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def inverse {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T) (Type (t + 1)) ⥤
      Sheaf (proEtaleModelTopology T') (Type (t + 1)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPullback (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The corresponding sectionwise direct image on these same models.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def direct {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T') (Type (t + 1)) ⥤
      Sheaf (proEtaleModelTopology T) (Type (t + 1)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPushforwardContinuous (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The defining geometric adjunction, rather than an arbitrary functor adjunction.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def adjunction {T' T : Scheme.{t}} (g : T' ⟶ T) : inverse g ⊣ direct g :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafAdjunctionContinuous (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The geometric inverse image is left exact on the equivalent small model.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower).
Proof: scheme base change preserves finite limits on the pro-etale sites. The
AsSmall equivalences preserve those limits. The sheaf inverse image is left Kan
extension followed by left exact sheafification, so preserves finite limits. -/
@[instance]
theorem inverse_finiteLimits {T' T : Scheme.{t}} (g : T' ⟶ T) :
    PreservesFiniteLimits (inverse g) := by
  let := proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt) ⋙ proEtaleBaseChange g ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange g) := flat_of_preservesFiniteLimits _
  dsimp only [inverse]
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- The ring-valued inverse image on the transported small pro-etale sites.  This is
the same left-Kan-extension/sheafification construction as `inverse`, with the
commutative-ring value category; it is the transported version of
`proEtaleSheafInverseImage` from `def-weil-proetale-inverse-image`.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
noncomputable def transportedRingInverseImage {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1} ⥤
      Sheaf (proEtaleModelTopology T') CommRingCat.{t + 1} :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPullback (CommRingCat.{t + 1})
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The actual ring direct image on the small models.
Source: Stacks 00YV (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedRingDirectImage {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T') CommRingCat.{t + 1} ⥤
      Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1} :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPushforwardContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The ring adjunction unit, forgetting commutativity on the small models.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedRingUnit {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    siteModuleRings O ⟶
      siteModuleRings ((transportedRingDirectImage g).obj
        ((transportedRingInverseImage g).obj O)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (sheafCompose (proEtaleModelTopology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
      (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O)

/-- Module inverse image along the actual transported ring unit, as in
`proEtaleModuleInverseImage`, already in the small-model coordinates.
Source: Stacks 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedModuleInverseImage {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    ConstantCompletion.Mod O ⥤
      ConstantCompletion.Mod ((transportedRingInverseImage g).obj O) :=
  letI := proEtaleModelBaseChange_isContinuous g
  SheafOfModules.pullback.{t + 1} (F := proEtaleModelBaseChange g)
    (J := proEtaleModelTopology T) (K := proEtaleModelTopology T')
    (transportedRingUnit g O)

/-- Underlying ring comparison: the set-adjoint of the ring adjunction unit.
Source: Stacks 00YV (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def ringUnderlyingMap {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    (inverse g).obj ((sheafCompose (proEtaleModelTopology T)
      (CategoryTheory.forget CommRingCat)).obj O) ⟶
      (sheafCompose (proEtaleModelTopology T') (CategoryTheory.forget CommRingCat)).obj
        ((transportedRingInverseImage g).obj O) :=
  letI := proEtaleModelBaseChange_isContinuous g
  ((adjunction g).homEquiv _ _).symm
    ((sheafCompose (proEtaleModelTopology T) (CategoryTheory.forget CommRingCat)).map
      (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
        (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O))

/-- The canonical constant map, adjoint to sheafification of constant sections.
This is `proEtaleConstantInverseImageMap` on the small models, with unrestricted
coefficient universe, rather than a choice of an isomorphism of constant sheaves.
Source: Stacks 0H7J (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def constantInverseImageMap {T' T : Scheme.{t}} (g : T' ⟶ T)
    (B : CommRingCat.{t + 1}) :
    (transportedRingInverseImage g).obj
        ((constantSheaf (proEtaleModelTopology T) CommRingCat.{t + 1}).obj B) ⟶
      (constantSheaf (proEtaleModelTopology T') CommRingCat.{t + 1}).obj B :=
  letI := proEtaleModelBaseChange_isContinuous g
  (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')).homEquiv _ _).symm
      (((sheafificationAdjunction (proEtaleModelTopology T) CommRingCat.{t + 1}).homEquiv
        _ _).symm
          (Functor.whiskerLeft (proEtaleModelBaseChange g).op
            (toSheafify (proEtaleModelTopology T')
              ((Functor.const (proEtaleSiteModel T')ᵒᵖ).obj B))))

section GeometricConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem binary_graph {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type u) J K)
    (S₁ S₂ S₃ : Sheaf J (Type u)) (N₁ N₂ N₃ : Sheaf K (Type u))
    (π₁ : L.obj S₁ ⟶ N₁) (π₂ : L.obj S₂ ⟶ N₂) (π₃ : L.obj S₃ ⟶ N₃)
    (u₁ : S₁ ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj N₁)
    (u₂ : S₂ ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj N₂)
    (u₃ : S₃ ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj N₃)
    (h₁ : ∀ U x, π₁.hom.app (F.op.obj U) ((adj.unit.app S₁).hom.app U x) =
      u₁.hom.app U x)
    (h₂ : ∀ U x, π₂.hom.app (F.op.obj U) ((adj.unit.app S₂).hom.app U x) =
      u₂.hom.app U x)
    (h₃ : ∀ U x, π₃.hom.app (F.op.obj U) ((adj.unit.app S₃).hom.app U x) =
      u₃.hom.app U x)
    (μ : ∀ U : Cᵒᵖ, S₁.obj.obj U → S₂.obj.obj U → S₃.obj.obj U)
    (ν : ∀ V : Dᵒᵖ, N₁.obj.obj V → N₂.obj.obj V → N₃.obj.obj V)
    (hn : ∀ {U V : Dᵒᵖ} (i : U ⟶ V) x y,
      N₃.obj.map i (ν U x y) = ν V (N₁.obj.map i x) (N₂.obj.map i y))
    (hu : ∀ U x y, ν (F.op.obj U) (u₁.hom.app U x) (u₂.hom.app U y) =
      u₃.hom.app U (μ U x y))
    (Z : Sheaf J (Type u)) (a : Z ⟶ S₁) (b : Z ⟶ S₂) (t : Z ⟶ S₃)
    (ht : ∀ U x, t.hom.app U x = μ U (a.hom.app U x) (b.hom.app U x)) :
    ∀ V x, π₃.hom.app V ((L.map t).hom.app V x) =
      ν V (π₁.hom.app V ((L.map a).hom.app V x))
        (π₂.hom.app V ((L.map b).hom.app V x)) := by
  let a' := L.map a ≫ π₁
  let b' := L.map b ≫ π₂
  let c : L.obj Z ⟶ N₃ := ⟨{
    app := fun V ↦ ↾fun x ↦ ν V (a'.hom.app V x) (b'.hom.app V x)
    naturality := by
      intro U V i
      ext x
      have ha := ConcreteCategory.congr_hom (a'.hom.naturality i) x
      have hb := ConcreteCategory.congr_hom (b'.hom.naturality i) x
      change a'.hom.app V ((L.obj Z).obj.map i x) =
        N₁.obj.map i (a'.hom.app U x) at ha
      change b'.hom.app V ((L.obj Z).obj.map i x) =
        N₂.obj.map i (b'.hom.app U x) at hb
      change ν V (a'.hom.app V ((L.obj Z).obj.map i x))
        (b'.hom.app V ((L.obj Z).obj.map i x)) = _
      rw [ha, hb]
      exact (hn i _ _).symm }⟩
  have he : L.map t ≫ π₃ = c := by
    apply (adj.homEquiv Z N₃).injective
    ext U x
    have ha := congrArg (fun z ↦ z.hom.app U x) (adj.unit.naturality a)
    have hb := congrArg (fun z ↦ z.hom.app U x) (adj.unit.naturality b)
    have hc := congrArg (fun z ↦ z.hom.app U x) (adj.unit.naturality t)
    change (adj.unit.app S₁).hom.app U (a.hom.app U x) =
      (L.map a).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x) at ha
    change (adj.unit.app S₂).hom.app U (b.hom.app U x) =
      (L.map b).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x) at hb
    change (adj.unit.app S₃).hom.app U (t.hom.app U x) =
      (L.map t).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x) at hc
    change π₃.hom.app (F.op.obj U)
      ((L.map t).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x)) =
      ν (F.op.obj U)
        (π₁.hom.app (F.op.obj U)
          ((L.map a).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x)))
        (π₂.hom.app (F.op.obj U)
          ((L.map b).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x)))
    rw [← ha, ← hb, ← hc, h₁, h₂, h₃, ht]
    exact (hu U _ _).symm
  intro V x
  exact congrArg (fun z ↦ z.hom.app V x) he

private theorem nullary_graph {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type u) J K)
    (S : Sheaf J (Type u)) (N : Sheaf K (Type u)) (π : L.obj S ⟶ N)
    (u₀ : S ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj N)
    (hπ : ∀ U x, π.hom.app (F.op.obj U) ((adj.unit.app S).hom.app U x) =
      u₀.hom.app U x)
    (μ : ∀ U : Cᵒᵖ, S.obj.obj U) (ν : ∀ V : Dᵒᵖ, N.obj.obj V)
    (hn : ∀ {U V : Dᵒᵖ} (i : U ⟶ V), N.obj.map i (ν U) = ν V)
    (hu : ∀ U, u₀.hom.app U (μ U) = ν (F.op.obj U))
    (Z : Sheaf J (Type u)) (a : Z ⟶ S)
    (ha : ∀ U x, a.hom.app U x = μ U) :
    ∀ V x, π.hom.app V ((L.map a).hom.app V x) = ν V := by
  let c : L.obj Z ⟶ N := ⟨{
    app := fun V ↦ ↾fun _ ↦ ν V
    naturality := by intro U V i; ext x; exact (hn i).symm }⟩
  have he : L.map a ≫ π = c := by
    apply (adj.homEquiv Z N).injective
    ext U x
    have h := congrArg (fun z ↦ z.hom.app U x) (adj.unit.naturality a)
    change (adj.unit.app S).hom.app U (a.hom.app U x) =
      (L.map a).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x) at h
    change π.hom.app (F.op.obj U)
      ((L.map a).hom.app (F.op.obj U) ((adj.unit.app Z).hom.app U x)) = ν (F.op.obj U)
    rw [← h, hπ, ha, hu]
  intro V x
  exact congrArg (fun z ↦ z.hom.app V x) he


private def algebraOfNormalizedUnits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type u) J K)
    (O : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (r : L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj O) ≅
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj B)
    (N : ConstantCompletion.Mod O ⥤ ConstantCompletion.Mod B)
    (e : N ⋙ ConstantCompletion.underlying B ≅ ConstantCompletion.underlying O ⋙ L)
    (hr_add : ∀ U (x y : O.obj.obj U),
      (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U (x + y))) =
        (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U x)) +
          (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U y)))
    (hr_mul : ∀ U (x y : O.obj.obj U),
      (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U (x * y))) =
        (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U x)) *
          (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U y)))
    (hr_zero : ∀ U, (@id (B.obj.obj (F.op.obj U))
      (((adj.homEquiv _ _) r.hom).hom.app U (0 : O.obj.obj U))) = 0)
    (hr_one : ∀ U, (@id (B.obj.obj (F.op.obj U))
      (((adj.homEquiv _ _) r.hom).hom.app U (1 : O.obj.obj U))) = 1)
    (hm_add : ∀ (M : ConstantCompletion.Mod O) U (x y : M.val.obj U),
      (@id ((N.obj M).val.obj (F.op.obj U))
        (((adj.homEquiv _ _) (e.inv.app M)).hom.app U (x + y))) =
        (@id ((N.obj M).val.obj (F.op.obj U)) (((adj.homEquiv _ _) (e.inv.app M)).hom.app U x)) +
          (@id ((N.obj M).val.obj (F.op.obj U)) (((adj.homEquiv _ _) (e.inv.app M)).hom.app U y)))
    (hm_zero : ∀ (M : ConstantCompletion.Mod O) U,
      (@id ((N.obj M).val.obj (F.op.obj U))
        (((adj.homEquiv _ _) (e.inv.app M)).hom.app U (0 : M.val.obj U))) = 0)
    (hm_smul : ∀ (M : ConstantCompletion.Mod O) U (a : O.obj.obj U) (x : M.val.obj U),
      (@id ((N.obj M).val.obj (F.op.obj U))
        (((adj.homEquiv _ _) (e.inv.app M)).hom.app U (a • x))) =
        (@id (B.obj.obj (F.op.obj U)) (((adj.homEquiv _ _) r.hom).hom.app U a)) •
          (@id ((N.obj M).val.obj (F.op.obj U)) (((adj.homEquiv _ _) (e.inv.app M)).hom.app U x))) :
    SheafOfModules.AlgebraicInverseImage L O B := by
  let ro := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj O
  let rb := (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj B
  let ur := (adj.homEquiv ro rb) r.hom
  let um (M : ConstantCompletion.Mod O) :=
    (adj.homEquiv ((ConstantCompletion.underlying O).obj M)
      ((ConstantCompletion.underlying B).obj (N.obj M))) (e.inv.app M)
  have hu (S : Sheaf J (Type u)) (T : Sheaf K (Type u)) (π : L.obj S ⟶ T) :
      ∀ U x, π.hom.app (F.op.obj U) ((adj.unit.app S).hom.app U x) =
        ((adj.homEquiv S T) π).hom.app U x := by
    rw [Adjunction.homEquiv_unit]
    intro U x
    rfl
  have ring_map_add {U V : Dᵒᵖ} (i : U ⟶ V) (x y : B.obj.obj U) :
      (B.obj.map i).hom (x + y) = (B.obj.map i).hom x + (B.obj.map i).hom y :=
    map_add (B.obj.map i).hom x y
  have ring_map_mul {U V : Dᵒᵖ} (i : U ⟶ V) (x y : B.obj.obj U) :
      (B.obj.map i).hom (x * y) = (B.obj.map i).hom x * (B.obj.map i).hom y :=
    map_mul (B.obj.map i).hom x y
  have module_map_add (M : ConstantCompletion.Mod O) {U V : Dᵒᵖ}
      (i : U ⟶ V) (x y : (N.obj M).val.obj U) :
      ((N.obj M).val.map i).hom (x + y) =
        ((N.obj M).val.map i).hom x + ((N.obj M).val.map i).hom y :=
    map_add ((N.obj M).val.map i).hom x y
  refine { ringUnderlying := r, modules := N, moduleUnderlying := e
           ringAdd := ?_, ringMul := ?_, ringZero := ?_, ringOne := ?_
           moduleAdd := ?_, moduleZero := ?_, moduleSMul := ?_ }
  · intro Z a b t ht
    exact binary_graph J K F L adj ro ro ro rb rb rb r.hom r.hom r.hom
      ur ur ur (hu _ _ _) (hu _ _ _) (hu _ _ _)
      (fun U x y ↦ @id (O.obj.obj U) x + @id (O.obj.obj U) y)
      (fun U x y ↦ @id (B.obj.obj U) x + @id (B.obj.obj U) y)
      (fun i x y ↦ ring_map_add i x y)
      (fun U x y ↦ (hr_add U x y).symm) Z a b t ht
  · intro Z a b t ht
    exact binary_graph J K F L adj ro ro ro rb rb rb r.hom r.hom r.hom
      ur ur ur (hu _ _ _) (hu _ _ _) (hu _ _ _)
      (fun U x y ↦ @id (O.obj.obj U) x * @id (O.obj.obj U) y)
      (fun U x y ↦ @id (B.obj.obj U) x * @id (B.obj.obj U) y)
      (fun i x y ↦ ring_map_mul i x y)
      (fun U x y ↦ (hr_mul U x y).symm) Z a b t ht
  · intro Z a ha
    exact nullary_graph J K F L adj ro rb r.hom ur (hu _ _ _)
      (fun U ↦ (0 : O.obj.obj U)) (fun U ↦ (0 : B.obj.obj U)) (fun i ↦ map_zero (B.obj.map i).hom)
      hr_zero Z a ha
  · intro Z a ha
    exact nullary_graph J K F L adj ro rb r.hom ur (hu _ _ _)
      (fun U ↦ (1 : O.obj.obj U)) (fun U ↦ (1 : B.obj.obj U)) (fun i ↦ map_one (B.obj.map i).hom)
      hr_one Z a ha
  · intro M Z a b t ht
    exact binary_graph J K F L adj _ _ _ _ _ _
      (e.inv.app M) (e.inv.app M) (e.inv.app M) (um M) (um M) (um M)
      (hu _ _ _) (hu _ _ _) (hu _ _ _)
      (fun U x y ↦ @id (M.val.obj U) x + @id (M.val.obj U) y)
      (fun U x y ↦ @id ((N.obj M).val.obj U) x + @id ((N.obj M).val.obj U) y)
      (fun i x y ↦ module_map_add M i x y)
      (fun U x y ↦ (hm_add M U x y).symm) Z a b t ht
  · intro M Z a ha
    exact nullary_graph J K F L adj _ _ (e.inv.app M) (um M) (hu _ _ _)
      (fun U ↦ (0 : M.val.obj U)) (fun U ↦ (0 : (N.obj M).val.obj U))
      (fun i ↦ map_zero ((N.obj M).val.map i).hom)
      (hm_zero M) Z a ha
  · intro M Z a b t ht
    exact binary_graph J K F L adj ro _ _ rb _ _ r.hom (e.inv.app M) (e.inv.app M)
      ur (um M) (um M) (hu _ _ _) (hu _ _ _) (hu _ _ _)
      (fun U a x ↦ @id (O.obj.obj U) a • @id (M.val.obj U) x)
      (fun U a x ↦ @id (B.obj.obj U) a • @id ((N.obj M).val.obj U) x)
      (fun i a x ↦ (N.obj M).val.map_smul i a x)
      (fun U a x ↦ (hm_smul M U a x).symm) Z a b t ht


section AbstractForget
universe w
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]
  {E : Type w} [Category.{u} E] (U : E ⥤ Type u)
  [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
  [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]

private def abstractForget :
    Functor.sheafPullback F E J K ⋙ sheafCompose K U ≅
      sheafCompose J U ⋙ Functor.sheafPullback F (Type u) J K :=
  Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso F E J K) (sheafCompose K U) ≪≫
    sheafPullbackForgetIso J K F U ≪≫
    Functor.isoWhiskerLeft (sheafCompose J U)
      (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K).symm

private theorem abstractForget_unit (S : Sheaf J E) :
    (sheafCompose J U).map ((Functor.sheafAdjunctionContinuous F E J K).unit.app S) ≫
      (F.sheafPushforwardContinuous (Type u) J K).map
        ((abstractForget J K F U).hom.app S) =
      (Functor.sheafAdjunctionContinuous F (Type u) J K).unit.app
        ((sheafCompose J U).obj S) := by
  let R := F.sheafPushforwardContinuous (Type u) J K
  let e := Functor.sheafPullbackConstruction.sheafPullbackIso F E J K
  let s := Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K
  have he := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous F E J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F E J K) S
  have he' : (sheafCompose J U).map
      ((Functor.sheafAdjunctionContinuous F E J K).unit.app S) ≫
        R.map ((sheafCompose K U).map (e.hom.app S)) =
      (sheafCompose J U).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F E J K).unit.app S) :=
    by
      have h' := congrArg (sheafCompose J U).map he
      simp only [Functor.map_comp] at h'
      apply Sheaf.hom_ext
      ext X x
      exact congrArg (fun k ↦ k.hom.app X x) h'
  have hs := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous F (Type u) J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K)
    ((sheafCompose J U).obj S)
  change (Functor.sheafAdjunctionContinuous F (Type u) J K).unit.app
      ((sheafCompose J U).obj S) ≫ R.map (s.hom.app _) = _ at hs
  have h := sheafPullbackForgetIso_unit J K F U S
  dsimp only [abstractForget, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change _ ≫ R.map ((sheafCompose K U).map (e.hom.app S) ≫
    (sheafPullbackForgetIso J K F U).hom.app S ≫
      s.inv.app ((sheafCompose J U).obj S)) = _
  simp only [Functor.map_comp]
  rw [reassoc_of% he', reassoc_of% h, ← hs, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  rfl

end AbstractForget

private theorem ring_comparison_isIso {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    IsIso (ringUnderlyingMap g O) := by
  let := proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt) ⋙ proEtaleBaseChange g ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange g) := flat_of_preservesFiniteLimits _
  let e := (abstractForget (proEtaleModelTopology T)
    (proEtaleModelTopology T') (proEtaleModelBaseChange g)
    (CategoryTheory.forget CommRingCat.{t + 1})).app O
  have he : ringUnderlyingMap g O = e.inv := by
    apply ((adjunction g).homEquiv _ _).injective
    change _ = (adjunction g).unit.app _ ≫ (direct g).map e.inv
    dsimp only [ringUnderlyingMap]
    rw [Equiv.apply_symm_apply]
    have h := abstractForget_unit (proEtaleModelTopology T)
      (proEtaleModelTopology T') (proEtaleModelBaseChange g)
      (CategoryTheory.forget CommRingCat.{t + 1}) O
    change _ ≫ (direct g).map e.hom = _ at h
    have hh := congrArg (fun a ↦ a ≫ (direct g).map e.inv) h
    dsimp only [adjunction]
    simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] using hh
  rw [he]
  infer_instance

private def constructedForget {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {E : Type*} [Category.{u} E] (U : E ⥤ Type u)
    [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
    [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
    [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op] :
    Functor.sheafPullback F E J K ⋙ sheafCompose K U ≅
      sheafCompose J U ⋙ Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K :=
  Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso F E J K) (sheafCompose K U) ≪≫
    sheafPullbackForgetIso J K F U

private theorem constructedForget_unit {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {E : Type*} [Category.{u} E] (U : E ⥤ Type u)
    [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
    [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
    [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]
    (S : Sheaf J E) :
    (sheafCompose J U).map ((Functor.sheafAdjunctionContinuous F E J K).unit.app S) ≫
      (F.sheafPushforwardContinuous (Type u) J K).map
        ((constructedForget J K F U).hom.app S) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K).unit.app
        ((sheafCompose J U).obj S) := by
  have he := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous F E J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F E J K) S
  have he' : (sheafCompose J U).map
      ((Functor.sheafAdjunctionContinuous F E J K).unit.app S) ≫
        (F.sheafPushforwardContinuous (Type u) J K).map
          ((sheafCompose K U).map
            ((Functor.sheafPullbackConstruction.sheafPullbackIso F E J K).hom.app S)) =
      (sheafCompose J U).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F E J K).unit.app S) := by
    have h' := congrArg (sheafCompose J U).map he
    simp only [Functor.map_comp] at h'
    apply Sheaf.hom_ext
    ext X x
    exact congrArg (fun k ↦ k.hom.app X x) h'
  dsimp only [constructedForget, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerRight_app]
  erw [Functor.map_comp, ← Category.assoc, he']
  exact sheafPullbackForgetIso_unit J K F U S

private theorem module_comparison_of_presentation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]
    [PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K)]
    (O : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (φ : siteModuleRings O ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J K).obj (siteModuleRings B))
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj (siteModuleRings O))
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj (siteModuleRings B)))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ e : SheafOfModules.pullback.{u} φ ⋙ ConstantCompletion.underlying B ≅
        ConstantCompletion.underlying O ⋙ Functor.sheafPullback F (Type u) J K,
      ∀ (M : ConstantCompletion.Mod O) (U : Cᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).hom.app (F.op.obj U)
          (((ConstantCompletion.underlying O).map
            ((SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app M)).hom.app U x) =
        ((Functor.sheafAdjunctionContinuous F (Type u) J K).unit.app
          ((ConstantCompletion.underlying O).obj M)).hom.app U x := by
  obtain ⟨e, he⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation φ pr hr
  let ua := SheafOfModules.toSheaf (siteModuleRings O)
  let ub := SheafOfModules.toSheaf (siteModuleRings B)
  let vj := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  let vk := sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})
  let la := Functor.sheafPullbackConstruction.sheafPullback F AddCommGrpCat.{u} J K
  let ls := Functor.sheafPullbackConstruction.sheafPullback F (Type (u)) J K
  let a := sheafPullbackForgetIso J K F (CategoryTheory.forget AddCommGrpCat.{u})
  let s := Functor.sheafPullbackConstruction.sheafPullbackIso F (Type (u)) J K
  let e' : SheafOfModules.pullback.{u} φ ⋙ ConstantCompletion.underlying B ≅
      ConstantCompletion.underlying O ⋙ Functor.sheafPullback F (Type u) J K :=
    (Functor.associator (SheafOfModules.pullback.{u} φ) ub vk).symm ≪≫
      Functor.isoWhiskerRight e vk ≪≫ Functor.associator ua la vk ≪≫
      Functor.isoWhiskerLeft ua a ≪≫ (Functor.associator ua vj ls).symm ≪≫
      Functor.isoWhiskerLeft (ua ⋙ vj) s.symm
  refine ⟨e', fun M U x ↦ ?_⟩
  have hm := he M
  have ha := sheafPullbackForgetIso_unit J K F
    (CategoryTheory.forget AddCommGrpCat.{u}) (ua.obj M)
  have hs := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous F (Type (u)) J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type (u)) J K)
    ((ua ⋙ vj).obj M)
  have hm' := congrArg (fun z ↦ z.hom.app U x) hm
  have ha' := congrArg (fun z ↦ z.hom.app U x) ha
  have hs' := congrArg (fun z ↦ z.hom.app U x) hs
  dsimp only [e', Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change (s.inv.app ((ua ⋙ vj).obj M)).hom.app (F.op.obj U)
      ((a.hom.app (ua.obj M)).hom.app (F.op.obj U)
        ((e.hom.app M).hom.app (F.op.obj U)
          (((SheafOfModules.toSheaf (siteModuleRings O)).map
            ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M)).hom.app U x))) = _
  rw [show ((e.hom.app M).hom.app (F.op.obj U)
      (((SheafOfModules.toSheaf (siteModuleRings O)).map
        ((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M)).hom.app U x)) =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
        AddCommGrpCat.{u} J K).unit.app (ua.obj M)).hom.app U x from hm']
  rw [show (a.hom.app (ua.obj M)).hom.app (F.op.obj U)
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
        AddCommGrpCat.{u} J K).unit.app (ua.obj M)).hom.app U x) =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
        (Type (u)) J K).unit.app ((ua ⋙ vj).obj M)).hom.app U x from ha']
  erw [← hs']
  exact congrArg (fun z ↦ z.hom.app (F.op.obj U)
    (((Functor.sheafAdjunctionContinuous F (Type u) J K).unit.app
      ((ConstantCompletion.underlying O).obj M)).hom.app U x))
      (Iso.hom_inv_id_app s ((ua ⋙ vj).obj M))

private theorem module_comparison {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃ e : transportedModuleInverseImage g O ⋙
          ConstantCompletion.underlying ((transportedRingInverseImage g).obj O) ≅
        ConstantCompletion.underlying O ⋙ inverse g,
      ∀ (M : ConstantCompletion.Mod O) (U : (proEtaleSiteModel T)ᵒᵖ)
          (x : M.val.obj U),
        (e.hom.app M).hom.app ((proEtaleModelBaseChange g).op.obj U)
          (((ConstantCompletion.underlying O).map
            ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
              (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
              (K := proEtaleModelTopology T')
              (R := siteModuleRings ((transportedRingInverseImage g).obj O))
              (transportedRingUnit g O)).unit.app M)).hom.app U x) =
        ((adjunction g).unit.app ((ConstantCompletion.underlying O).obj M)).hom.app U x := by
  let := proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt) ⋙ proEtaleBaseChange g ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange g) := flat_of_preservesFiniteLimits _
  let F := proEtaleModelBaseChange g
  let J := proEtaleModelTopology T
  let K := proEtaleModelTopology T'
  let R := (transportedRingInverseImage g).obj O
  let φ : siteModuleRings O ⟶
      (F.sheafPushforwardContinuous RingCat.{t + 1} J K).obj (siteModuleRings R) :=
    transportedRingUnit g O
  let pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{t + 1})).obj (siteModuleRings O))
      ((sheafCompose K (CategoryTheory.forget RingCat.{t + 1})).obj (siteModuleRings R)) :=
    { unit := (sheafCompose J (CategoryTheory.forget RingCat.{t + 1})).map φ
      iso := (constructedForget J K F (CategoryTheory.forget CommRingCat.{t + 1})).app O
      equation := fun U x ↦ by
        have h := constructedForget_unit J K F
          (CategoryTheory.forget CommRingCat.{t + 1}) O
        exact congrArg (fun z ↦ z.hom.app U x) h }
  exact module_comparison_of_presentation J K F O R φ pr rfl

private theorem canonical_algebra_exists {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃ I : SheafOfModules.AlgebraicInverseImage (inverse g) O
        ((transportedRingInverseImage g).obj O),
      I.ringUnderlying.hom = ringUnderlyingMap g O ∧
      I.modules = transportedModuleInverseImage g O ∧
      ∀ M : ConstantCompletion.Mod O,
        HEq ((adjunction g).homEquiv _ _ (I.moduleUnderlying.inv.app M))
          ((ConstantCompletion.underlying O).map
            ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
              (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
              (K := proEtaleModelTopology T')
              (R := siteModuleRings ((transportedRingInverseImage g).obj O))
              (transportedRingUnit g O)).unit.app M)) := by
  let := proEtaleModelBaseChange_isContinuous g
  let := ring_comparison_isIso g O
  obtain ⟨e, he⟩ := module_comparison g O
  let F := proEtaleModelBaseChange g
  let J := proEtaleModelTopology T
  let K := proEtaleModelTopology T'
  let R := (transportedRingInverseImage g).obj O
  let φ : siteModuleRings O ⟶
      (F.sheafPushforwardContinuous RingCat.{t + 1} J K).obj (siteModuleRings R) :=
    transportedRingUnit g O
  let η := (SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
    (F := F) (J := J) (K := K) (R := siteModuleRings R) φ).unit
  let r := asIso (ringUnderlyingMap g O)
  have hr : ((adjunction g).homEquiv _ _) r.hom =
      (sheafCompose J (CategoryTheory.forget CommRingCat.{t + 1})).map
        ((Functor.sheafAdjunctionContinuous F CommRingCat.{t + 1} J K).unit.app O) := by
    dsimp only [r, asIso_hom, ringUnderlyingMap]
    exact Equiv.apply_symm_apply _ _
  have hm (M : ConstantCompletion.Mod O) (U : (proEtaleSiteModel T)ᵒᵖ)
      (x : M.val.obj U) :
      (((adjunction g).homEquiv _ _) (e.inv.app M)).hom.app U x =
        (η.app M).val.app U x := by
    erw [Adjunction.homEquiv_unit]
    change (e.inv.app M).hom.app (F.op.obj U)
      (((adjunction g).unit.app ((ConstantCompletion.underlying O).obj M)).hom.app U x) = _
    erw [← he M U x]
    exact congrArg (fun z ↦ z.hom.app (F.op.obj U) ((η.app M).val.app U x))
      (Iso.hom_inv_id_app e M)
  have hm' (M : ConstantCompletion.Mod O) :
      ((adjunction g).homEquiv _ _) (e.inv.app M) =
        (ConstantCompletion.underlying O).map (η.app M) := by
    ext U x
    exact hm M U x
  let I : SheafOfModules.AlgebraicInverseImage (inverse g) O R :=
    algebraOfNormalizedUnits J K F (inverse g) (adjunction g) O R r
      (transportedModuleInverseImage g O) e
      (fun U x y ↦ by
        erw [hr]
        exact map_add
          (((Functor.sheafAdjunctionContinuous F CommRingCat.{t + 1} J K).unit.app
            O).hom.app U).hom x y)
      (fun U x y ↦ by
        erw [hr]
        exact map_mul
          (((Functor.sheafAdjunctionContinuous F CommRingCat.{t + 1} J K).unit.app
            O).hom.app U).hom x y)
      (fun U ↦ by
        erw [hr]
        exact map_zero
          (((Functor.sheafAdjunctionContinuous F CommRingCat.{t + 1} J K).unit.app
            O).hom.app U).hom)
      (fun U ↦ by
        erw [hr]
        exact map_one
          (((Functor.sheafAdjunctionContinuous F CommRingCat.{t + 1} J K).unit.app
            O).hom.app U).hom)
      (fun M U x y ↦ by
        erw [hm']
        exact map_add ((η.app M).val.app U).hom x y)
      (fun M U ↦ by
        erw [hm']
        exact map_zero ((η.app M).val.app U).hom)
      (fun M U a x ↦ by
        erw [hm', hr]
        exact ((η.app M).val.app U).hom.map_smul a x)
  exact ⟨I, rfl, rfl, fun M ↦ heq_of_eq (hm' M)⟩

private theorem constantIso_hom {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {E : Type*} [Category.{u} E] [HasWeakSheafify J E] [HasWeakSheafify K E]
    [(F.sheafPushforwardContinuous E J K).IsRightAdjoint]
    {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T)) (B : E) :
    (F.constantSheafsheafPullbackIso E J K hT hFT).hom.app B =
      ((F.sheafAdjunctionContinuous E J K).homEquiv _ _).symm
        (((sheafificationAdjunction J E).homEquiv _ _).symm
          (Functor.whiskerLeft F.op
            (toSheafify K ((Functor.const Dᵒᵖ).obj B)))) := by
  let aJ := constantSheafAdj J E hT
  let a := (aJ.comp (F.sheafAdjunctionContinuous E J K)).ofNatIsoRight
    (F.sheafPushforwardContinuousCompSheafSectionsObjIso E J K (op T))
  change (a.leftAdjointUniq (constantSheafAdj K E hFT)).hom.app B = _
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  dsimp only [Functor.sheafPushforwardContinuousCompSheafSectionsObjIso]
  erw [Category.comp_id, Equiv.trans_apply, Equiv.apply_symm_apply]
  dsimp only [aJ, constantSheafAdj]
  erw [Adjunction.comp_homEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  erw [Adjunction.comp_unit_app, Adjunction.homEquiv_unit]
  simp only [constantPresheafAdj_unit_app, Category.id_comp]
  rfl

private theorem constants_comparison {T' T : Scheme.{t}} (g : T' ⟶ T) :
    ∃ e : constantSheaf (proEtaleModelTopology T) CommRingCat.{t + 1} ⋙
        transportedRingInverseImage g ≅
      constantSheaf (proEtaleModelTopology T') CommRingCat.{t + 1},
      ∀ B, e.hom.app B = constantInverseImageMap g B := by
  let := proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T.ProEt ⥤ proEtaleSiteModel T).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).functor.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let F := proEtaleModelBaseChange g
  let : PreservesFiniteLimits F := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt) ⋙ proEtaleBaseChange g ⋙ AsSmall.up)
    infer_instance
  let τ := (AsSmall.up : T.ProEt ⥤ proEtaleSiteModel T).obj (⊤_ T.ProEt)
  have hτ : IsTerminal τ :=
    (terminalIsTerminal (C := T.ProEt)).isTerminalObj AsSmall.up _
  let e := F.constantSheafsheafPullbackIso CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T') hτ (hτ.isTerminalObj F _)
  exact ⟨e, fun B ↦ constantIso_hom (proEtaleModelTopology T)
    (proEtaleModelTopology T') F hτ (hτ.isTerminalObj F _) B⟩

private theorem ringMap_naturality {T' T : Scheme.{t}} (g : T' ⟶ T)
    {R S : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (inverse g).map
        ((sheafCompose (proEtaleModelTopology T) (CategoryTheory.forget CommRingCat)).map φ) ≫
      ringUnderlyingMap g S =
    ringUnderlyingMap g R ≫
      (sheafCompose (proEtaleModelTopology T') (CategoryTheory.forget CommRingCat)).map
        ((transportedRingInverseImage g).map φ) := by
  let := proEtaleModelBaseChange_isContinuous g
  have hr (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
      ((adjunction g).homEquiv _ _) (ringUnderlyingMap g O) =
        (sheafCompose (proEtaleModelTopology T) (CategoryTheory.forget CommRingCat)).map
          (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
            (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O) := by
    change ((adjunction g).homEquiv _ _)
      (((adjunction g).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  apply ((adjunction g).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, hr S]
  erw [Adjunction.homEquiv_naturality_right, hr R]
  have h := ((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.naturality φ
  have hh := congrArg
    (sheafCompose (proEtaleModelTopology T) (CategoryTheory.forget CommRingCat)).map h
  simp only [Functor.map_comp] at hh
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun z ↦ z.hom.app U x) hh

private theorem algebra_ext_by_unit
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
    {O : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (a b : SheafOfModules.AlgebraicInverseImage L O B)
    (hr : a.ringUnderlying.hom = b.ringUnderlying.hom)
    (hm : a.modules = b.modules)
    (hu : ∀ M, HEq ((adj.homEquiv _ _) (a.moduleUnderlying.inv.app M))
      ((adj.homEquiv _ _) (b.moduleUnderlying.inv.app M))) : a = b := by
  rcases a with ⟨ar, aa, am, az, ao, af, au, ma, mz, ms⟩
  rcases b with ⟨br, ba, bm, bz, bo, bf, bu, na, nz, ns⟩
  dsimp only at hr hm hu
  have he : ar = br := Iso.ext hr
  cases he
  cases hm
  have hi : au.inv = bu.inv := by
    apply NatTrans.ext
    funext M
    apply (adj.homEquiv _ _).injective
    exact eq_of_heq (hu M)
  have he' : au = bu := by
    apply Iso.ext
    apply (cancel_epi au.inv).mp
    rw [Iso.inv_hom_id, hi, Iso.inv_hom_id]
  cases he'
  rfl

end GeometricConstruction
/-- The unique algebraic lift with all data fields fixed by the actual ring and
module inverse images and their adjunction units. `HEq` only handles the dependent
codomains until the preceding equality of ring functors is substituted.
Source: Stacks 00YV, 03D2 and 0H7J
(blueprint: lem-sf-cbc-completed-pullback-unit-tower).
Proof: the set-adjoint of the ring unit is the canonical underlying-set comparison.
Finite-product preservation makes it invertible and preserves all ring-operation
graphs. Pullback along that unit is the module inverse image; the set-adjoint of
its unit is invertible and preserves addition, zero and the scalar-action graph.
These statements follow first on the Kan-extension generators, then after
sheafification. The canonical constant-section map is invertible and natural.
They assemble to InverseImageData with exactly the displayed data. Conversely the
predicate fixes the ring functor, the module functors, both underlying comparisons,
and the constant comparison componentwise. All remaining fields are propositions,
so extensionality and proof irrelevance give uniqueness. -/
theorem canonicalInverseImageData_existsUnique {T' T : Scheme.{t}} (g : T' ⟶ T) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃! F : ConstantCompletion.InverseImageData (inverse g),
      F.rings = transportedRingInverseImage g ∧
      (∀ O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1},
        HEq (F.algebra O).ringUnderlying.hom (ringUnderlyingMap g O) ∧
        HEq (F.algebra O).modules (transportedModuleInverseImage g O) ∧
        ∀ M : ConstantCompletion.Mod O,
          HEq ((adjunction g).homEquiv _ _ ((F.algebra O).moduleUnderlying.inv.app M))
            ((ConstantCompletion.underlying O).map
              ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
                (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
                (K := proEtaleModelTopology T')
                (R := siteModuleRings ((transportedRingInverseImage g).obj O))
                (transportedRingUnit g O)).unit.app M))) ∧
      ∀ B : CommRingCat.{t + 1},
        HEq (F.constants.hom.app B) (constantInverseImageMap g B) := by
  let := proEtaleModelBaseChange_isContinuous g
  choose A hAr hAM hAu using canonical_algebra_exists g
  obtain ⟨e, he⟩ := constants_comparison g
  let F : ConstantCompletion.InverseImageData (inverse g) :=
    { rings := transportedRingInverseImage g
      algebra := A
      ring_naturality := fun {R S} φ ↦ by
        rw [hAr R, hAr S]
        exact ringMap_naturality g φ
      constants := e }
  refine ⟨F, ⟨rfl, fun O ↦ ⟨heq_of_eq (hAr O), heq_of_eq (hAM O), hAu O⟩,
    fun B ↦ heq_of_eq (he B)⟩, ?_⟩
  intro G hG
  rcases G with ⟨gr, ga, gn, gc⟩
  rcases hG with ⟨hR, hA, hC⟩
  dsimp only at hR
  cases hR
  have ha : ga = A := by
    funext O
    apply algebra_ext_by_unit (adjunction g) (ga O) (A O)
    · exact (eq_of_heq (hA O).1).trans (hAr O).symm
    · exact (eq_of_heq (hA O).2.1).trans (hAM O).symm
    · intro M
      exact ((hA O).2.2 M).trans (hAu O M).symm
  have hc : gc = e := by
    apply Iso.ext
    apply NatTrans.ext
    funext B
    exact (eq_of_heq (hC B)).trans (he B).symm
  cases ha
  cases hc
  rfl


/-- The canonical algebraic inverse image, chosen from a predicate determining all
its data fields by actual pullbacks and unit-normalized comparisons.
Source: Stacks 00YV, 03D2 and 0H7J
(blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def canonicalInverseImageData {T' T : Scheme.{t}} (g : T' ⟶ T) :
    ConstantCompletion.InverseImageData (inverse g) :=
  (canonicalInverseImageData_existsUnique g).exists.choose

/-- The geometric morphism with its canonical algebraic lift, using the published
finite-product construction of ring and module inverse images.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def morphism {T' T : Scheme.{t}} (g : T' ⟶ T) : Morphism (site T) (site T') where
  inverse := inverse g
  direct := direct g
  adjunction := adjunction g
  finiteLimits := inverse_finiteLimits g
  algebra := canonicalInverseImageData g

/-- Ordinary constant towers evaluated at any level are the identity functor.
Source: Stacks 0941 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def diagonalEvaluation (S : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :
    S.delta A ⋙ S.evaluate A n ≅ 𝟭 (S.derived A) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)) ≪≫
    Functor.mapDerivedCategoryIdIso (S.modules A)

/-- The projection of the actual derived strict limit, obtained by evaluating the
constant/limit adjunction counit. On a K-injective tower it is the limit projection.
Source: Stacks 0941 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def projection (S : Site.{u}) (A : Type u) [CommRing A]
    (M : S.towerDerived A) (n : ℕ) :
    (S.rlim A).obj M ⟶ (S.evaluate A n).obj M :=
  (diagonalEvaluation S A n).inv.app ((S.rlim A).obj M) ≫
    (S.evaluate A n).map ((S.deltaAdjunction A).counit.app M)

/-- The projection to the finite reduction, with its quotient action retained.
Source: Stacks 099M (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finiteProjection (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (N : S.derived A) (n : ℕ) :
    (S.completion A I).obj N ⟶
      (S.finiteRestriction A I n).obj ((S.finiteReduction A I n).obj N) :=
  projection S A ((S.reduction A I).obj N) n ≫
    (S.finiteEvaluationIso A I n).hom.app N

/-- The inverse reduced unit prescribed by clause (i): the scalar-extension adjunct
of the specified limit projection, before forgetting its finite coefficient action.
Source: Stacks 099M (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finiteInverse (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (N : S.derived A) (n : ℕ) :
    (S.finiteReduction A I n).obj ((S.completion A I).obj N) ⟶
      (S.finiteReduction A I n).obj N :=
  ((S.finiteAdjunction A I n).homEquiv _ _).symm (finiteProjection S A I N n)

/-- The finite coefficient target of the pulled-back strict quotient tower.
Source: Stacks 099N(5) (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def targetEvaluation {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.evaluate A n).obj ((f.towerPull A).obj ((V.reduction A I).obj K)) ≅
      (U.finiteRestriction A I n).obj
        ((f.pull (quotientRing A I n)).obj ((V.finiteReduction A I n).obj K)) :=
  (f.evaluatePullIso A n).app ((V.reduction A I).obj K) ≪≫
    (f.pull A).mapIso ((V.finiteEvaluationIso A I n).app K) ≪≫
      (f.finiteRestrictionPullIso A I n).app ((V.finiteReduction A I n).obj K)

/-- The constant-coefficient projection-induced alpha of corrected clause (iii).
It is the scalar-extension adjunct of the limit projection after R lim of tau,
exactly the constant-coefficient presentation in Stacks 099N(5).
Source: Stacks 099N(5) (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finitePullbackProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.finiteReduction A I n).obj ((U.completion A I).obj ((f.pull A).obj K)) ⟶
      (f.pull (quotientRing A I n)).obj ((V.finiteReduction A I n).obj K) :=
  ((U.finiteAdjunction A I n).homEquiv _ _).symm
    ((U.rlim A).map ((f.reductionPullIso A I).inv.app K) ≫
      projection U A ((f.towerPull A).obj ((V.reduction A I).obj K)) n ≫
        (targetEvaluation f A I K n).hom)

section TowerProof
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem projection_naturality (S : Site.{u}) (A : Type u) [CommRing A]
    {M N : S.towerDerived A} (f : M ⟶ N) (n : ℕ) :
    (S.rlim A).map f ≫ projection S A N n =
      projection S A M n ≫ (S.evaluate A n).map f := by
  have h := (diagonalEvaluation S A n).inv.naturality ((S.rlim A).map f)
  change (S.rlim A).map f ≫ (diagonalEvaluation S A n).inv.app _ =
    (diagonalEvaluation S A n).inv.app _ ≫
      (S.evaluate A n).map ((S.delta A).map ((S.rlim A).map f)) at h
  have hc := (S.deltaAdjunction A).counit.naturality f
  change (S.delta A).map ((S.rlim A).map f) ≫ _ = _ ≫ f at hc
  dsimp only [projection]
  rw [← Category.assoc, h, Category.assoc, ← CategoryTheory.Functor.map_comp, hc,
    CategoryTheory.Functor.map_comp, Category.assoc]

private theorem finiteInverse_unit (S : Site.{u}) (A : Type u) [CommRing A]
    (d : CompleteCoefficientDatum A) (N : S.derived A) (n : ℕ) :
    (S.finiteReduction A d.ideal n).map ((S.unit A d.ideal).app N) ≫
      finiteInverse S A d.ideal N n = 𝟙 _ := by
  apply ((S.finiteAdjunction A d.ideal n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [finiteInverse, Equiv.apply_symm_apply]
  change (S.unit A d.ideal).app N ≫ finiteProjection S A d.ideal N n =
    (S.finiteAdjunction A d.ideal n).unit.app N ≫ _
  rw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  have h := (completionFiniteReduction S A d N n).2
  dsimp only [finiteProjection, projection, diagonalEvaluation]
  convert h using 1
  simp only [Category.assoc]
  rfl

private theorem reduction_unit_isIso (S : Site.{u}) (A : Type u) [CommRing A]
    (d : CompleteCoefficientDatum A) (N : S.derived A) :
    IsIso ((S.reduction A d.ideal).map ((S.unit A d.ideal).app N)) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro n
  let E := S.evaluateModule A n.unop
  have hf : IsIso ((S.finiteReduction A d.ideal n.unop).map
      ((S.unit A d.ideal).app N)) := (completionFiniteReduction S A d N n.unop).1
  have he : IsIso ((S.evaluate A n.unop).map
      ((S.reduction A d.ideal).map ((S.unit A d.ideal).app N))) :=
    (NatIso.isIso_map_iff (S.finiteEvaluationIso A d.ideal n.unop)
      ((S.unit A d.ideal).app N)).mpr (by dsimp only [Functor.comp_map]; infer_instance)
  exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i)
    ((S.reduction A d.ideal).map ((S.unit A d.ideal).app N))).mpr
      (by dsimp only [Functor.comp_map]; infer_instance)

private theorem finiteInverse_evaluation (S : Site.{u}) (A : Type u) [CommRing A]
    (d : CompleteCoefficientDatum A)
    (b : S.completion A d.ideal ⋙ S.reduction A d.ideal ≅ S.reduction A d.ideal)
    (hb : ∀ N, b.inv.app N = (S.reduction A d.ideal).map ((S.unit A d.ideal).app N))
    (N : S.derived A) (n : ℕ) :
    (S.evaluate A n).map (b.hom.app N) ≫
        (S.finiteEvaluationIso A d.ideal n).hom.app N =
      (S.finiteEvaluationIso A d.ideal n).hom.app ((S.completion A d.ideal).obj N) ≫
        (S.finiteRestriction A d.ideal n).map (finiteInverse S A d.ideal N n) := by
  apply (cancel_epi ((S.evaluate A n).map (b.inv.app N))).mp
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, hb]
  have hn := (S.finiteEvaluationIso A d.ideal n).hom.naturality
    ((S.unit A d.ideal).app N)
  change (S.evaluate A n).map ((S.reduction A d.ideal).map
    ((S.unit A d.ideal).app N)) ≫ _ = _ ≫
      (S.finiteRestriction A d.ideal n).map
        ((S.finiteReduction A d.ideal n).map ((S.unit A d.ideal).app N)) at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, finiteInverse_unit,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem finitePullbackProjection_eq {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    finitePullbackProjection f A I K n =
      finiteInverse U A I ((f.pull A).obj K) n ≫ (f.finitePullIso A I n).hom.app K := by
  apply ((U.finiteAdjunction A I n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [finitePullbackProjection, finiteInverse, Equiv.apply_symm_apply]
  dsimp only [Site.completion, ConstantCompletion.completion, Functor.comp_obj]
  rw [← Category.assoc]
  erw [projection_naturality]
  rw [Category.assoc]
  have ht : (U.evaluate A n).map ((f.reductionPullIso A I).inv.app K) ≫
      (targetEvaluation f A I K n).hom =
      (U.finiteEvaluationIso A I n).hom.app ((f.pull A).obj K) ≫
        (U.finiteRestriction A I n).map ((f.finitePullIso A I n).hom.app K) :=
    reductionPullFiniteEvaluation f A I K n
  rw [ht]
  simp only [finiteProjection, Category.assoc]

/-- Completion-unit reduction, strict tensor/pullback comparison, and the normalized
completed-pullback reduction, with no completeness assumption in (i) or (ii).

Source: smooth-purity blueprint, fix-lem-exchanges Proof Steps 2 and 5; Stacks
099M, 099N, 03EL, 06YS and 0G7E
(blueprint: lem-sf-cbc-completed-pullback-unit-tower).

Proof, following the node:
1. Represent N by one flat-term K-flat complex Q. On the diagram site the
   diagonal of Q is K-flat: tensor and acyclicity are levelwise. Thus the universal
   derived quotient presentation is represented by the strict tower Q tensor P_n.
2. Every restricted finite-quotient complex is derived I-complete, since the
   elements of I act nilpotently. The Koszul/quotient reflector and scalar
   adjunction make F_n(eta) invertible. The normalized K-injective strict-limit
   model gives p_n eta = u_n, hence its adjunct b_n satisfies b_n F_n(eta)=1.
   Thus b_n is the specified inverse.
3. The cone of R(eta) evaluates to zero at every level. Kernels, cokernels and
   cohomology of strict towers are levelwise, so its representative is acyclic.
   Localization makes its cone zero, hence R(eta) invertible. Naturality of eta
   gives the natural strict inverse b, with evaluated inverse exactly b_n.
4. On Q the canonical tensor/pullback comparison commutes with each quotient
   transition, naturally in chain maps and chain homotopies. Pullback preserves
   flat-term K-flat representatives and quasi-isomorphisms. Localization of this
   resolving class descends the comparison, independently of Q. It is precisely
   the existing, representative-normalized reductionPullIso in inverse direction.
5. Compose this tau with b at Lg*K. This gives q as a natural isomorphism in the
   derived category of strict towers, so all its evaluated maps respect transitions.
6. For complete K, Stacks 099N(2),(5) and completedPullbackAdjunction express
   completed inverse image in constant-coefficient categories as C(Lg*K), with
   its R lim(tau) presentation. Naturality of the limit counit identifies its
   projection with tau_n p_n. Naturality of scalar extension makes tau_n b_n
   its adjunct, exactly finitePullbackProjection of corrected clause (iii).
   Its restriction of scalars is the component of the isomorphism q up to the
   finite comparison isomorphisms. Restriction of scalars detects
   quasi-isomorphisms, hence is conservative, so this finite-coefficient map is
   invertible, the last conjunct. No completed-ring coefficient arrow is
   identified here. -/
theorem completedPullbackUnitTower {T' T : Scheme.{t}} (g : T' ⟶ T)
    (A : Type (t + 1)) [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃ b : (site T').completion A d.ideal ⋙ (site T').reduction A d.ideal ≅
        (site T').reduction A d.ideal,
      (∀ N : (site T').derived A,
        b.inv.app N = ((site T').reduction A d.ideal).map
          (((site T').unit A d.ideal).app N)) ∧
      (∀ (N : (site T').derived A) (n : ℕ),
        ((site T').evaluate A n).map (b.hom.app N) ≫
            ((site T').finiteEvaluationIso A d.ideal n).hom.app N =
          ((site T').finiteEvaluationIso A d.ideal n).hom.app
              (((site T').completion A d.ideal).obj N) ≫
            ((site T').finiteRestriction A d.ideal n).map
              (finiteInverse (site T') A d.ideal N n)) ∧
      ∃ q : (morphism g).pull A ⋙ (site T').completion A d.ideal ⋙
            (site T').reduction A d.ideal ≅
          (site T).reduction A d.ideal ⋙ (morphism g).towerPull A,
        (∀ K : (site T).derived A,
          q.hom.app K = b.hom.app (((morphism g).pull A).obj K) ≫
            ((morphism g).reductionPullIso A d.ideal).inv.app K) ∧
        ∀ K : (site T).derived A, (site T).IsComplete A d.ideal K → ∀ n : ℕ,
          ((site T').evaluate A n).map (q.hom.app K) ≫
              (targetEvaluation (morphism g) A d.ideal K n).hom =
            ((site T').finiteEvaluationIso A d.ideal n).hom.app
                (((site T').completion A d.ideal).obj (((morphism g).pull A).obj K)) ≫
              ((site T').finiteRestriction A d.ideal n).map
                (finitePullbackProjection (morphism g) A d.ideal K n) ∧
          IsIso (finitePullbackProjection (morphism g) A d.ideal K n) := by
  let := d.noetherian
  let S := site T'
  let f := morphism g
  let η := Functor.whiskerRight (S.unit A d.ideal) (S.reduction A d.ideal)
  have (N : S.derived A) : IsIso (η.app N) := reduction_unit_isIso S A d N
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let b : S.completion A d.ideal ⋙ S.reduction A d.ideal ≅ S.reduction A d.ideal :=
    (asIso η).symm
  have hb (N : S.derived A) : b.inv.app N =
      (S.reduction A d.ideal).map ((S.unit A d.ideal).app N) := rfl
  have he := finiteInverse_evaluation S A d b hb
  refine ⟨b, hb, he, ?_⟩
  let q : f.pull A ⋙ S.completion A d.ideal ⋙ S.reduction A d.ideal ≅
      (site T).reduction A d.ideal ⋙ f.towerPull A :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft (f.pull A) b ≪≫ (f.reductionPullIso A d.ideal).symm
  have hq (K : (site T).derived A) : q.hom.app K =
      b.hom.app ((f.pull A).obj K) ≫ (f.reductionPullIso A d.ideal).inv.app K := by
    change 𝟙 _ ≫ b.hom.app ((f.pull A).obj K) ≫
      (f.reductionPullIso A d.ideal).inv.app K = _
    rw [Category.id_comp]
  refine ⟨q, hq, ?_⟩
  intro K _ n
  have hη := (completionFiniteReduction S A d ((f.pull A).obj K) n).1
  have hfinite : IsIso (finiteInverse S A d.ideal ((f.pull A).obj K) n) := by
    apply (isIso_comp_left_iff
      ((S.finiteReduction A d.ideal n).map ((S.unit A d.ideal).app _)) _).mp
    rw [finiteInverse_unit]
    infer_instance
  have ha := finitePullbackProjection_eq f A d.ideal K n
  constructor
  · change (S.evaluate A n).map (q.hom.app K) ≫
        (targetEvaluation f A d.ideal K n).hom =
      (S.finiteEvaluationIso A d.ideal n).hom.app
        ((S.completion A d.ideal).obj ((f.pull A).obj K)) ≫
      (S.finiteRestriction A d.ideal n).map (finitePullbackProjection f A d.ideal K n)
    rw [hq, CategoryTheory.Functor.map_comp, Category.assoc]
    have ht : (S.evaluate A n).map ((f.reductionPullIso A d.ideal).inv.app K) ≫
        (targetEvaluation f A d.ideal K n).hom =
        (S.finiteEvaluationIso A d.ideal n).hom.app ((f.pull A).obj K) ≫
          (S.finiteRestriction A d.ideal n).map ((f.finitePullIso A d.ideal n).hom.app K) :=
      reductionPullFiniteEvaluation f A d.ideal K n
    rw [ht, ← Category.assoc, he, Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← ha]
  · rw [ha]
    infer_instance

end TowerProof

end AlgebraicGeometry.Scheme.CompletedPullbackUnitTower
