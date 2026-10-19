/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Exact finite-valued functors on finite continuous group sets

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BMV,
`pione-lemma-second-fundamental-functor`
(blueprint: lem-wf-exact-finite-gsets-forgetful).
-/

@[expose] public section

universe g u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ContAction

private lemma action_map_smul {G : Type g} [Group G] [TopologicalSpace G]
    {X Y : Action FintypeCat.{u} G} (f : X ⟶ Y) (a : G) (x : X.V) :
    f.hom (a • x) = a • f.hom x :=
  ConcreteCategory.congr_hom (f.comm a) x

private lemma continuous_of_limit {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {J : Type*} [SmallCategory J] [FinCategory J]
    {F : J ⥤ Action FintypeCat.{u} G} {c : Cone F} (hc : IsLimit c)
    (hF : ∀ j, (F.obj j).IsContinuous) : c.pt.IsContinuous := by
  have hc' := isLimitOfPreserves (Action.forget FintypeCat G ⋙ FintypeCat.incl) hc
  have (j : J) : ContinuousSMul G (F.obj j).V := hF j
  change ContinuousSMul G c.pt.V
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  have heq : (MulAction.stabilizer G x : Set G) =
      ⋂ j, (MulAction.stabilizer G ((c.π.app j).hom x) : Set G) := by
    ext a
    simp only [Set.mem_iInter]
    change (a • x = x) ↔ ∀ j, a • (c.π.app j).hom x = (c.π.app j).hom x
    constructor
    · intro ha j
      rw [← action_map_smul, ha]
    · intro ha
      apply (Types.isLimitEquivSections hc').injective
      apply Subtype.ext
      funext j
      change (c.π.app j).hom (a • x) = (c.π.app j).hom x
      rw [action_map_smul, ha j]
  rw [heq]
  exact isOpen_iInter_of_finite fun j ↦ stabilizer_isOpen G _

private lemma continuous_of_colimit {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {J : Type*} [SmallCategory J] [FinCategory J]
    {F : J ⥤ Action FintypeCat.{u} G} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, (F.obj j).IsContinuous) : c.pt.IsContinuous := by
  have hc' := isColimitOfPreserves (Action.forget FintypeCat G ⋙ FintypeCat.incl) hc
  have (j : J) : ContinuousSMul G (F.obj j).V := hF j
  change ContinuousSMul G c.pt.V
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc' x
  change (c.ι.app j).hom y = x at hy
  let y' : (F.obj j).V := y
  change (c.ι.app j).hom y' = x at hy
  rw [← hy]
  apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G y')
  · intro a ha
    change a • (c.ι.app j).hom y = (c.ι.app j).hom y
    rw [← action_map_smul, MulAction.mem_stabilizer_iff.mp ha]
  · exact stabilizer_isOpen G y'

private instance continuous_closed_limits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {J : Type*} [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact continuous_of_limit p.isLimit p.prop_diag_obj

private instance continuous_closed_colimits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {J : Type*} [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    exact continuous_of_colimit p.isColimit p.prop_diag_obj

private instance finite_limits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : HasFiniteLimits (ContAction FintypeCat.{u} G) where
  out _ := inferInstance

private instance finite_colimits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : HasFiniteColimits (ContAction FintypeCat.{u} G) where
  out _ := inferInstance

private instance inclusion_preserves_limits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : PreservesFiniteLimits
      (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{u}) (G := G))) where
  preservesFiniteLimits _ := inferInstance

private instance inclusion_preserves_colimits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : PreservesFiniteColimits
      (ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{u}) (G := G))) where
  preservesFiniteColimits _ := inferInstance

private instance forget_preserves_limits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : PreservesFiniteLimits
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) := by
  change PreservesFiniteLimits
    (ObjectProperty.ι _ ⋙ Action.forget FintypeCat G)
  exact comp_preservesFiniteLimits _ _

private instance forget_preserves_colimits {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : PreservesFiniteColimits
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) := by
  change PreservesFiniteColimits
    (ObjectProperty.ι _ ⋙ Action.forget FintypeCat G)
  exact comp_preservesFiniteColimits _ _

private lemma continuous_of_injective {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {X Y : Action FintypeCat.{u} G} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) (hY : Y.IsContinuous) : X.IsContinuous := by
  have : ContinuousSMul G Y.V := hY
  change ContinuousSMul G X.V
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  have heq : MulAction.stabilizer G x = MulAction.stabilizer G (f.hom x) := by
    ext a
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro ha
      rw [← action_map_smul, ha]
    · intro ha
      apply hf
      rw [action_map_smul, ha]
  rw [heq]
  exact stabilizer_isOpen G _

private instance preGalois {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : PreGaloisCategory (ContAction FintypeCat.{u} G) where
  hasQuotientsByFiniteGroups K _ _ := by
    obtain ⟨K', hK', hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv K
    exact hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    let I := ObjectProperty.ι (Action.IsContinuous (V := FintypeCat.{u}) (G := G))
    have : Mono i.hom := preserves_mono_of_preservesLimit I i
    let Z := CategoryTheory.FintypeCat.Action.imageComplement G i.hom
    let j := CategoryTheory.FintypeCat.Action.imageComplementIncl G i.hom
    have hZ : Z.IsContinuous := continuous_of_injective j Subtype.val_injective Y.property
    let Z' : ContAction FintypeCat.{u} G := ⟨Z, hZ⟩
    let j' : Z' ⟶ Y := ObjectProperty.homMk j
    have : Mono i.hom.hom := preserves_mono_of_preservesLimit (Action.forget _ _) i.hom
    have : Mono (FintypeCat.incl.map i.hom.hom) := inferInstance
    refine ⟨Z', j', ⟨?_⟩⟩
    apply isColimitOfReflects I
    refine (isColimitMapCoconeBinaryCofanEquiv I i j').symm ?_
    apply isColimitOfReflects (Action.forget FintypeCat G ⋙ FintypeCat.incl)
    exact (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm
      (Types.isCoprodOfMono (FintypeCat.incl.map i.hom.hom))

private instance forget_reflects_isos {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}).ReflectsIsomorphisms := by
  change (ObjectProperty.ι _ ⋙ Action.forget FintypeCat G).ReflectsIsomorphisms
  infer_instance

private instance forget_fiberFunctor {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : PreGaloisCategory.FiberFunctor
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) where
  preservesQuotientsByFiniteGroups K _ _ := by
    obtain ⟨K', hK', hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv K
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _

private instance galois {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : GaloisCategory (ContAction FintypeCat.{u} G) where
  hasFiberFunctor := ⟨forget₂ _ FintypeCat, ⟨inferInstance⟩⟩

private lemma exact_nonempty {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (X : ContAction FintypeCat.{u} G) (hX : Nonempty X.obj.V) : Nonempty (H.obj X) := by
  let U := forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl
  have : PreservesFiniteLimits U := comp_preservesFiniteLimits _ _
  let t : X ⟶ ⊤_ (ContAction FintypeCat.{u} G) := terminal.from X
  let ht := Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj U)
  have : Epi (U.map t) := (epi_iff_surjective _).mpr fun y ↦
    ⟨hX.some, (ht.uniq _).trans (ht.uniq _).symm⟩
  have : Epi t := Functor.epi_of_epi_map U inferInstance
  have : Epi (H.map t) := preserves_epi_of_preservesColimit H t
  let hHt := Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj H)
  obtain ⟨x, _⟩ := (epi_iff_surjective (H.map t)).mp inferInstance hHt.default
  exact ⟨x⟩

private noncomputable def exact_reflects_initial {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (X : ContAction FintypeCat.{u} G) (hX : IsEmpty (H.obj X)) : IsInitial X := by
  let U := forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl
  have : PreservesFiniteColimits U := comp_preservesFiniteColimits _ _
  have hUX : IsEmpty (U.obj X) := by
    refine ⟨fun x ↦ ?_⟩
    exact hX.false (exact_nonempty H X ⟨x⟩).some
  exact ((Types.initial_iff_empty _).mpr hUX).some.isInitialOfObj U

private instance exact_faithful {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] : H.Faithful where
  map_injective {X Y} f g hfg := by
    let e := equalizer.ι f g
    have : IsIso (equalizer.ι (H.map f) (H.map g)) := equalizer.ι_of_eq hfg
    have : IsIso (H.map e) := by
      dsimp [e]
      rw [← equalizerComparison_comp_π f g H]
      infer_instance
    obtain ⟨Z, j, ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand e
    have hcH := isColimitOfPreserves H hc
    have hcH' := (isColimitMapCoconeBinaryCofanEquiv H e j) hcH
    have hdis := ((Types.binaryCofan_isColimit_iff _).mp ⟨hcH'⟩).2.2.1
    have hZ : IsEmpty (H.obj Z) := by
      refine ⟨fun z ↦ ?_⟩
      obtain ⟨x, hx⟩ := (epi_iff_surjective (H.map e)).mp inferInstance (H.map j z)
      exact Set.disjoint_left.mp hdis ⟨x, hx⟩ ⟨z, rfl⟩
    have hiZ := exact_reflects_initial H Z hZ
    have : IsIso e := (BinaryCofan.isColimit_iff_isIso_inl hiZ _).mp ⟨hc⟩
    exact eq_of_epi_equalizer

private instance balanced {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Balanced (ContAction FintypeCat.{u} G) := by
  let U := forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl
  have : PreservesFiniteLimits U := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits U := comp_preservesFiniteColimits _ _
  exact Functor.balanced_of_preserves U

private instance exact_reflects_isos {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] : H.ReflectsIsomorphisms := by
  infer_instance

/-- An exact finite-valued functor on finite continuous `G`-sets is naturally isomorphic
 to the underlying-set functor. Source: Stacks Project, Tag 0BMV,
 `pione-lemma-second-fundamental-functor`
 (blueprint: lem-wf-exact-finite-gsets-forgetful).

Proof: finite limits and colimits of finite actions remain continuous. For limits,
point stabilizers are finite intersections of open stabilizers; for colimits, each
point comes from a diagram object and its stabilizer contains that of a representative.
An invariant complement to a subobject is continuous by injectivity. These observations
make continuous finite actions a Galois category, with the forgetful fibre functor.

An exact set-valued functor sends nonempty actions to nonempty sets: the map to the
terminal action is epic, and exactness preserves epimorphisms and the terminal object.
It therefore reflects initial objects. If two arrows have equal images, their equalizer
has an isomorphic image; its invariant complement has empty image, hence is initial.
The equalizer is consequently an isomorphism and the arrows agree. Thus the functor is
faithful, and it reflects isomorphisms since this category is balanced.

Lift the finite-valued functor to `FintypeCat`. Reflection of limits and colimits along
the inclusion shows that this lift is exact and is a fibre functor. Apply the library's
`CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor`, then whisker with the
inclusion into types. This uniqueness theorem uses the finite cofiltered-system argument
of Tag 0BMV via the pro-representability of fibre functors. -/
theorem nonempty_forget_iso_of_exact_finite {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [∀ X : ContAction FintypeCat.{u} G, Finite (H.obj X)] :
    Nonempty ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl) ≅ H) := by
  let Hf : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
    ObjectProperty.lift _ H (fun X ↦ inferInstance)
  have : PreservesFiniteLimits (Hf ⋙ FintypeCat.incl) :=
    inferInstanceAs (PreservesFiniteLimits H)
  have : PreservesFiniteColimits (Hf ⋙ FintypeCat.incl) :=
    inferInstanceAs (PreservesFiniteColimits H)
  have : PreservesFiniteLimits Hf :=
    preservesFiniteLimits_of_reflects_of_preserves Hf FintypeCat.incl
  have : PreservesFiniteColimits Hf :=
    preservesFiniteColimits_of_reflects_of_preserves Hf FintypeCat.incl
  have : (Hf ⋙ FintypeCat.incl).ReflectsIsomorphisms :=
    inferInstanceAs H.ReflectsIsomorphisms
  have : Hf.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp Hf FintypeCat.incl
  have : PreGaloisCategory.FiberFunctor Hf := {
    preservesQuotientsByFiniteGroups := fun K _ _ ↦ by
      obtain ⟨K', hK', hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv K
      exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm Hf }
  obtain ⟨e⟩ := PreGaloisCategory.nonempty_iso_of_fiberFunctor
    (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) Hf
  exact ⟨Functor.isoWhiskerRight e FintypeCat.incl⟩

end ContAction

#print axioms ContAction.nonempty_forget_iso_of_exact_finite
