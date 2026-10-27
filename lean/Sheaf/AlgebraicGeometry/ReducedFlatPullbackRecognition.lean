module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Subobject.Limits
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Recognition of reduced flat pullbacks of closed subschemes

Source: Stacks Project, Schemes, Tags 01JU, 01JT, 01J3 and 01J4; Modules, Tag 02N4
(blueprint: lem-trf-reduced-flat-pullback-recognition).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A reduced flat pullback of a closed immersion is the reduced induced closed subscheme
on the inverse image of its closed image. The canonical ideal map is injective on every
open and its image is the vanishing ideal of that inverse image.

Source: Stacks Project, Schemes, Tags 01JU, 01JT, 01J3 and 01J4; Modules, Tag 02N4
(blueprint: lem-trf-reduced-flat-pullback-recognition).

The closed set `i.ker.support` is the image of the closed immersion `i`: `support_ker`
identifies it with the closure of the image, which is already closed. Thus its preimage
is precisely the closed set named in the node. The ideal map is the tensor pullback of
the ideal inclusion followed by the existing canonical structure-module comparison.

Proof:
1. The base-change ideal-image theorem identifies the kernel ideal of
   `pullback.snd i g` with the image of the pulled-back ideal inclusion. Its chosen
   adjunction differs from the structure-map adjunction by `leftAdjointUniq`.
   Naturality expresses the change as precomposition with an isomorphism, which
   leaves the image subobject unchanged.
2. Exactness of flat module pullback preserves the monomorphism `i.ker.toModulesι`.
   The structure-module comparison is an isomorphism, so the composite is monic.
   The image equality gives an isomorphism to the kernel ideal compatible with
   inclusion. On every open, its composite with the injective kernel-ideal
   inclusion is injective.
3. `Scheme.Pullback.range_snd` identifies the image with the inverse image of
   `range i`. Since `i` is a closed immersion, `support_ker` identifies its support
   with that closed range. Apply the uniqueness clause of
   `reduced_induced_closed_subscheme` to the reduced pullback and this image.
   Substitute the resulting equality of kernel and vanishing ideals into step 1.
No reducedness of `T`, finiteness condition, or Noetherian hypothesis is used. -/
theorem reduced_flat_pullback_recognition {T X Y : Scheme.{u}}
    (i : T ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X) [Flat g]
    [IsReduced (pullback i g)] :
    IsClosedImmersion (pullback.snd i g) ∧
    Set.range (pullback.snd i g) = g ⁻¹' Set.range i ∧
    (∀ U : Y.Opens, Function.Injective
      (((Scheme.Modules.tensorPullback g).map i.ker.toModulesι ≫
        Scheme.Modules.tensorPullbackObjUnitToUnit g).app U)) ∧
    imageSubobject ((Scheme.Modules.tensorPullback g).map i.ker.toModulesι ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit g) =
        Subobject.mk (Scheme.IdealSheafData.vanishingIdeal
          (i.ker.support.preimage g.continuous)).toModulesι ∧
    ∃! e : pullback i g ≅ (Scheme.IdealSheafData.vanishingIdeal
        (i.ker.support.preimage g.continuous)).subscheme,
      e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
        (i.ker.support.preimage g.continuous)).subschemeι = pullback.snd i g := by
  classical
  let F := Scheme.Modules.tensorPullback g
  let a := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction g)
  let a₀ := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let c := a.leftAdjointUniq a₀
  let ε := (a.homEquiv (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit Y.ringCatSheaf)).symm
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  have hε : ε = (c.app (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit g := by
    dsimp [ε, Scheme.Modules.tensorPullbackObjUnitToUnit]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [← c.hom.naturality_assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  let φ := F.map i.ker.toModulesι ≫ Scheme.Modules.tensorPullbackObjUnitToUnit g
  have himg : Subobject.mk (pullback.snd i g).ker.toModulesι = imageSubobject φ := by
    have h := (closedSubscheme_baseChange_ideal_image i g).2
    change Subobject.mk (pullback.snd i g).ker.toModulesι =
      imageSubobject (F.map i.ker.toModulesι ≫ ε) at h
    have hn : F.map i.ker.toModulesι ≫ (c.app _).hom =
        (c.app i.ker.toModules).hom ≫ F.map i.ker.toModulesι :=
      c.hom.naturality i.ker.toModulesι
    rw [hε, ← Category.assoc, hn, Category.assoc, imageSubobject_iso_comp] at h
    exact h
  have : PreservesFiniteLimits F := (flat_module_pullback_exact_pushforward_injective g).1.1
  have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit g) :=
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g).1
  have : Mono φ := inferInstance
  have hm : Subobject.mk φ = Subobject.mk (pullback.snd i g).ker.toModulesι :=
    (imageSubobject_mono φ).symm.trans himg.symm
  let e := Subobject.isoOfMkEqMk φ (pullback.snd i g).ker.toModulesι hm
  have he : e.hom ≫ (pullback.snd i g).ker.toModulesι = φ := by simp [e]
  have hinj (U : Y.Opens) : Function.Injective (φ.app U) := by
    have happ := congrArg (fun ψ ↦ ψ.app U) he
    rw [← happ]
    exact ((pullback.snd i g).ker.injective_toModulesι_app U).comp
      (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
  have hrange := Scheme.Pullback.range_snd i g
  have hs : Set.range i = (i.ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  have hW : Set.range (pullback.snd i g) =
      ((i.ker.support.preimage g.continuous) : Set Y) := by
    rw [hrange, hs]
    rfl
  obtain ⟨hker, hiso⟩ :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme Y
      (i.ker.support.preimage g.continuous)).2.2.2.2.2.2.2
        (pullback i g) (pullback.snd i g) hW
  refine ⟨inferInstance, hrange, hinj, ?_, hiso⟩
  exact himg.symm.trans (congrArg (fun J : Y.IdealSheafData ↦
    Subobject.mk J.toModulesι) hker)

end AlgebraicGeometry
