/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Complements on sheaves of modules on a scheme

## Sections of a kernel of `𝒪_X`-modules

Limits in `X.Modules` are computed section-wise, because evaluation at an open subset
preserves finite limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`). This file
records the resulting concrete description of the sections of a categorical kernel: over any
open `U`, the sections of `kernel f` are exactly the sections of the source that `f` kills.

This is the tool that turns a sheaf of modules defined as a kernel — as the ideal sheaf of a
`Scheme.IdealSheafData` is in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` —
into a computable object.

## Restriction to an open subset and pullback

Mathlib identifies, via `AlgebraicGeometry.Scheme.Modules.overEquiv`, sheaves of modules over
the localized sheaf of rings `𝒪_Y|_U` with sheaves of modules on the open subscheme `U`. We
record how that identification interacts with the unit object and with the pullback functor
along the open immersion `U.ι`, and deduce that invertibility of a sheaf of modules is stable
under pullback along an arbitrary morphism of schemes.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `SheafOfModules.IsInvertible.pullback`: the pullback of an invertible sheaf of modules along
  a morphism of schemes is invertible.

## Implementation notes

The argument for `SheafOfModules.IsInvertible.pullback` only uses restriction to opens and the
pullback of sheaves of modules; nothing about it is specific to schemes. Once the pullback
functor is available for morphisms of ringed sites, the statement belongs next to
`SheafOfModules.IsInvertible` in that generality.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section Kernel

variable {X : Scheme.{u}} (U : X.Opens)
  {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N)

/-- **The sections of a kernel are the kernel of the sections.** Over any open `U`, the image
of `kernel.ι f` on sections is the set of sections of `M` killed by `f`.

This is stated for `SheafOfModules X.ringCatSheaf` rather than for the definitionally equal
`X.Modules`, because instance search for `PreservesLimit` does not see through the latter. -/
lemma range_map_kernelι :
    Set.range ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) =
      { x | (SheafOfModules.evaluation X.ringCatSheaf (op U)).map f x = 0 } := by
  set G := SheafOfModules.evaluation X.ringCatSheaf (op U) with hG
  have key : ((PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ≫
      G.map (kernel.ι f)) = ModuleCat.ofHom (LinearMap.ker (G.map f).hom).subtype := by
    simp [ModuleCat.kernelIsoKer_inv_kernel_ι]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change G.map f (G.map (kernel.ι f) y) = 0
    rw [← ConcreteCategory.comp_apply, ← G.map_comp, kernel.condition, G.map_zero]
    rfl
  · intro hx
    refine ⟨(PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ⟨x, hx⟩, ?_⟩
    have h2 := ConcreteCategory.congr_hom key ⟨x, hx⟩
    simp only [Iso.trans_inv, ConcreteCategory.comp_apply] at h2
    exact h2

lemma map_kernelι_eq :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) =
      (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f).hom ≫
        kernel.ι _ := by
  rw [← PreservesKernel.iso_inv_ι]
  simp

instance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) := by
  rw [map_kernelι_eq]
  infer_instance

/-- `kernel.ι f` is injective on sections over any open, not merely a monomorphism. -/
lemma injective_map_kernelι :
    Function.Injective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

end Kernel

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

namespace Modules

noncomputable section

/-- The pullback of the structure sheaf along a morphism of schemes is the structure sheaf. -/
def pullbackObjUnitIsoUnit (f : X ⟶ Y) :
    (Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : IsIso (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- The restriction of the structure sheaf to an open subset, as a sheaf of modules over
the localized sheaf of rings, is the unit object. -/
def overFunctorObjUnitIsoUnit (U : Y.Opens) :
    (SheafOfModules.overFunctor Y.ringCatSheaf U).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  Iso.refl _

/-- Under the equivalence `Scheme.Modules.overEquiv`, the unit object corresponds to the unit
object.  The composite runs along the top of

```text
  overEquiv U (𝒪_Y|_U) --- overEquiv U (overFunctor U 𝒪_Y) --- restrict U.ι 𝒪_Y --- 𝒪_U
```

where the middle identification is `Scheme.Modules.overFunctorEquiv U`. -/
def overEquivObjUnitIsoUnit (U : Y.Opens) :
    (overEquiv U).functor.obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (overEquiv U).functor.mapIso (overFunctorObjUnitIsoUnit U).symm ≪≫
    (overFunctorEquiv U).app _ ≪≫ restrictUnitIso U.ι

/-- Under the equivalence `Scheme.Modules.overEquiv`, the restriction `M.over U` of a sheaf
of modules to an open subset corresponds to its pullback along the open immersion `U.ι`:

```text
                   overFunctorEquiv U            restrictFunctorIsoPullback U.ι
  overEquiv U (M|_U) --------------> restrict U.ι M --------------> (U.ι)^* M
```
-/
def overEquivObjOverIsoPullbackObj (M : Y.Modules) (U : Y.Opens) :
    (overEquiv U).functor.obj (M.over U) ≅ (Modules.pullback U.ι).obj M :=
  (overFunctorEquiv U).app M ≪≫ (restrictFunctorIsoPullback U.ι).app M

/-- If the restriction of `M` to an open subset `U` is trivial, then so is its pullback
along the open immersion `U.ι`. -/
def pullbackObjIsoUnitOfOverIsoUnit {M : Y.Modules} {U : Y.Opens}
    (e : M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)) :
    (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (overEquivObjOverIsoPullbackObj M U).symm ≪≫ (overEquiv U).functor.mapIso e ≪≫
    overEquivObjUnitIsoUnit U

/-- Conversely, if the pullback of `M` along an open immersion `U.ι` is trivial, then so is
the restriction of `M` to `U`. -/
def overIsoUnitOfPullbackObjIsoUnit {M : Y.Modules} {U : Y.Opens}
    (e : (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  (overEquiv U).functor.preimageIso
    (overEquivObjOverIsoPullbackObj M U ≪≫ e ≪≫ (overEquivObjUnitIsoUnit U).symm)

/-- The key local computation behind functoriality of the Picard presheaf: if `M` is trivial
on an open subset `U` of `Y`, then its pullback along `g : X ⟶ Y` is trivial on `g ⁻¹ᵁ U`.

The proof transports `e` around the restriction square

```text
             (g ⁻¹ᵁ U).ι
  g ⁻¹ᵁ U -----------------> X
     |                       |
  g ∣_ U                     g
     |                       |
     v                       v
     U ---------U.ι--------> Y
```

which reads `(g ⁻¹ᵁ U).ι ≫ g = (g ∣_ U) ≫ U.ι` (`AlgebraicGeometry.morphismRestrict_ι`), so
that `((g ⁻¹ᵁ U).ι)^* g^* M ≅ (g ∣_ U)^* (U.ι)^* M`. -/
def overPullbackObjIsoUnitOfOverIsoUnit (g : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)) :
    ((Modules.pullback g).obj M).over (g ⁻¹ᵁ U) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (g ⁻¹ᵁ U)) :=
  overIsoUnitOfPullbackObjIsoUnit
    ((Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
      (Modules.pullbackCongr (morphismRestrict_ι g U).symm).app M ≪≫
      ((Modules.pullbackComp (g ∣_ U) U.ι).symm).app M ≪≫
      (Modules.pullback (g ∣_ U)).mapIso (pullbackObjIsoUnitOfOverIsoUnit e) ≪≫
      pullbackObjUnitIsoUnit (g ∣_ U))

end

end Modules

/-- The pullback of an invertible sheaf of modules along a morphism of schemes is invertible. -/
theorem _root_.SheafOfModules.IsInvertible.pullback {g : X ⟶ Y} {M : Y.Modules}
    (hM : M.IsInvertible) : ((Modules.pullback g).obj M).IsInvertible := by
  obtain ⟨q, hq⟩ := hM.exists_isInvertibleData
  have := hq
  refine SheafOfModules.isInvertible_of_forall_over_unit (M := (Modules.pullback g).obj M)
    (fun i : q.I ↦ g ⁻¹ᵁ q.X i) ?_ ?_
  · rw [Opens.coversTop_iff]
    exact ((Opens.coversTop_iff _ _).mp q.coversTop).comap g.base.hom
  · intro i
    obtain ⟨hu⟩ := SheafOfModules.LocalGeneratorsData.IsInvertibleData.nonempty_unique (q := q) i
    let _ := hu
    exact ⟨Modules.overPullbackObjIsoUnitOfOverIsoUnit g M (q.X i)
      ((asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeIsoUnit _)⟩

end AlgebraicGeometry.Scheme
