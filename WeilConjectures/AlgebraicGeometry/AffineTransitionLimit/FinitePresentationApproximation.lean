/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.ClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.Separated
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Separated
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The finite presentation model system of a morphism of finite type

A morphism of finite type `f : X ⟶ S` of quasi-compact quasi-separated schemes exhibits `X` as a
cofiltered limit of schemes of finite presentation over `S` along closed immersions
(`AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation`,
`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation`, Stacks Project
Tag 09ZQ).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationApproximation

/-!
## The finite presentation model system of a morphism of finite type

A morphism `f : X ⟶ S` locally of finite type between quasi-compact quasi-separated schemes
exhibits `X` as a cofiltered limit of schemes of finite presentation over `S` with closed
immersions as transition morphisms, see
`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation` (Stacks Project
Tag 09ZQ).
-/

set_option backward.defeqAttrib.useBackward true

open TopologicalSpace in
/-- **Closed immersion into a scheme of finite presentation**: a quasi-compact quasi-separated
scheme `X` that is locally of finite type over a quasi-compact quasi-separated scheme `S`
admits a closed immersion over `S` into a scheme of finite presentation over `S`.

This is Stacks Project Tag 01ZE followed by the shrinking step of Tag 01ZG.
(Blueprint: `lemma:nagata-finite-type-fp-model-system`.) -/
theorem Scheme.Hom.exists_isClosedImmersion_locallyOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (i : X ⟶ Y), LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
      QuasiSeparated p ∧ IsClosedImmersion i ∧ i ≫ p = f := by
  obtain ⟨Y, p, i, hp, hpc, hpqs, hi, hcomp⟩ :=
    f.exists_isImmersion_locallyOfFinitePresentation
  have := hp; have := hpc; have := hpqs; have := hi
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨W, g, hWc, hg, hgW⟩ := i.exists_isCompact_isClosedImmersion
  have := hg
  have : QuasiCompact W.ι := W.quasiCompact_ι hWc
  refine ⟨W.toScheme, W.ι ≫ p, g, inferInstance, inferInstance, inferInstance, hg, ?_⟩
  rw [← Category.assoc, hgW, hcomp]

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of the closed subscheme cut out by an ideal sheaf `I` into the closed
subscheme cut out by a subideal sheaf of finite type of `I` is a closed immersion. -/
instance Scheme.IdealSheafData.isClosedImmersion_fgSubCone_π_app {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (J : (I.FGSub)ᵒᵖ) :
    IsClosedImmersion (I.fgSubCone.π.app J) := by
  have h : I.fgSubCone.π.app J ≫ (J.unop : Y.IdealSheafData).subschemeι = I.subschemeι :=
    inclusion_subschemeι _
  have : IsClosedImmersion (I.fgSubCone.π.app J ≫
      (J.unop : Y.IdealSheafData).subschemeι) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (J.unop : Y.IdealSheafData).subschemeι

/-- A **finite presentation approximation** of a morphism `f : X ⟶ S` is a cofiltered system
`D` of quasi-compact quasi-separated schemes of finite presentation over `S`, whose transition
morphisms are closed immersions, together with a limit cone with point `X` whose projections
are closed immersions compatible with `f`:

```
              X
    π.app i  ↙    ↓    ↘  π.app j
  D.obj i  ────────────⟶  D.obj j
                D.map g            ↘ p.app j
                                       S
```

Every morphism locally of finite type between quasi-compact quasi-separated schemes admits one
(`AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation`, Stacks Project
Tag 09ZQ). (Blueprint: `def:nagata-finite-type-fp-model-system`.) -/
structure Scheme.Hom.FinitePresentationApproximation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of models. -/
  D : I ⥤ Scheme.{u}
  /-- The structure morphisms of the models to `S`. -/
  p : D ⟶ (Functor.const I).obj S
  /-- Every model is locally of finite presentation over `S`. -/
  locallyOfFinitePresentation_p (i : I) : LocallyOfFinitePresentation (p.app i)
  /-- Every model is quasi-compact over `S`. -/
  quasiCompact_p (i : I) : QuasiCompact (p.app i)
  /-- Every model is quasi-separated over `S`. -/
  quasiSeparated_p (i : I) : QuasiSeparated (p.app i)
  /-- Every model is quasi-compact. -/
  compactSpace_obj (i : I) : CompactSpace (D.obj i)
  /-- Every model is quasi-separated. -/
  quasiSeparatedSpace_obj (i : I) : QuasiSeparatedSpace (D.obj i)
  /-- The transition morphisms of the system are closed immersions. -/
  isClosedImmersion_map {i j : I} (g : i ⟶ j) : IsClosedImmersion (D.map g)
  /-- The morphisms from `X` to the models. -/
  π : (Functor.const I).obj X ⟶ D
  /-- The morphisms from `X` to the models are closed immersions. -/
  isClosedImmersion_π (i : I) : IsClosedImmersion (π.app i)
  /-- `X` is the limit of the models. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The morphisms from `X` to the models are compatible with `f`. -/
  w (i : I) : π.app i ≫ p.app i = f

namespace Scheme.Hom.FinitePresentationApproximation

attribute [instance] smallCategory isCofiltered locallyOfFinitePresentation_p quasiCompact_p
  quasiSeparated_p compactSpace_obj quasiSeparatedSpace_obj isClosedImmersion_map
  isClosedImmersion_π

end Scheme.Hom.FinitePresentationApproximation

set_option backward.isDefEq.respectTransparency false in
/-- **The finite presentation model system of a morphism of finite type** (Stacks Project
Tag 09ZQ): a quasi-compact quasi-separated scheme `X` that is locally of finite type over a
quasi-compact quasi-separated scheme `S` is the cofiltered limit of a system of schemes of
finite presentation over `S` whose transition morphisms and whose morphisms from `X` are all
closed immersions.

The system is that of the closed subschemes of a finite presentation model `Y` of `X` over `S`
cut out by the subideal sheaves of finite type of the kernel of the closed immersion `X ⟶ Y`.
(Blueprint: `lemma:nagata-finite-type-fp-model-system`.) -/
@[stacks 09ZQ]
theorem Scheme.Hom.nonempty_finitePresentationApproximation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty f.FinitePresentationApproximation := by
  obtain ⟨Y, q, i, hq, hqc, hqs, hi, hcomp⟩ :=
    f.exists_isClosedImmersion_locallyOfFinitePresentation
  have := hq; have := hqc; have := hqs; have := hi
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  refine ⟨{
    I := (i.ker.FGSub)ᵒᵖ
    D := i.ker.fgSubDiagram
    p :=
      { app J := (J.unop : Y.IdealSheafData).subschemeι ≫ q
        naturality := by
          intro J J' g
          simp }
    locallyOfFinitePresentation_p J := by
      change LocallyOfFinitePresentation ((J.unop : Y.IdealSheafData).subschemeι ≫ q)
      infer_instance
    quasiCompact_p J := by
      change QuasiCompact ((J.unop : Y.IdealSheafData).subschemeι ≫ q)
      infer_instance
    quasiSeparated_p J := by
      change QuasiSeparated ((J.unop : Y.IdealSheafData).subschemeι ≫ q)
      infer_instance
    compactSpace_obj J := inferInstance
    quasiSeparatedSpace_obj J := inferInstance
    isClosedImmersion_map g := inferInstance
    π := (Functor.const _).map i.toImage ≫ i.ker.fgSubCone.π
    isClosedImmersion_π J := by
      change IsClosedImmersion (i.toImage ≫ i.ker.fgSubCone.π.app J)
      infer_instance
    isLimit := i.ker.isLimitFgSubCone.ofIsoLimit (Cone.ext (asIso i.toImage).symm fun J ↦ by simp)
    w J := by
      change (i.toImage ≫ i.ker.fgSubCone.π.app J) ≫
        (J.unop : Y.IdealSheafData).subschemeι ≫ q = f
      simpa using hcomp }⟩

/-- The interface consumed by the descent of a separated morphism of finite presentation to a
finite stage (Stacks Project Tag 01ZQ): all the instance arguments of
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated` are provided
by the fields of a finite presentation approximation. -/
example {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FinitePresentationApproximation)
    {X' : Scheme.{u}} (g : X' ⟶ X) [LocallyOfFinitePresentation g] [QuasiCompact g]
    [IsSeparated g] :
    ∃ (i : F.I) (Y : Scheme.{u}) (p : Y ⟶ F.D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : IsSeparated p) (h : X' ⟶ Y),
      IsPullback h g p ((Cone.mk X F.π).π.app i) :=
  Scheme.exists_isPullback_of_finitePresentation_of_isSeparated F.isLimit g

/-- The interface consumed by the descent of separatedness over a fixed base to a finite stage
(Stacks Project Tag 01ZH): the structure morphisms of a finite presentation approximation form
the natural transformation `t` required by
`AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit`. -/
example {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FinitePresentationApproximation) (i₀ : F.I)
    [IsSeparated ((Cone.mk X F.π).π.app i₀ ≫ F.p.app i₀)] :
    ∃ j : F.I, ∀ {i : F.I} (_ : i ⟶ j), IsSeparated (F.p.app i) :=
  Scheme.exists_isSeparated_app_of_isLimit F.isLimit F.p i₀

/-- **The separated finite presentation envelope of a morphism of finite type** (Stacks Project
Tag 01ZJ): a separated morphism `f : X ⟶ S` locally of finite type between quasi-compact
quasi-separated schemes factors as a closed immersion `i : X ⟶ X'` followed by a separated,
quasi-compact morphism `f' : X' ⟶ S` locally of finite presentation.

Take a finite presentation approximation of `f` (Stacks Project Tag 09ZQ) and descend the
separatedness of `f` to a stage of the system (Stacks Project Tag 01ZH); that stage is the
required envelope. (Blueprint: `prop:nagata-finite-type-closed-in-fp`.) -/
@[stacks 01ZJ]
theorem Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ S), IsClosedImmersion i ∧
      LocallyOfFinitePresentation f' ∧ QuasiCompact f' ∧ IsSeparated f' ∧ i ≫ f' = f := by
  obtain ⟨F⟩ := f.nonempty_finitePresentationApproximation
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := F.I)
  have : IsSeparated ((Cone.mk X F.π).π.app i₀ ≫ F.p.app i₀) := by
    change IsSeparated (F.π.app i₀ ≫ F.p.app i₀)
    rw [F.w i₀]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isSeparated_app_of_isLimit F.isLimit F.p i₀
  exact ⟨F.D.obj j, F.π.app j, F.p.app j, inferInstance, inferInstance, inferInstance,
    hj (𝟙 j), F.w j⟩

end FinitePresentationApproximation

end AlgebraicGeometry
