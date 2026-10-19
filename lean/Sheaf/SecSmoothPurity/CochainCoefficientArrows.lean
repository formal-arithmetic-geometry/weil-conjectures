/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainTensorCoherenceData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (blueprint: def-pur-cochain-coefficient-arrows).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace CategoryTheory.CochainPullback
set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

/-- Identity inverse image, transporting every operation by the identity.
Source: Stacks 03D2 (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def identityAlgebraicInverseImage (A : Sheaf J CommRingCat.{w}) :
    SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf J (Type w))) A A where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules A)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

/-- Functor laws for the existing sheafified scalar extension.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows).
Proof: on a pure tensor the maps are `s ⊗ x ↦ s ⊗ h(x)`.
Identity and composition hold on these tensors; sheafification is functorial. -/
theorem extensionFunctor_laws {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    (∀ M : Modules A, SheafOfModules.changeOfRingsHom a M (𝟙 M) = 𝟙 _) ∧
      (∀ (M N H : Modules A) (b : M ⟶ N) (c : N ⟶ H),
        SheafOfModules.changeOfRingsHom a M (b ≫ c) =
          SheafOfModules.changeOfRingsHom a M b ≫
            SheafOfModules.changeOfRingsHom a N c) := by
  constructor
  · intro M
    unfold SheafOfModules.changeOfRingsHom
    have h : (show SheafOfModules.changeOfRingsPresheaf a M ⟶
        SheafOfModules.changeOfRingsPresheaf a M from
      { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map
          ((show M ⟶ M from 𝟙 M).val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturality a M (𝟙 M) }) =
          𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars (a.hom.app U).hom).map_id _
    exact (congrArg (fun b ↦ (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).map b) h).trans
        (Functor.map_id _ _)
  · intro M N H b c
    unfold SheafOfModules.changeOfRingsHom
    rw [← Functor.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_comp _ _

/-- Actual scalar extension, with the scalar placed first by the existing API.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def extensionFunctor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    Modules A ⥤ Modules B where
  obj M := SheafOfModules.changeOfRings a M
  map b := SheafOfModules.changeOfRingsHom a _ b
  map_id := (extensionFunctor_laws a).1
  map_comp := (extensionFunctor_laws a).2 _ _ _

/-- Actual restriction of scalars; this keeps the underlying abelian sheaf.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable abbrev restrictionFunctor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)

/-- The sheafification-unit image of `s ⊗ x` in scalar extension.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def extensionTmul {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :
    ((extensionFunctor a).obj M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf a M)).app U)
        (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules in
private theorem tensorRestriction_tmul
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S) (M : Modules A)
    {X Y : Cᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap c M i) s m

open SheafOfModules in
private noncomputable def tensorToRestriction
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S)
    (f : changeOfRingsPresheaf c M ⟶ H.val) : M ⟶ (restrictionFunctor c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

open SheafOfModules in
private noncomputable def restrictionToTensor
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S)
    (g : M ⟶ (restrictionFunctor c).obj H) : changeOfRingsPresheaf c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Cᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

open SheafOfModules in
private noncomputable def tensorPresheafHomEquiv
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S) :
    (changeOfRingsPresheaf c M ⟶ H.val) ≃ (M ⟶ (restrictionFunctor c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

open SheafOfModules in
private noncomputable def tensorHomEquiv
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A) (H : Modules S) :
    ((extensionFunctor c).obj M ⟶ H) ≃ (M ⟶ (restrictionFunctor c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

open SheafOfModules in
private theorem tensorHomEquiv_naturality_left
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    {M N : Modules A} (a : M ⟶ N)
    (H : Modules S) (f : (extensionFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((extensionFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).map
          ((show SheafOfModules.changeOfRingsPresheaf c M ⟶
          SheafOfModules.changeOfRingsPresheaf c N from
        { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (a.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality c M a })) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv
    (changeOfRingsPresheaf c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

open SheafOfModules in
private theorem tensorHomEquiv_naturality_right
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S)
    (M : Modules A)
    {H H' : Modules S}
    (f : (extensionFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restrictionFunctor c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

open SheafOfModules in
private noncomputable def tensorAdjunction
    {A S : Sheaf J CommRingCat.{w}} (c : A ⟶ S) : extensionFunctor c ⊣ restrictionFunctor c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }


/-- The scalar-extension adjunction normalized by `x ↦ 1 ⊗ x`.
Source: Stacks 03CY and 03D7
(blueprint: def-pur-cochain-coefficient-arrows).
Proof: compose the sectionwise balanced tensor hom correspondence with the
module sheafification adjunction. The resulting unit has the displayed formula.
The unit determines the counit, so an adjunction with this formula is unique. -/
theorem extensionAdjunction_existsUnique {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    ∃! adj : extensionFunctor a ⊣ restrictionFunctor a,
      ∀ (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x = extensionTmul a M U 1 x := by
  have hunit : ∀ (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U),
      ((tensorAdjunction a).unit.app M).val.app U x = extensionTmul a M U 1 x := by
    intro M U x
    rw [← Adjunction.homEquiv_id, tensorAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  refine ⟨tensorAdjunction a, hunit, ?_⟩
  intro adj hadj
  apply Adjunction.ext
  ext M U x
  exact (hadj M U x).trans (hunit M U x).symm

/-- The unique normalized scalar-extension adjunction.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def extensionAdjunction {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  Classical.choose (extensionAdjunction_existsUnique a)

/-- Scalar extension is additive because it is a left adjoint between abelian categories.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable instance extensionFunctorAdditive {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) : (extensionFunctor a).Additive :=
  (extensionAdjunction a).left_adjoint_additive

/-- The object/map presentation of scalar extension with identity inverse image.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows).
Proof: expand the functor map; the two transport maps are identities. -/
theorem extensionFunctor_mapPresentation {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} (b : M ⟶ N) :
    (extensionFunctor a).map b = eqToHom (rfl :
      (extensionFunctor a).obj M = SheafOfModules.changeOfRings a M) ≫
        SheafOfModules.changeOfRingsHom a M b ≫ eqToHom rfl := by
  simp [extensionFunctor]

/-- Scalar extension as the actual ringed identity-topos pullback.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def extensionPullback {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    RingedPullback A B where
  uInv := 𝟭 _
  uPush := 𝟭 _
  adj := Adjunction.id
  finiteLimits := inferInstance
  RI := A
  I := identityAlgebraicInverseImage A
  coefficient := a
  L := extensionFunctor a
  hobj _ := rfl
  hmap := extensionFunctor_mapPresentation a
  V := restrictionFunctor a
  moduleAdj := extensionAdjunction a

/-- The normalized comparison for scalar extension, uniquely fixed by pure tensors.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def extensionComparison {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    Comparison (extensionPullback a) :=
  Classical.choice
    (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
    A B A (𝟭 _) (identityAlgebraicInverseImage A) a (extensionFunctor a)
    (fun _ ↦ rfl) (𝟭 _) Adjunction.id (extensionFunctor_mapPresentation a)).1

/-- Termwise scalar extension on unbounded cochain complexes.
Source: Stacks 03CY and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable abbrev extend {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  pull (extensionPullback a)

/-- The canonical scalar-association map epsilon, with its actual tensor source and target.
Source: Stacks 03EL and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def epsilon {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex A) : (extend a).obj (P ⊗ Q) ≅
      (extend a).obj P ⊗ (extend a).obj Q :=
  comparison (extensionPullback a) (extensionComparison a) P Q

/-- Insertion of the scalar unit, as a morphism of underlying sheaves.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def insertion {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) (M : Modules A) :
    (underlying A).obj M ⟶ (underlying B).obj ((extensionFunctor a).obj M) :=
  (underlying A).map ((extensionAdjunction a).unit.app M)

/-- The compatible coefficient square over the same geometric inverse image.
In particular the equality of the two coefficient maps is part of the input.
The module functor is required to be the actual scalar-extension presentation.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
structure CoefficientSquare (f : RingedPullback R S) where
  R' : Sheaf J CommRingCat.{w}
  S' : Sheaf K CommRingCat.{w}
  sourceMap : R ⟶ R'
  targetMap : S ⟶ S'
  RI' : Sheaf K CommRingCat.{w}
  I' : SheafOfModules.AlgebraicInverseImage f.uInv R' RI'
  coefficient' : RI' ⟶ S'
  inverseImageMap : f.RI ⟶ RI'
  inverseImageMap_graph :
    f.uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map sourceMap) ≫
        I'.ringUnderlying.hom =
      f.I.ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map inverseImageMap
  square : inverseImageMap ≫ coefficient' = f.coefficient ≫ targetMap
  L' : Modules R' ⥤ Modules S'
  hobj' : ∀ M, L'.obj M = SheafOfModules.changeOfRings coefficient' (I'.modules.obj M)
  hmap' : ∀ {M N} (b : M ⟶ N), L'.map b = eqToHom (hobj' M) ≫
    SheafOfModules.changeOfRingsHom coefficient' (I'.modules.obj M) (I'.modules.map b) ≫
      eqToHom (hobj' N).symm
  V' : Modules S' ⥤ Modules R'
  moduleAdj' : L' ⊣ V'
  [additive' : L'.Additive]

attribute [instance] CoefficientSquare.additive'

/-- Change coefficients while keeping the original inverse-image adjunction.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def changed (f : RingedPullback R S) (d : CoefficientSquare f) :
    RingedPullback d.R' d.S' where
  uInv := f.uInv
  uPush := f.uPush
  adj := f.adj
  finiteLimits := f.finiteLimits
  RI := d.RI'
  I := d.I'
  coefficient := d.coefficient'
  L := d.L'
  hobj := d.hobj'
  hmap := d.hmap'
  V := d.V'
  moduleAdj := d.moduleAdj'

/-- A generalized inverse-image generator, followed by scalar-unit insertion.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def generator (f : RingedPullback R S) (k : Comparison f)
    {M : Modules R} {Z : Sheaf J (Type w)} (x : Z ⟶ (underlying R).obj M) :
    f.uInv.obj Z ⟶ (underlying S).obj (f.L.obj M) :=
  f.uInv.map x ≫ f.I.moduleUnderlying.inv.app M ≫ k.q M

/-- Scalar association is normalized on every generalized inverse-image generator.
Together with S'-linearity and balancing this specifies exactly
`s' ⊗ (x ⊗ r) ↦ (1 ⊗ x) ⊗ s' phi'(r)`.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
def IsScalarAssociation (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (b : extensionFunctor d.sourceMap ⋙ (changed f d).L ≅
      f.L ⋙ extensionFunctor d.targetMap) : Prop :=
  ∀ (M : Modules R) (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying R).obj M),
    generator (changed f d) k' (x ≫ insertion d.sourceMap M) ≫
        (underlying d.S').map (b.hom.app M) =
      generator f k x ≫ insertion d.targetMap (f.L.obj M)

/-- The compatible coefficient square gives a unique normalized scalar association.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows).
Proof: on generalized pure tensors use the coefficient square to move the R'
scalar across the tensor relation. Multiplication of S' scalars gives the forward
map; insertion of the two units gives its inverse. The bilinear universal property,
then sheafification, extend the maps. The two composites are identities on pure
tensors. Those generators also give naturality and uniqueness. -/
theorem scalarAssociation_existsUnique (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :
    ∃! b : extensionFunctor d.sourceMap ⋙ (changed f d).L ≅
      f.L ⋙ extensionFunctor d.targetMap, IsScalarAssociation f k d k' b := sorry

/-- The unique canonical module scalar-association isomorphism.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def scalarAssociation (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :=
  Classical.choose (scalarAssociation_existsUnique f k d k')

/-- Kappa is the termwise lift of the normalized scalar-association map.
Source: Stacks 03EL and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def kappa (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) (P : Complex R) :
    (pull (changed f d)).obj ((extend d.sourceMap).obj P) ≅
      (extend d.targetMap).obj ((pull f).obj P) :=
  (NatIso.mapHomologicalComplex (scalarAssociation f k d k') (.up ℤ)).app P

/-- Tau is the extension unit followed by the inverse scalar association, with
restriction of scalars making the semilinear map an S-linear map.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def transitionModule (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :
    f.L ⟶ extensionFunctor d.sourceMap ⋙ (changed f d).L ⋙
      restrictionFunctor d.targetMap :=
  Functor.whiskerLeft f.L (extensionAdjunction d.targetMap).unit ≫
    Functor.whiskerRight (scalarAssociation f k d k').inv (restrictionFunctor d.targetMap)

/-- The restriction of scalars on complexes, applied termwise.
Source: Stacks 03CY (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable abbrev restrictComplex {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :=
  (restrictionFunctor a).mapHomologicalComplex (.up ℤ)

/-- The canonical transition chain map, rather than an inverse to coefficient change.
Source: Stacks 03EL (blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def tau (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) (P : Complex R) :
    (pull f).obj P ⟶ (restrictComplex d.targetMap).obj
      ((pull (changed f d)).obj ((extend d.sourceMap).obj P)) :=
  (NatTrans.mapHomologicalComplex (transitionModule f k d k') (.up ℤ)).app P

/-- The canonical lax tensor map for restriction of scalars, obtained by adjunction.
Source: Stacks 03CY and 03EK
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def restrictionTensorModule {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M N : Modules B) :
    (restrictionFunctor a).obj M ⊗ (restrictionFunctor a).obj N ⟶
      (restrictionFunctor a).obj (M ⊗ N) :=
  (extensionAdjunction a).homEquiv _ _
    (((extensionComparison a).mu
      ((restrictionFunctor a).obj M) ((restrictionFunctor a).obj N)).hom ≫
        ((extensionAdjunction a).counit.app M ⊗ₘ
          (extensionAdjunction a).counit.app N))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionTensorModule_naturality
    {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M M' N N' : Modules B} (f : M ⟶ M') (g : N ⟶ N') :
    ((restrictionFunctor a).map f ⊗ₘ (restrictionFunctor a).map g) ≫
        restrictionTensorModule a M' N' =
      restrictionTensorModule a M N ≫ (restrictionFunctor a).map (f ⊗ₘ g) := by
  unfold restrictionTensorModule
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  apply congrArg ((extensionAdjunction a).homEquiv _ _)
  have h := (extensionComparison a).naturality
    ((restrictionFunctor a).map f) ((restrictionFunctor a).map g)
  dsimp only [extensionPullback] at h
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have hf : (extensionFunctor a).map ((restrictionFunctor a).map f) ≫
      (extensionAdjunction a).counit.app M' =
        (extensionAdjunction a).counit.app M ≫ f :=
    (extensionAdjunction a).counit.naturality f
  have hg : (extensionFunctor a).map ((restrictionFunctor a).map g) ≫
      (extensionAdjunction a).counit.app N' =
        (extensionAdjunction a).counit.app N ≫ g :=
    (extensionAdjunction a).counit.naturality g
  rw [hf, hg]


universe uA vA uB vB

section

variable {A : Type uA} [Category.{vA} A] [Abelian A] [MonoidalCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj X ⊗ L.obj Y ⟶ L.obj (X ⊗ Y))


private noncomputable def laxTotalComponent (P Q : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).X n ⟶
        L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun a b h ↦
    e (P.X a) (Q.X b) ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem laxTotalComponent_comm
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      e X Y ≫ L.map (f ⊗ₘ g) = (L.map f ⊗ₘ L.map g) ≫ e X' Y')
    (P Q : CochainComplex A ℤ) (n m : ℤ) :
    laxTotalComponent L e P Q n ≫
        L.map ((CochainComplex.mapBifunctor P Q (curriedTensor A)).d n m) =
      (CochainComplex.mapBifunctor
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) (curriedTensor B)).d n m ≫
          laxTotalComponent L e P Q m := by
  by_cases hnm : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at hnm
    subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    change a + b = n at hab
    simp only [laxTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    simp only [L.map_add, Preadditive.comp_add, Category.assoc]
    rw [← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₁,
      ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq P Q _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega)]
    simp only [
      ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
      one_smul, Functor.map_units_smul, Functor.map_comp,
      Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      Functor.mapHomologicalComplex_obj_d, ← tensorHom_id, ← id_tensorHom]
    dsimp only [Functor.mapHomologicalComplex, curriedTensor_obj_obj]
    apply congrArg₂ (· + ·)
    · simpa only [L.map_id, Category.assoc] using
        congrArg (fun f ↦ f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            (a + 1) b (n + 1) (by omega))) (he (P.d a (a + 1)) (𝟙 (Q.X b)))
    · simpa only [L.map_id, Category.assoc, Linear.units_smul_comp,
        Linear.comp_units_smul] using
        congrArg (fun f ↦ a.negOnePow • (f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            a (b + 1) (n + 1) (by omega)))) (he (𝟙 (P.X a)) (Q.d b (b + 1)))
  · rw [HomologicalComplex.shape _ n m hnm, HomologicalComplex.shape _ n m hnm,
      L.map_zero, comp_zero, zero_comp]

end

/-- Sum of the canonical restriction tensor maps over a total degree.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def restrictionTensorComponent {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) (n : ℤ) :
    ((restrictComplex a).obj P ⊗ (restrictComplex a).obj Q).X n ⟶
      (restrictionFunctor a).obj ((P ⊗ Q).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
    restrictionTensorModule a (P.X p) (Q.X q) ≫
      (restrictionFunctor a).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules B)) p q n hpq))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction's tensor comparison commutes with the signed total differential.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-arrows).
Proof: on each summand, naturality of the adjunction's unit and counit and of
scalar extension's tensor comparison commutes with each differential. Restriction
is additive, so it preserves the factor (-1)^p. Sum the two equations. -/
theorem restrictionTensorComponent_comm {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) (n m : ℤ) :
    restrictionTensorComponent a P Q n ≫
        (restrictionFunctor a).map ((P ⊗ Q).d n m) =
      ((restrictComplex a).obj P ⊗ (restrictComplex a).obj Q).d n m ≫
        restrictionTensorComponent a P Q m := by
  exact laxTotalComponent_comm (restrictionFunctor a) (restrictionTensorModule a)
    (fun f g ↦ (restrictionTensorModule_naturality a f g).symm) P Q n m

/-- The usual restriction-of-scalars tensor map on total complexes.
It sends a homogeneous pure tensor `x ⊗ y` to `x ⊗ y` and is not asserted invertible.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
noncomputable def restrictionTensor {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (P Q : Complex B) :
    (restrictComplex a).obj P ⊗ (restrictComplex a).obj Q ⟶
      (restrictComplex a).obj (P ⊗ Q) where
  f := restrictionTensorComponent a P Q
  comm' n m _ := restrictionTensorComponent_comm a P Q n m

/-- The two coefficient equations, with scalar restriction on the semilinear one.
The first is an equation of S'-linear chain maps; the second is an equation of
S-linear chain maps into the restriction of the same target. Specializing the
second equation to every pair m >= n of quotient coefficient maps is precisely
commutation of the comparisons with all quotient-tower transitions.
Source: Stacks 03EL and 07A4
(blueprint: def-pur-cochain-coefficient-arrows). -/
def IsCompatibleWithCoefficients (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) : Prop :=
  (∀ (P Q : Complex R),
    (pull (changed f d)).map (epsilon d.sourceMap P Q).hom ≫
        (comparison (changed f d) k'
          ((extend d.sourceMap).obj P) ((extend d.sourceMap).obj Q)).hom ≫
          ((kappa f k d k' P).hom ⊗ₘ (kappa f k d k' Q).hom) =
      (kappa f k d k' (P ⊗ Q)).hom ≫
        (extend d.targetMap).map (comparison f k P Q).hom ≫
          (epsilon d.targetMap ((pull f).obj P) ((pull f).obj Q)).hom) ∧
  (∀ (P Q : Complex R),
    (comparison f k P Q).hom ≫ (tau f k d k' P ⊗ₘ tau f k d k' Q) ≫
        restrictionTensor d.targetMap
          ((pull (changed f d)).obj ((extend d.sourceMap).obj P))
          ((pull (changed f d)).obj ((extend d.sourceMap).obj Q)) =
      tau f k d k' (P ⊗ Q) ≫ (restrictComplex d.targetMap).map
        ((pull (changed f d)).map (epsilon d.sourceMap P Q).hom ≫
          (comparison (changed f d) k'
            ((extend d.sourceMap).obj P) ((extend d.sourceMap).obj Q)).hom))


end CategoryTheory.CochainPullback
