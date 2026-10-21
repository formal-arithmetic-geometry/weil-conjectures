/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementData
import Sheaf.Paper.RingedRefinementMate

/-!
# Coefficient compatible refinement mate

(blueprint: lem-pur-ringed-refinement-formal-laws).
-/

@[expose] public noncomputable section
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Transposing the coefficient-compatible clopen map gives the displayed square.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, counit calculation
(blueprint: lem-pur-ringed-refinement-formal-laws).
Proof: apply the mate/counit calculation to h at the two coefficients, then use
its prescribed adjunct formula to identify the two refinement maps. -/
private theorem square_of_h {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (sc : ScalarComparisons o) {p : Spatial o}
    {e : OpenComparisons p} (r : Refinements e)
    {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B)
    (hc : ∀ M : category c X A,
      (sc.pull u a).hom.app ((o.shriek j₂ A).obj M) ≫
          (o.scalar Y a).T.map (e.h d A M) ≫ (sc.delta j₁ a).hom.app M =
        (o.operation u B).left.map ((sc.delta j₂ a).hom.app M) ≫
          e.h d B ((o.scalar X a).T.obj M)) :
    left sc r u j₁ j₂ h d a = right sc r u j₁ j₂ h d a := by
  ext M
  change (o.scalar Z a).T.map ((r.map u j₁ j₂ h d A).app M) ≫
      (sc.chi u a).app ((o.shriek j₁ A).obj M) ≫
        (o.operation u B).right.map ((sc.delta j₁ a).hom.app M) =
    (sc.delta j₂ a).hom.app M ≫
      (r.map u j₁ j₂ h d B).app ((o.scalar X a).T.obj M)
  rw [← r.adjunct u j₁ j₂ h d A M,
    ← r.adjunct u j₁ j₂ h d B ((o.scalar X a).T.obj M)]
  exact refinement_coefficient_mate (o.operation u A).derivedAdjunction
    (o.operation u B).derivedAdjunction (sc.pull u a).hom
    (e.h d A M) (e.h d B ((o.scalar X a).T.obj M))
    ((sc.delta j₁ a).hom.app M) ((sc.delta j₂ a).hom.app M) (hc M)


set_option backward.isDefEq.respectTransparency false in
/-- The coherence equations apart from the coefficient square and the two equations
which follow formally from it and functoriality.
Source: Steps 6--8 of the coefficient supplement
(blueprint: lem-pur-ringed-refinement-formal-laws). -/
structure ResidualLaws {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (sc : ScalarComparisons o) (ac : ScalarComposition o)
    {p : Spatial o} {e : OpenComparisons p} (r : Refinements e) : Prop where
  coefficient : ∀ {U V : Over T} (f : U ⟶ V) {A B C : Rings m T}
    (a : A ⟶ B) (b : B ⟶ C) (N : category c U A),
    (ac.derived V a b).hom.app ((o.operation f A).right.obj N) ≫
        (sc.chi f (a ≫ b)).app N =
      (o.scalar V b).T.map ((sc.chi f a).app N) ≫
        (sc.chi f b).app ((o.scalar U a).T.obj N) ≫
        (o.operation f C).right.map ((ac.derived U a b).hom.app N)
  open_coefficient : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C) (M : category c U A),
    (ac.derived V a b).hom.app ((o.shriek j A).obj M) ≫ (sc.delta j (a ≫ b)).hom.app M =
      (o.scalar V b).T.map ((sc.delta j a).hom.app M) ≫
        (sc.delta j b).hom.app ((o.scalar U a).T.obj M) ≫
        (o.shriek j C).map ((ac.derived U a b).hom.app M)
  coefficient_identity : ∀ {U V : Over T} (f : U ⟶ V) (A : Rings m T)
    (N : category c U A),
    (sc.chi f (𝟙 A)).app N ≫
        (o.operation f A).right.map ((ac.unit U A).hom.app N) =
      (ac.unit V A).hom.app ((o.operation f A).right.obj N)
  open_identity : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (A : Rings m T) (M : category c U A),
    (sc.delta j (𝟙 A)).hom.app M ≫ (o.shriek j A).map ((ac.unit U A).hom.app M) =
      (ac.unit V A).hom.app ((o.shriek j A).obj M)
  refinements : ∀ {X Y Z W : Over T} (u : Y ⟶ Z) (v : Z ⟶ W)
    (j₁ : X ⟶ Y) (j₂ : X ⟶ Z) (j₃ : X ⟶ W)
    [IsProper u.left] [IsProper v.left] [IsProper (u ≫ v).left]
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left] [IsOpenImmersion j₃.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] [QuasiCompact j₃.left]
    (h₁ : j₁ ≫ u = j₂) (h₂ : j₂ ≫ v = j₃) (h₃ : j₁ ≫ (u ≫ v) = j₃)
    (d₁ : Shape u j₁ j₂) (d₂ : Shape v j₂ j₃) (d₃ : Shape (u ≫ v) j₁ j₃)
    (R : Rings m T) (M : category c X R),
    (r.map (u ≫ v) j₁ j₃ h₃ d₃ R).app M =
      (r.map v j₂ j₃ h₂ d₂ R).app M ≫
        (o.operation v R).right.map ((r.map u j₁ j₂ h₁ d₁ R).app M) ≫
        (p.pushComp u v R).hom.app ((o.shriek j₁ R).obj M)
  refinement_identity : ∀ {X Y : Over T} (j : X ⟶ Y)
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    (h : j ≫ 𝟙 Y = j) (d : Shape (𝟙 Y) j j) (R : Rings m T)
    (M : category c X R),
    (r.map (𝟙 Y) j j h d R).app M =
      (o.operation (𝟙 Y) R).derivedAdjunction.homEquiv _ _
        ((p.pullId Y R).hom.app ((o.shriek j R).obj M))
  spatial_coefficient : ∀ {U V W : Over T} (f : U ⟶ V) (g : V ⟶ W)
    {A B : Rings m T} (a : A ⟶ B) (N : category c U A),
    (o.scalar W a).T.map ((p.pushComp f g A).hom.app N) ≫
        (sc.chi (f ≫ g) a).app N =
      (sc.chi g a).app ((o.operation f A).right.obj N) ≫
        (o.operation g B).right.map ((sc.chi f a).app N) ≫
        (p.pushComp f g B).hom.app ((o.scalar U a).T.obj N)


/-- Compatibility of the clopen map with scalar extension, before transposing it.
Source: Step 5 of the coefficient supplement
(blueprint: lem-pur-ringed-refinement-formal-laws). -/
def HCompatible {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (sc : ScalarComparisons o) {p : Spatial o}
    (e : OpenComparisons p) : Prop :=
  ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (_h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B) (M : category c X A),
    (sc.pull u a).hom.app ((o.shriek j₂ A).obj M) ≫
        (o.scalar Y a).T.map (e.h d A M) ≫ (sc.delta j₁ a).hom.app M =
      (o.operation u B).left.map ((sc.delta j₂ a).hom.app M) ≫
        e.h d B ((o.scalar X a).T.obj M)

/-- Complete the laws from the clopen calculation and the remaining coherence equations.
Source: Steps 5--8 of the coefficient supplement
(blueprint: lem-pur-ringed-refinement-formal-laws).
Proof: transpose h compatibility to obtain the square; naturality is naturality
of the displayed left transformation. For a commuting coefficient square, express
each successive mate as the direct mate using the coefficient cocycle, then use
transport along the equality of coefficient maps. The remaining equations are given. -/
theorem laws_of_clopen {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (sc : ScalarComparisons o) (ac : ScalarComposition o)
    {p : Spatial o} {e : OpenComparisons p} (r : Refinements e)
    (hc : HCompatible sc e) (hr : ResidualLaws sc ac r) : Laws sc ac r where
  square := by
    intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a
    exact square_of_h sc r u j₁ j₂ h d a (hc u j₁ j₂ h d a)
  natural := by
    intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a M N f
    exact (left sc r u j₁ j₂ h d a).naturality f
  coefficient := hr.coefficient
  open_coefficient := hr.open_coefficient
  coefficient_identity := hr.coefficient_identity
  coefficient_square := by
    intro U V f A B C D a b a' b' h N
    have hs {B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C) :
        successive sc ac f a b N = (sc.chi f (a ≫ b)).app N := by
      unfold successive
      rw [← hr.coefficient f a b N, Iso.inv_hom_id_app_assoc]
    rw [hs a b, hs a' b']
    simpa only [eqToHom_map] using
      eqToHom_naturality (fun q ↦ (sc.chi f q).app N) h
  open_identity := hr.open_identity
  refinements := hr.refinements
  refinement_identity := hr.refinement_identity
  spatial_coefficient := hr.spatial_coefficient

/-- Shift compatibility of the generating transformations, before composition.
Source: coefficient supplement Step 8
(blueprint: lem-pur-ringed-refinement-formal-laws). -/
structure BasicShifts {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {p : Spatial o} {e : OpenComparisons p}
    (r : Refinements e) where
  [scalar : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B), (o.scalar W a).T.CommShift ℤ]
  scalar_counit : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (o.scalar W a).ε ℤ
  inverse_scalar : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (sc.pull f a).hom ℤ
  delta : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B : Rings m T} (a : A ⟶ B), NatTrans.CommShift (sc.delta j a).hom ℤ
  chi : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
    NatTrans.CommShift (sc.chi f a) ℤ
  beta : ∀ {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X)
    (u : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion b.left] [IsOpenImmersion j.left]
    (sq : IsPullback b q u j) (R : Rings m T),
    NatTrans.CommShift (e.beta b q u j sq R).hom ℤ
  pi : ∀ {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
    (hs : IsClopen (Set.range s.left.base)) (R : Rings m T),
    NatTrans.CommShift (e.pi s hs R) ℤ
  refinement : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) (R : Rings m T), NatTrans.CommShift (r.map u j₁ j₂ h d R) ℤ

/-- Composition supplies both displayed coefficient-square shift compatibilities.
Source: coefficient supplement Step 8
(blueprint: lem-pur-ringed-refinement-formal-laws).
Proof: install the shifts of scalar extension and of the generators; compatibility
with shifts is preserved by left and right whiskering and vertical composition. -/
def shifts_of_generators {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (sc : ScalarComparisons o)
    {p : Spatial o} {e : OpenComparisons p} (r : Refinements e)
    (hs : BasicShifts sc r) : Shifts sc r where
  scalar := hs.scalar
  scalar_counit := hs.scalar_counit
  inverse_scalar := hs.inverse_scalar
  delta := hs.delta
  chi := hs.chi
  beta := hs.beta
  pi := hs.pi
  refinement := hs.refinement
  square_left := by
    intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a
    let (W : Over T) {A B : Rings m T} (a : A ⟶ B) :
        (o.scalar W a).T.CommShift ℤ := hs.scalar W a
    have : NatTrans.CommShift (r.map u j₁ j₂ h d A) ℤ :=
      hs.refinement u j₁ j₂ h d A
    have : NatTrans.CommShift (sc.chi u a) ℤ := hs.chi u a
    have : NatTrans.CommShift (sc.delta j₁ a).hom ℤ := hs.delta j₁ a
    have hh : NatTrans.CommShift
        (Functor.whiskerRight (r.map u j₁ j₂ h d A) (o.scalar Z a).T ≫
          (Functor.associator (o.shriek j₁ A) (o.operation u A).right
            (o.scalar Z a).T).hom ≫
          Functor.whiskerLeft (o.shriek j₁ A) (sc.chi u a) ≫
          (Functor.associator (o.shriek j₁ A) (o.scalar Y a).T
            (o.operation u B).right).inv ≫
          Functor.whiskerRight (sc.delta j₁ a).hom (o.operation u B).right ≫
          (Functor.associator (o.scalar X a).T (o.shriek j₁ B)
            (o.operation u B).right).hom) ℤ := inferInstance
    have he :
        Functor.whiskerRight (r.map u j₁ j₂ h d A) (o.scalar Z a).T ≫
          (Functor.associator (o.shriek j₁ A) (o.operation u A).right
            (o.scalar Z a).T).hom ≫
          Functor.whiskerLeft (o.shriek j₁ A) (sc.chi u a) ≫
          (Functor.associator (o.shriek j₁ A) (o.scalar Y a).T
            (o.operation u B).right).inv ≫
          Functor.whiskerRight (sc.delta j₁ a).hom (o.operation u B).right ≫
          (Functor.associator (o.scalar X a).T (o.shriek j₁ B)
            (o.operation u B).right).hom = left sc r u j₁ j₂ h d a := by
      ext M
      simp [left]
    rw [he] at hh
    exact hh
  square_right := by
    intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a
    let (W : Over T) {A B : Rings m T} (a : A ⟶ B) :
        (o.scalar W a).T.CommShift ℤ := hs.scalar W a
    have : NatTrans.CommShift (r.map u j₁ j₂ h d B) ℤ :=
      hs.refinement u j₁ j₂ h d B
    have : NatTrans.CommShift (sc.delta j₂ a).hom ℤ := hs.delta j₂ a
    unfold right
    infer_instance

end SheafOfModules.RingedRefinement
