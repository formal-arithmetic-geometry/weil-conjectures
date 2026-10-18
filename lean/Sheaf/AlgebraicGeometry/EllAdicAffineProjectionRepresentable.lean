/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.AlgebraicGeometry.EllAdicAffineLineRepresentable
import Sheaf.AlgebraicGeometry.EllAdicClosedSupportRepresentable
import all Sheaf.AlgebraicGeometry.EllAdicCompactSupportComposition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Data.Fintype.Option

/-! # Bounded constructible affine projection duality -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Induction

private theorem leftAdjoint_of_counit {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    (h : ∀ K : D, ∃ P : C, ∃ ε : F.obj P ⟶ K,
      ∀ M : C, Function.Bijective (fun a : M ⟶ P ↦ F.map a ≫ ε)) :
    F.IsLeftAdjoint := by
  classical
  choose P ε hε using h
  let e (M : C) (K : D) : (F.obj M ⟶ K) ≃ (M ⟶ P K) :=
    (Equiv.ofBijective (fun a : M ⟶ P K ↦ F.map a ≫ ε K) (hε K M)).symm
  have he : ∀ (M N : C) (K : D) (a : M ⟶ N) (b : F.obj N ⟶ K),
      e M K (F.map a ≫ b) = a ≫ e N K b := by
    intro M N K a b
    apply (hε K M).1
    change (e M K).symm (e M K (F.map a ≫ b)) = F.map (a ≫ e N K b) ≫ ε K
    rw [Equiv.symm_apply_apply, F.map_comp, Category.assoc]
    congr 1
    exact ((e N K).symm_apply_apply b).symm
  exact ⟨_, ⟨Adjunction.adjunctionOfEquivRight e he⟩⟩
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) [IsFinitenessCoefficient ℓ Λ]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
include ℓ hΛ in
private theorem closed_leftAdjoint (i : X ⟶ Y) [IsClosedImmersion i.left] :
    (boundedConstructibleLowerStar Λ ℓ i).IsLeftAdjoint := by
  classical
  have : IsFinitenessCoefficient ℓ Λ := by cases hΛ <;> infer_instance
  apply leftAdjoint_of_counit
  intro K
  obtain ⟨hc, L, ε, hε⟩ := closed_support_representable Λ ℓ hΛ i K
  let _ := hc
  let β : boundedConstructibleLowerStar Λ ℓ i ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((i.left)_*⟦Λ⟧) :=
    boundedConstructibleLowerStarCompatibility Λ ℓ i ≪≫
      Functor.isoWhiskerLeft (boundedConstructible _).ι
        ((i.left)_*⟦Λ⟧).rightDerivedFunctorIsoMapDerivedCategory
  let ε' : (boundedConstructibleLowerStar Λ ℓ i).obj L ⟶ K :=
    ObjectProperty.homMk ((β.app L).hom ≫ ε)
  refine ⟨L, ε', fun M ↦ ?_⟩
  let e₁ : (M ⟶ L) ≃ (M.obj ⟶ L.obj) :=
    { toFun := fun a ↦ a.hom
      invFun := ObjectProperty.homMk
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e₂ := Equiv.ofBijective
    (fun a : M.obj ⟶ L.obj ↦ D((i.left)_*⟦Λ⟧).map a ≫ ε) (hε M)
  let e₃ : (D((i.left)_*⟦Λ⟧).obj M.obj ⟶ K.obj) ≃
      (((boundedConstructibleLowerStar Λ ℓ i).obj M).obj ⟶ K.obj) :=
    { toFun := fun b ↦ (β.app M).hom ≫ b
      invFun := fun b ↦ (β.app M).inv ≫ b
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
  let e₄ : ((boundedConstructibleLowerStar Λ ℓ i).obj M ⟶ K) ≃
      (((boundedConstructibleLowerStar Λ ℓ i).obj M).obj ⟶ K.obj) :=
    { toFun := fun a ↦ a.hom
      invFun := ObjectProperty.homMk
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e := e₁.trans (e₂.trans (e₃.trans e₄.symm))
  convert e.bijective using 1
  funext a
  apply ObjectProperty.hom_ext
  change ((boundedConstructibleLowerStar Λ ℓ i).map a).hom ≫
    ((β.app L).hom ≫ ε) = _
  change ((boundedConstructibleLowerStar Λ ℓ i).map a).hom ≫
    ((β.app L).hom ≫ ε) = (β.app M).hom ≫ (D((i.left)_*⟦Λ⟧).map a.hom ≫ ε)
  have hn := β.hom.naturality a
  change ((boundedConstructibleLowerStar Λ ℓ i).map a).hom ≫ (β.app L).hom =
    (β.app M).hom ≫ D((i.left)_*⟦Λ⟧).map a.hom at hn
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ ε) hn
include ℓ hΛ in
private theorem closed_shriek_leftAdjoint (i : X ⟶ Y) [IsClosedImmersion i.left] :
    (boundedConstructibleLowerShriek Λ ℓ i).IsLeftAdjoint := by
  have := closed_leftAdjoint Λ ℓ hΛ i
  obtain ⟨α⟩ := properLowerShriekIso Λ ℓ hΛ i
  exact Functor.isLeftAdjoint_of_iso α.symm

private noncomputable abbrev affineOver (n : Type u) (Y : Over (Spec (.of k))) :
    Over (Spec (.of k)) := Over.mk ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
private noncomputable abbrev affineProjection (n : Type u) (Y : Over (Spec (.of k))) :
    affineOver n Y ⟶ Y := Over.homMk (𝔸(n; Y.left) ↘ Y.left) rfl
private instance affine_finiteType (n : Type u) [Finite n] :
    LocallyOfFiniteType (affineOver n Y).hom :=
  inferInstanceAs (LocallyOfFiniteType ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
private instance affine_quasiCompact (n : Type u) [Finite n] :
    QuasiCompact (affineOver n Y).hom :=
  inferInstanceAs (QuasiCompact ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
private instance affine_separated (n : Type u) [Finite n] :
    IsSeparated (affineOver n Y).hom :=
  inferInstanceAs (IsSeparated ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))

include hΛ in
private theorem shriek_comp_leftAdjoint
    {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [(boundedConstructibleLowerShriek Λ ℓ f).IsLeftAdjoint]
    [(boundedConstructibleLowerShriek Λ ℓ g).IsLeftAdjoint] :
    (boundedConstructibleLowerShriek Λ ℓ (f ≫ g)).IsLeftAdjoint := by
  obtain ⟨α⟩ := ellAdic_compactSupport_comp Λ ℓ hΛ f g
  exact Functor.isLeftAdjoint_of_iso α.symm

include hΛ in
private theorem reindex_adjoint (n m : Type u) [Finite n] [Finite m] (e : n ≃ m)
    (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [(boundedConstructibleLowerShriek Λ ℓ (affineProjection n Y)).IsLeftAdjoint] :
    (boundedConstructibleLowerShriek Λ ℓ (affineProjection m Y)).IsLeftAdjoint := by
  let e' := AffineSpace.reindexIso Y.left e
  let i : affineOver m Y ⟶ affineOver n Y :=
    Over.homMk e'.hom (by
      dsimp only [e', AffineSpace.reindexIso, affineOver, Over.mk_hom]
      rw [← Category.assoc, AffineSpace.reindex_over])
  have : IsIso i.left := inferInstanceAs (IsIso e'.hom)
  have := closed_shriek_leftAdjoint Λ ℓ hΛ i
  have hi : i ≫ affineProjection n Y = affineProjection m Y := by
    ext
    exact AffineSpace.reindex_over e Y.left
  rw [← hi]
  exact shriek_comp_leftAdjoint Λ ℓ hΛ i (affineProjection n Y)
include hΛ in
private theorem sum_adjoint (n m : Type u) [Finite n] [Finite m]
    (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [(boundedConstructibleLowerShriek Λ ℓ (affineProjection n Y)).IsLeftAdjoint]
    [(boundedConstructibleLowerShriek Λ ℓ
      (affineProjection m (affineOver n Y))).IsLeftAdjoint] :
    (boundedConstructibleLowerShriek Λ ℓ (affineProjection (n ⊕ m) Y)).IsLeftAdjoint := by
  let e := AffineSpace.sumIso (n := n) (m := m) Y.left
  let i : affineOver (n ⊕ m) Y ⟶ affineOver m (affineOver n Y) :=
    Over.homMk e.hom (by
      change e.hom ≫ ((𝔸(m; 𝔸(n; Y.left)) ↘ 𝔸(n; Y.left)) ≫
        ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)) = (𝔸(n ⊕ m; Y.left) ↘ Y.left) ≫ Y.hom
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ Y.hom)
        (AffineSpace.sumIso_hom_over_over (n := n) (m := m) Y.left))
  have : IsIso i.left := inferInstanceAs (IsIso e.hom)
  have := closed_shriek_leftAdjoint Λ ℓ hΛ i
  let p := affineProjection m (affineOver n Y)
  let q := affineProjection n Y
  have := shriek_comp_leftAdjoint Λ ℓ hΛ p q
  have h := shriek_comp_leftAdjoint Λ ℓ hΛ i (p ≫ q)
  have hi : i ≫ (p ≫ q) = affineProjection (n ⊕ m) Y := by
    ext
    exact AffineSpace.sumIso_hom_over_over Y.left
  rwa [hi] at h

include hΛ in
private theorem affine_adjoint_from_line
    (hline : ∀ (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom],
      (boundedConstructibleLowerShriek Λ ℓ (affineProjection PUnit.{u + 1} T)).IsLeftAdjoint)
    (n : Type u) [Finite n] :
    ∀ (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom],
      (boundedConstructibleLowerShriek Λ ℓ (affineProjection n T)).IsLeftAdjoint := by
  classical
  let P (t : Type u) : Prop := ∀ [Finite t] (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom],
      (boundedConstructibleLowerShriek Λ ℓ (affineProjection t T)).IsLeftAdjoint
  have hn : P n := by
    refine @Finite.induction_empty_option P ?_ ?_ ?_ n inferInstance
    · intro α β e hα _ T _ _ _
      have : Finite α := Finite.of_equiv β e.symm
      have := hα T
      exact reindex_adjoint Λ ℓ hΛ α β e T
    · intro _ T _ _ _
      have : IsIso (affineProjection PEmpty T).left :=
        inferInstanceAs (IsIso (𝔸(PEmpty; T.left) ↘ T.left))
      exact closed_shriek_leftAdjoint Λ ℓ hΛ (affineProjection PEmpty T)
    · intro α _ hα _ T _ _ _
      have := hα T
      have := hline (affineOver α T)
      have := sum_adjoint Λ ℓ hΛ α PUnit.{u + 1} T
      exact reindex_adjoint Λ ℓ hΛ (α ⊕ PUnit.{u + 1}) (Option α)
        (Equiv.optionEquivSumPUnit α).symm T
  exact hn

private def fullHomEquiv {C : Type*} [Category C] (P : ObjectProperty C)
    (M N : P.FullSubcategory) : (M ⟶ N) ≃ (M.obj ⟶ N.obj) where
  toFun a := a.hom
  invFun := ObjectProperty.homMk
  left_inv _ := rfl
  right_inv _ := rfl

include hΛ in
private theorem projection_from_line
    (hline : ∀ (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom],
      (boundedConstructibleLowerShriek Λ ℓ (affineProjection PUnit.{u + 1} T)).IsLeftAdjoint)
    (n : Type u) [Finite n]
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ P : (boundedConstructible (condensedRingObj Λ (affineOver n Y).left)).FullSubcategory,
      ∃ e : ∀ M : (boundedConstructible (condensedRingObj Λ (affineOver n Y).left)).FullSubcategory,
        ((rightDerivedLowerShriekOfCompactification Λ
          (compactificationOverField (affineProjection n Y))).obj M.obj ⟶ K.obj) ≃
          (M.obj ⟶ P.obj),
        ∀ (M N : (boundedConstructible
            (condensedRingObj Λ (affineOver n Y).left)).FullSubcategory)
          (a : M.obj ⟶ N.obj)
          (b : (rightDerivedLowerShriekOfCompactification Λ
            (compactificationOverField (affineProjection n Y))).obj N.obj ⟶ K.obj),
          e M ((rightDerivedLowerShriekOfCompactification Λ
            (compactificationOverField (affineProjection n Y))).map a ≫ b) = a ≫ e N b := by
  classical
  let p := affineProjection n Y
  let F := boundedConstructibleLowerShriek Λ ℓ p
  have : F.IsLeftAdjoint := affine_adjoint_from_line Λ ℓ hΛ hline n Y
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  let β : F ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p) :=
    boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ (f := p)
      (compactificationOverField p)
  let ep (M : (boundedConstructible
      (condensedRingObj Λ (affineOver n Y).left)).FullSubcategory) :
      ((rightDerivedLowerShriekOfCompactification Λ
          (compactificationOverField p)).obj M.obj ⟶ K.obj) ≃ ((F.obj M).obj ⟶ K.obj) :=
    { toFun := fun b ↦ (β.app M).hom ≫ b
      invFun := fun b ↦ (β.app M).inv ≫ b
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
  let e (M : (boundedConstructible
      (condensedRingObj Λ (affineOver n Y).left)).FullSubcategory) :=
    (ep M).trans ((fullHomEquiv _ (F.obj M) K).symm.trans
      ((adj.homEquiv M K).trans (fullHomEquiv _ M (G.obj K))))
  refine ⟨G.obj K, e, fun M N a b ↦ ?_⟩
  change (adj.homEquiv M K (ObjectProperty.homMk ((β.app M).hom ≫
      ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p)).map a ≫
        b)))).hom = a ≫
      (adj.homEquiv N K (ObjectProperty.homMk ((β.app N).hom ≫ b))).hom
  have hn := β.hom.naturality (ObjectProperty.homMk a : M ⟶ N)
  change (F.map (ObjectProperty.homMk a)).hom ≫ (β.app N).hom =
    (β.app M).hom ≫
      (rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p)).map a at hn
  have harg : (ObjectProperty.homMk ((β.app M).hom ≫
      ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p)).map a ≫
        b)) : F.obj M ⟶ K) = F.map (ObjectProperty.homMk a) ≫
      ObjectProperty.homMk ((β.app N).hom ≫ b) := by
    ext
    change (β.app M).hom ≫
      ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p)).map a ≫ b) =
      (F.map (ObjectProperty.homMk a)).hom ≫ ((β.app N).hom ≫ b)
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ b) hn.symm
  rw [harg]
  exact congrArg (fun z ↦ z.hom) (adj.homEquiv_naturality_left
    (ObjectProperty.homMk a : M ⟶ N) (ObjectProperty.homMk ((β.app N).hom ≫ b)))

end Induction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ hΛ in
/-- Bounded constructible representatives for compact support along every finite-dimensional
relative affine-space projection.

Source: blueprint `sk-cor-affine-space-rational/`
`sk-cor-affine-space-rational-induction.proof.md`, coordinate induction; its integral
counterpart is `sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md` (2).
Proof: closed-support representability, exact closed pushforward and compactification
comparison imply that compact support along a closed immersion has a right adjoint on
bounded constructible categories. This covers all scheme isomorphisms and the empty-coordinate
projection. Reindex coordinates using the affine-space reindexing isomorphism. For a sum of
coordinate sets use the isomorphism with an iterated affine space, compose the two adjunctions,
and transport along compact-support composition. Finite empty/option induction, using the
affine-line adjunction on each successive base, proves existence of the adjunction in every
finite dimension. Its right adjoint applied to `K` is a bounded constructible representative.
The bounded/ambient compatibility isomorphism and the two full inclusions transport the
adjunction Hom equivalence to the displayed ambient Hom equivalence. The naturality square
of that compatibility and left naturality of the adjunction give the final identity.
The construction permits integral torsion and takes place in the ordinary derived category.
(blueprint: lem-sfb-adic-affine-projection-representable) -/
theorem affine_projection_representable (n : Type u) [Finite n]
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    let A : Over (Spec (.of k)) := Over.mk ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
    let p : A ⟶ Y := Over.homMk (𝔸(n; Y.left) ↘ Y.left) rfl
    letI : LocallyOfFiniteType A.hom :=
      inferInstanceAs (LocallyOfFiniteType ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
    letI : QuasiCompact A.hom :=
      inferInstanceAs (QuasiCompact ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
    letI : IsSeparated A.hom :=
      inferInstanceAs (IsSeparated ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
    ∃ P : (boundedConstructible (condensedRingObj Λ A.left)).FullSubcategory,
      ∃ e : ∀ M : (boundedConstructible (condensedRingObj Λ A.left)).FullSubcategory,
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p)).obj
          M.obj ⟶ K.obj) ≃ (M.obj ⟶ P.obj),
        ∀ (M N : (boundedConstructible (condensedRingObj Λ A.left)).FullSubcategory)
          (a : M.obj ⟶ N.obj)
          (b : (rightDerivedLowerShriekOfCompactification Λ
            (compactificationOverField p)).obj N.obj ⟶ K.obj),
          e M ((rightDerivedLowerShriekOfCompactification Λ
            (compactificationOverField p)).map a ≫ b) = a ≫ e N b := by
  classical
  have : IsFinitenessCoefficient ℓ Λ := by cases hΛ <;> infer_instance
  exact projection_from_line Λ ℓ hΛ
    (fun T _ _ _ ↦ affineLine_compactSupport_isLeftAdjoint Λ ℓ hΛ T) n K

end AlgebraicGeometry.ProEtale.CondensedRing
