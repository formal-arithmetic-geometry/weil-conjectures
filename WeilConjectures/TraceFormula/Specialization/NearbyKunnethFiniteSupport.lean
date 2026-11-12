/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedPoints
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteClosedPoints
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict
import WeilConjectures.TraceFormula.Specialization.SliceSupport
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitDimension

/-!

# Gabber's Künneth formula for nearby cycles: the finite-support step

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type, and let `C` be the cone of the Künneth map `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`
for bounded constructible `A`, `B`. This file proves that `C` is supported on finitely many closed
points of the special fibre `X_s × Y_s`
(`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible`), given
that its source and target are bounded constructible, that the total spaces locally embed into
`𝔸ᵐ_S`, `𝔸^{m'}_S`, and that the generic-slicing step holds in chart dimension `m + m' - 1`:
by the generic-slicing step (`NearbyCyclesModel.SliceKunnethFormula`, blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support"), `C` vanishes on the special fibre
`(𝒵 ×_{𝔸¹_S} Spec K⟦t⟧)_s` of the generic slice of every chart coordinate.

## Proof

Around a point of `X_s × Y_s`, choose charts `V ⟶ 𝔸(ι_V; S)`, `W ⟶ 𝔸(ι_W; S)` (immersions over
`S` of opens of the total spaces of `M`, `N`). Their coordinates, pulled
back to `V ×_S W`, are coordinates of the restriction of the product to `V ×_S W`; on the special
fibre they detect closed points (`AlgebraicGeometry.AffineSpace`
`.isClosed_singleton_of_forall_isClosed_singleton_reindex` and
`AlgebraicGeometry.Scheme.Pullback.isClosed_singleton_iff`). By the generic-slicing step, the cone
of the restricted Künneth map vanishes over the generic point of each coordinate line, so `C` is
supported on finitely many closed points
(`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- Derived pullbacks repeatedly request these same graded tensor properties. Prove them
-- once for module objects, instead of rebuilding their colimit instances at each use.
/-- Graded tensor products of module objects have the fourfold tensor comparison. -/
lemma finiteSupportTensorFour (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (W X Y Z : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt W X Y Z := by
  infer_instance

/-- Graded tensor products of module objects preserve the left associativity colimits. -/
lemma finiteSupportTensorLeft (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X Y Z : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := by
  infer_instance

/-- Graded tensor products of module objects preserve the right associativity colimits. -/
lemma finiteSupportTensorRight (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X Y Z : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := by
  infer_instance

attribute [local instance] finiteSupportTensorFour finiteSupportTensorLeft finiteSupportTensorRight

/-- A property of the generic coordinate fibres can be transported along an implication. -/
private lemma exists_generic_coordinates_mono {k : Type u} [Field k] {Y : Scheme.{u}}
    {Q Q' : ∀ (T : Scheme.{u}), (T ⟶ Y) → Prop} (h : ∀ T r, Q T r → Q' T r)
    (H : ∃ (ι : Type u) (_ : Finite ι) (b : ι → (Y ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ i, LocallyOfFiniteType (b i)) ∧
      (∀ y : Y, (∀ i, IsClosed {b i y}) → IsClosed {y}) ∧
      ∀ i, ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
        (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧ Q _ (pullback.fst (b i) ξ)) :
    ∃ (ι : Type u) (_ : Finite ι) (b : ι → (Y ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ i, LocallyOfFiniteType (b i)) ∧
      (∀ y : Y, (∀ i, IsClosed {b i y}) → IsClosed {y}) ∧
      ∀ i, ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
        (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧ Q' _ (pullback.fst (b i) ξ) := by
  obtain ⟨ι, hι, b, hb, hcl, hgen⟩ := H
  refine ⟨ι, hι, b, hb, hcl, fun i ↦ ?_⟩
  obtain ⟨K, hK, ξ, t, ht, hi⟩ := hgen i
  exact ⟨K, hK, ξ, t, ht, h _ _ hi⟩

/-- A morphism between bounded constructible complexes is invertible away from finitely many
closed points if it is invertible over the generic points of local coordinate lines. -/
private theorem exists_finset_isIso_of_forall_exists_coordinates
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))} (f : A ⟶ B)
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) A)
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) B)
    (H : ∀ y : Y.left, ∃ (U : Y.left.Opens) (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ i, LocallyOfFiniteType (b i)) ∧ (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
        (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧
        IsIso (L((pullback.fst (b i) ξ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f))) :
    ∃ (S : Finset Y.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f) := by
  have := isNoetherian_left Y
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hC := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    Y.left)).ext_of_isTriangulatedClosed₃ _ hT hA hB
  obtain ⟨S, hS, hz⟩ := exists_finset_isZero_of_forall_exists_coordinates Y hC fun y ↦ by
    obtain ⟨U, hy, ι, hι, b, hb, hcl, hgen⟩ := H y
    refine ⟨U, hy, ι, hι, b, hb, hcl, fun i ↦ ?_⟩
    obtain ⟨K, hK, ξ, t, ht, hf⟩ := hgen i
    refine ⟨K, hK, ξ, t, ht, ?_⟩
    have hT₁ := L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT
    have hT₂ := L((pullback.fst (b i) ξ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished
      _ hT₁
    exact Triangle.isZero₃_of_isIso₁ _ hT₂ hf
  exact ⟨S, hS, (Triangle.isZero₃_iff_isIso₁ _
    (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished
      _ hT)).1 hz⟩

namespace NearbyCyclesModel

/-! ### Special coordinates -/

section SpecialCoordinate

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The special fibre `c_s : 𝒳_s ⟶ 𝔸ⁿ_{k'}` of a map `c : 𝒳 ⟶ 𝔸ⁿ_S` over the trait is its base
change along the closed point. -/
lemma IsTraitModelOver.isPullback_specialCoordinate (hM : M.IsTraitModelOver q g) {n : Type u}
    (c : M.total ⟶ 𝔸(n; trait k')) (hc : c ≫ 𝔸(n; trait k') ↘ trait k' = q) :
    IsPullback M.i (specialCoordinate hM c hc) c (AffineSpace.map n (traitClosedPoint k')) := by
  refine IsPullback.of_bot ?_ (specialCoordinate_map hM c hc).symm
    (AffineSpace.isPullback_map (n := n) (traitClosedPoint k'))
  rw [specialCoordinate_over, hc]
  exact hM.isPullback_i

/-- The special fibre of `c ≫ ρ` for a reindexing `ρ : 𝔸ⁿ_S ⟶ 𝔸ᵐ_S` is `c_s ≫ ρ`. -/
lemma specialCoordinate_comp_reindex (hM : M.IsTraitModelOver q g) {n m : Type u}
    (c : M.total ⟶ 𝔸(n; trait k')) (hc : c ≫ 𝔸(n; trait k') ↘ trait k' = q) (j : m → n) :
    specialCoordinate hM (c ≫ AffineSpace.reindex j (trait k'))
        (by rw [Category.assoc, AffineSpace.reindex_over, hc]) =
      specialCoordinate hM c hc ≫ AffineSpace.reindex j (Spec (.of k')) := by
  refine (AffineSpace.isPullback_map (n := m) (traitClosedPoint k')).hom_ext ?_ ?_
  · rw [specialCoordinate_map, Category.assoc, ← AffineSpace.map_reindex,
      specialCoordinate_map_assoc]
  · rw [specialCoordinate_over, Category.assoc, AffineSpace.reindex_over, specialCoordinate_over]

/-- The special fibre of `φ ≫ c` for a morphism of models `φ : P ⟶ M` over the trait is
`f' ≫ c_s`, where `f'` is the map of special fibres of `φ`. -/
lemma specialCoordinate_comp_hom (hM : M.IsTraitModelOver q g) {Z : Scheme.{u}}
    {Z' : Over (Spec (.of k'))} {P : NearbyCyclesModel Z Z'.left} {f : Z ⟶ X}
    {f' : Z'.left ⟶ X'.left} (φ : P.Hom M f f') {qP : P.total ⟶ trait k'}
    {gP : P.generic ⟶ Spec (.of (traitGenericField k'))} (hP : P.IsTraitModelOver qP gP)
    (hqP : qP = φ.total ≫ q) {n : Type u} (c : M.total ⟶ 𝔸(n; trait k'))
    (hc : c ≫ 𝔸(n; trait k') ↘ trait k' = q) :
    specialCoordinate hP (φ.total ≫ c) (by rw [Category.assoc, hc, hqP]) =
      f' ≫ specialCoordinate hM c hc := by
  subst hqP
  refine (AffineSpace.isPullback_map (n := n) (traitClosedPoint k')).hom_ext ?_ ?_
  · rw [specialCoordinate_map, Category.assoc, specialCoordinate_map, reassoc_of% φ.comm_i]
  · rw [specialCoordinate_over, Category.assoc, specialCoordinate_over]
    exact (comp_eq_of_mono hM.isPullback_i hP.isPullback_i φ.comm_i).symm

/-- **The coordinates of an immersion detect closed points of the special fibre**: if
`c : 𝒳 ⟶ 𝔸ⁿ_S` is an immersion over the trait and all coordinates of the image of `x ∈ 𝒳_s`
under the special fibre `c_s` are closed points of `𝔸¹_{k'}`, then `x` is a closed point. -/
lemma isClosed_singleton_of_isImmersion (hM : M.IsTraitModelOver q g) {n : Type u}
    (c : M.total ⟶ 𝔸(n; trait k')) (hc : c ≫ 𝔸(n; trait k') ↘ trait k' = q)
    [IsImmersion c] (x : X'.left)
    (hx : ∀ a : n, IsClosed {(specialCoordinate hM c hc ≫
      AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ a) (Spec (.of k'))) x}) :
    IsClosed {x} := by
  have : IsImmersion (specialCoordinate hM c hc) :=
    MorphismProperty.of_isPullback (P := @IsImmersion)
      (hM.isPullback_specialCoordinate c hc) inferInstance
  have : LocallyQuasiFinite (specialCoordinate hM c hc) := inferInstance
  refine (specialCoordinate hM c hc).isClosed_singleton_of_isClosed_singleton ?_
  exact AffineSpace.isClosed_singleton_of_forall_isClosed_singleton_reindex
    (⟨0⟩ : ULift.{u} (Fin 1)) _ fun a ↦ by
    simpa using hx a

/-- Closed special coordinates of a pulled-back chart give a closed image point. -/
private lemma isClosed_singleton_image_of_closed_specialCoordinates
    (hM : M.IsTraitModelOver q g) {Z : Scheme.{u}} {Z' : Over (Spec (.of k'))}
    {P : NearbyCyclesModel Z Z'.left} {f : Z ⟶ X} {f' : Z'.left ⟶ X'.left}
    (φ : P.Hom M f f') {qP : P.total ⟶ trait k'}
    {gP : P.generic ⟶ Spec (.of (traitGenericField k'))} (hP : P.IsTraitModelOver qP gP)
    (hqP : qP = φ.total ≫ q) {ι : Type u} (c : M.total ⟶ 𝔸(ι; trait k')) [IsImmersion c]
    (hc : c ≫ 𝔸(ι; trait k') ↘ trait k' = q) (z : Z'.left)
    (hcoord : ∀ a : ι, (φ.total ≫ c ≫ AffineSpace.reindex
      (fun _ : ULift.{u} (Fin 1) ↦ a) (trait k')) ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qP)
    (hz : ∀ a, IsClosed {(specialCoordinate hP
      (φ.total ≫ c ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (hcoord a)) z}) :
    IsClosed {f' z} := by
  refine isClosed_singleton_of_isImmersion hM c hc _ fun a ↦ ?_
  have h := hz a
  rwa [show specialCoordinate hP
      (φ.total ≫ c ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (hcoord a) =
      f' ≫ specialCoordinate hM c hc ≫ AffineSpace.reindex (fun _ ↦ a) (Spec (.of k')) by
    rw [← specialCoordinate_comp_reindex hM c hc]
    exact specialCoordinate_comp_hom hM φ hP hqP _ _, Scheme.Hom.comp_apply] at h

end SpecialCoordinate

/-! ### Closed points of the special fibre of a product -/

section Product

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- A point of the special fibre `X_s ×_{k'} Y_s` of a product over the trait whose images in
`X_s` and `Y_s` are closed is closed. -/
lemma isClosed_singleton_special (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) (z : Z'.left)
    (h₁ : IsClosed {f₁' z}) (h₂ : IsClosed {f₂' z}) : IsClosed {z} := by
  have hsq := isPullback_special hM hN hpb hP
  have : LocallyOfFiniteType X'.hom := MorphismProperty.of_isPullback
    hM.isPullback_i hM.locallyOfFiniteType
  have : LocallyOfFiniteType Y'.hom := MorphismProperty.of_isPullback
    hN.isPullback_i hN.locallyOfFiniteType
  refine hsq.isoPullback.hom.isClosed_singleton_of_isClosed_singleton ?_
  refine (Scheme.Pullback.isClosed_singleton_iff X'.hom Y'.hom _).2 ⟨?_, ?_⟩
  · rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst]
  · rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_snd]

end Product

/-! ### The special fibre of a generic slice -/

section Slice

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The point `x : Spec K ⟶ 𝔸¹_{k'}` of the generic slice lies over `Spec K ⟶ Spec k'`. -/
@[reassoc (attr := simp)]
lemma traitSlicePoint_over (x : K) :
    traitSlicePoint (k' := k') x ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k')) ↘ Spec (.of k') =
      Spec.map (CommRingCat.ofHom (algebraMap k' K)) := by
  rw [traitSlicePoint, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp

/-- **The fibre of a special coordinate over the slice point factors through the special fibre of
the generic slice**: for a coordinate `b : 𝒳 ⟶ 𝔸¹_S` with special fibre `b_s`, the projection
`𝒳_s ×_{𝔸¹_{k'}} Spec K ⟶ 𝒳_s` factors through the special fibre `(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧)_s ⟶ 𝒳_s`
of the generic slice. -/
lemma exists_comp_sliceSpecialMap (x : K) (hM : M.IsTraitModelOver q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    ∃ l : pullback (specialCoordinate hM b hb) (traitSlicePoint x) ⟶ sliceSpecial x b,
      l ≫ sliceSpecialMap x hM hb = pullback.fst _ _ := by
  refine ⟨pullback.lift (pullback.lift (pullback.fst _ _ ≫ M.i)
    (pullback.snd _ _ ≫ traitClosedPoint K) ?_) (pullback.snd _ _) (pullback.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Category.assoc, traitClosedPoint_traitSlice,
      ← specialCoordinate_map hM b hb, pullback.condition_assoc]
  · refine hM.isPullback_i.hom_ext ?_ ?_
    · simp [sliceSpecialMap]
    · simp only [sliceSpecialMap, Category.assoc, IsPullback.lift_snd, pullback.lift_snd_assoc]
      rw [← specialCoordinate_over hM b hb, pullback.condition_assoc, traitSlicePoint_over]

/-- Invertibility on the special fibre of a slice implies invertibility on the fibre of its
special coordinate, by the factorization through the slice. -/
private lemma isIso_map_specialCoordinate_of_isIso_sliceSpecialMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (x : K) (hM : M.IsTraitModelOver q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
    {A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj Λ X'.left))} (f : A ⟶ B)
    (hf : IsIso (L((sliceSpecialMap x hM hb)^*⟦Λ⟧).map f)) :
    IsIso (L((pullback.fst (specialCoordinate hM b hb) (traitSlicePoint x))^*⟦Λ⟧).map f) := by
  obtain ⟨l, hl⟩ := exists_comp_sliceSpecialMap x hM hb
  rw [← hl]
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp Λ l _) f).2
    (Functor.map_isIso L((l)^*⟦Λ⟧) _)

end Slice

/-! ### Restrictions of the Künneth map, after a further pullback -/

section Restriction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

/-- If `a ≫ b ≫ c = d ≫ e ≫ g` with `b`, `c`, `d`, `e` invertible, then `F.map a` is invertible if
and only if `F.map g` is, for every functor `F`. -/
lemma isIso_map_iff_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X₁ X₂ X₃ Y₁ Y₂ : C} {a : W ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : W ⟶ Y₁} {e : Y₁ ⟶ Y₂}
    {g : Y₂ ⟶ X₃} (h : a ≫ b ≫ c = d ≫ e ≫ g) [IsIso b] [IsIso c] [IsIso d] [IsIso e] :
    IsIso (F.map a) ↔ IsIso (F.map g) :=
  isIso_iff_of_comp_eq (b := F.map b) (c := F.map c) (d := F.map d) (e := F.map e)
    (by rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp, h])

-- the Künneth maps of the two products are large terms
/-- **Restriction of the Künneth map, after a further pullback**: for a restriction of the product
along open immersions and any functor `F` on the derived category of the special fibre of the
restriction, `F(Lρ'^* Π_{A,B})` is invertible if and only if `F(Π_{Lρ_M^* A, Lρ_N^* B})` is. -/
theorem isIso_map_map_kunnethMap_iff_of_isKunnethRestriction {φ₁ : P.Hom M f₁ f₁'}
    {φ₂ : P.Hom N f₂ f₂'} {φ₁U : PU.Hom MU e₁ e₁'} {φ₂U : PU.Hom NU e₂ e₂'}
    {ρM : MU.Hom M r₁ r₁'} {ρN : NU.Hom N r₂ r₂'} {ρP : PU.Hom P r r'}
    (h : IsKunnethRestriction φ₁ φ₂ φ₁U φ₂U ρM ρN ρP) {D : Type*} [Category D]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology ZU') Ab.{u + 1})
      (condensedRingObj Λ ZU')) ⥤ D)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso (F.map (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) ↔
      IsIso (F.map (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) := by
  have := h.isOpenImmersion_M
  have := h.isOpenImmersion_N
  have := h.isOpenImmersion_P
  have := ρM.isIso_pullbackExchange_of_isOpenImmersion Λ h.isPullback_M
  have := ρN.isIso_pullbackExchange_of_isOpenImmersion Λ h.isPullback_N
  have := ρP.isIso_pullbackExchange_of_isOpenImmersion Λ h.isPullback_P
  exact isIso_map_iff_of_comp_eq F (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN
    ρP h.htot₁ h.hgen₁ h.htot₂ h.hgen₂ h.hb₁ h.hs₁ h.hb₂ h.hs₂ A B)

end Restriction

/-! ### The finite-support step -/

/-- Slicing an affine chart at one coordinate gives local embeddings with that coordinate
removed. Keep the choice of the immersion inside this geometric lemma. -/
private lemma locallyEmbedsInAffineSpace_slice_coordinate {T S S' : Scheme.{u}}
    {ι : Type u} [Finite ι] (c : T ⟶ 𝔸(ι; S)) [IsImmersion c] (a : ι)
    (σ : S' ⟶ 𝔸(ULift.{u} (Fin 1); S)) :
    (pullback.snd (c ≫ AffineSpace.reindex (fun _ ↦ a) S) σ).LocallyEmbedsInAffineSpace
      (Nat.card {j : ι // j ≠ a}) := by
  obtain ⟨c', hc'i, hc'⟩ := exists_isImmersion_pullback_reindex c a σ
  exact Scheme.Hom.LocallyEmbedsInAffineSpace.of_isImmersion c' hc'

section ChartCoordinates

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- Global affine charts give coordinates detecting closed points on the special fibre of a
product, with invertible Künneth maps on their generic fibres. -/
private theorem exists_coordinates_isIso_kunnethMap_of_charts
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula Λ k' (m + m' - 1))
    {ιV ιW : Type u} [Finite ιV] [Finite ιW]
    (cV : M.total ⟶ 𝔸(ιV; trait k')) [IsImmersion cV]
    (hcV : cV ≫ 𝔸(ιV; trait k') ↘ trait k' = qM) (hcardV : Nat.card ιV ≤ m)
    (cW : N.total ⟶ 𝔸(ιW; trait k')) [IsImmersion cW]
    (hcW : cW ≫ 𝔸(ιW; trait k') ↘ trait k' = qN) (hcardW : Nat.card ιW ≤ m')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    ∃ (ι : Type u) (_ : Finite ι) (b : ι → (Z'.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))),
      (∀ i, LocallyOfFiniteType (b i)) ∧
      (∀ v : Z'.left, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))
        (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧
        IsIso (L((pullback.fst (b i) ξ)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  let coord : ιV ⊕ ιW → (P.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')) :=
    Sum.elim (fun a ↦ φ₁.total ≫ cV ≫ AffineSpace.reindex (fun _ ↦ a) (trait k'))
      (fun a ↦ φ₂.total ≫ cW ≫ AffineSpace.reindex (fun _ ↦ a) (trait k'))
  have hcoord : ∀ i, coord i ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
      φ₁.total ≫ qM := by
    rintro (a | a)
    · simp [coord, hcV]
    · simp [coord, hcW, hpb.w]
  refine ⟨ιV ⊕ ιW, inferInstance, fun i ↦ specialCoordinate hP (coord i) (hcoord i),
    fun i ↦ ?_, fun v hv ↦ ?_, fun i ↦ ?_⟩
  · have : LocallyOfFiniteType Z'.hom :=
      MorphismProperty.of_isPullback hP.isPullback_i hP.locallyOfFiniteType
    have : LocallyOfFiniteType (specialCoordinate hP (coord i) (hcoord i) ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of k')) ↘ Spec (.of k')) := by
      rw [specialCoordinate_over]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (𝔸(ULift.{u} (Fin 1); Spec (.of k')) ↘ Spec (.of k'))
  · exact isClosed_singleton_special hM hN hpb hP v
      (isClosed_singleton_image_of_closed_specialCoordinates hM φ₁ hP rfl cV hcV v
        (fun a ↦ hcoord (.inl a)) (fun a ↦ hv (.inl a)))
      (isClosed_singleton_image_of_closed_specialCoordinates hN φ₂ hP hpb.w cW hcW v
        (fun a ↦ hcoord (.inr a)) (fun a ↦ hv (.inr a)))
  · refine ⟨traitSliceField k', inferInstance, traitSlicePoint (traitSliceCoord k'),
      ⟨⊥, Ideal.isPrime_bot⟩, isGenericPoint_traitSlicePoint_traitSliceCoord k' _, ?_⟩
    refine isIso_map_specialCoordinate_of_isIso_sliceSpecialMap Λ (traitSliceCoord k')
      hP (hcoord i) _ ?_
    rcases i with a | a
    · have hlt : Nat.card {j : ιV // j ≠ a} < Nat.card ιV :=
        Finite.card_subtype_lt (x := a) (by simp)
      exact (hslice (by omega)).isIso φ₁ φ₂ hM hN hpb hP hgen inferInstance
        inferInstance inferInstance
        (b := cV ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (by simp [hcV])
        (by omega) (locallyEmbedsInAffineSpace_slice_coordinate cV a _) hm' heM heN hA hB
    · have hlt : Nat.card {j : ιW // j ≠ a} < Nat.card ιW :=
        Finite.card_subtype_lt (x := a) (by simp)
      exact isIso_map_kunnethMap_baseChangeSpecialMap_snd hM hN hpb hP hgen
        (b := cW ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (by simp [hcW]) Λ
        (hslice (by omega)) (by omega) hm
        (locallyEmbedsInAffineSpace_slice_coordinate cW a _) heM heN hA hB

end ChartCoordinates

section FiniteSupport

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- The restriction of a product over the trait to `V ×_S W` is of finite type over the trait
along the restricted structure morphisms of the first factor. -/
lemma isTraitModelOver_restrictOpen_productOpen
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) (V : M.total.Opens)
    (W : N.total.Opens) [QuasiCompact (productOpen φ₁ φ₂ V W).ι] :
    (P.restrictOpen (productOpen φ₁ φ₂ V W)).IsTraitModelOver
      (X' := P.restrictSpecialFibre (productOpen φ₁ φ₂ V W))
      ((φ₁.restrictOpen (productOpen φ₁ φ₂ V W) V inf_le_left).total ≫ V.ι ≫ qM)
      ((φ₁.restrictOpen (productOpen φ₁ φ₂ V W) V inf_le_left).generic ≫
        (M.j ⁻¹ᵁ V).ι ≫ gM) := by
  convert hP.restrictOpen (productOpen φ₁ φ₂ V W) using 1 <;>
    simp [Scheme.Hom.resLE_comp_ι_assoc]

section LocalCoordinates

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- Local affine charts give coordinates on a neighbourhood of each special-fibre point,
with the original Künneth map invertible after pullback to their generic fibres. -/
private theorem exists_local_coordinates_isIso_kunnethMap
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula Λ k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B)
    (z : Z'.left) :
    ∃ (U : Z'.left.Opens) (_ : z ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))),
      (∀ i, LocallyOfFiniteType (b i)) ∧ (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))
        (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧
        IsIso (L((pullback.fst (b i) ξ)^*⟦Λ⟧).map
          (L((U.ι)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) := by
  have := hM.isTraitModel.isNoetherian_total
  have := hN.isTraitModel.isNoetherian_total
  have := hP.isTraitModel.isNoetherian_total
  have := hM.locallyOfFiniteType
  have := hN.locallyOfFiniteType
  match hm (φ₁.total (P.i z)), hm' (φ₂.total (P.i z)) with
  | ⟨V, hzV, ιV, hιV, cV, hcardV, hcVi, hcV⟩, ⟨W, hzW, ιW, hιW, cW, hcardW, hcWi, hcW⟩ =>
    have : QuasiCompact V.ι := inferInstance
    have : QuasiCompact W.ι := inferInstance
    have : QuasiCompact (productOpen φ₁ φ₂ V W).ι := inferInstance
    let U := productOpen φ₁ φ₂ V W
    let ψ₁ := φ₁.restrictOpen U V inf_le_left
    let ψ₂ := φ₂.restrictOpen U W inf_le_right
    have hMV := hM.restrictOpen V
    have hNW := hN.restrictOpen W
    have hpbU : IsPullback ψ₁.total ψ₂.total (V.ι ≫ qM) (W.ι ≫ qN) := isPullback_resLE_inf hpb V W
    have hPU := isTraitModelOver_restrictOpen_productOpen (φ₂ := φ₂) hP V W
    have heMV : (M.restrictOpen V).j ≫ V.ι ≫ eM = (M.restrictOpen V).ε := by simp [← heM]
    have heNW : (N.restrictOpen W).j ≫ W.ι ≫ eN = (N.restrictOpen W).ε := by simp [← heN]
    have hgenU : ψ₂.generic ≫ (N.j ⁻¹ᵁ W).ι ≫ gN = ψ₁.generic ≫ (M.j ⁻¹ᵁ V).ι ≫ gM := by
      simp [ψ₁, ψ₂, Scheme.Hom.resLE_comp_ι_assoc, hgen]
    have hA' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 X) _ hA
    have hB' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 Y) _ hB
    refine ⟨P.i ⁻¹ᵁ U, ⟨hzV, hzW⟩, ?_⟩
    refine exists_generic_coordinates_mono (Y := (P.restrictSpecialFibre U).left)
      (Q := fun T r ↦ IsIso (L((r)^*⟦Λ⟧).map
        (kunnethMap Λ ψ₁ ψ₂ (L((𝟙 X)^*⟦Λ⟧).obj A) (L((𝟙 Y)^*⟦Λ⟧).obj B))))
      (Q' := fun T r ↦ IsIso (L((r)^*⟦Λ⟧).map
        (L(((P.i ⁻¹ᵁ U).ι)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))))
      (fun T r hi ↦ ?_)
      (exists_coordinates_isIso_kunnethMap_of_charts Λ hMV hNW hpbU hPU hgenU
        (hm.restrict V) (hm'.restrict W) hslice cV hcV hcardV cW hcW hcardW heMV heNW hA' hB')
    exact (isIso_map_map_kunnethMap_iff_of_isKunnethRestriction Λ
      (isKunnethRestriction_restrictOpen φ₁ φ₂ V W) L((r)^*⟦Λ⟧) A B).2 hi

end LocalCoordinates

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **The finite-support step of Gabber's Künneth formula** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support"; Illusie, *Autour du théorème de monodromie
locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait of models `M`,
`N` of finite type and bounded constructible `A`, `B` such that the source and the target of the
Künneth map `Π_{A,B}` are bounded constructible, and whose total spaces locally embed into `𝔸ᵐ_S`,
`𝔸^{m'}_S`, if the generic-slicing step holds in chart dimension `m + m' - 1`
(`NearbyCyclesModel.SliceKunnethFormula`), then `Π_{A,B}` is an isomorphism away from finitely
many closed points of the special fibre `X_s × Y_s`.

Around every point, the coordinates of charts `V ⟶ 𝔸(ι_V; S)`, `W ⟶ 𝔸(ι_W; S)` of the total
spaces detect closed points of the special fibre of `V ×_S W`, and the cone of
`Π_{A,B}` vanishes over the generic point of each coordinate line
(`NearbyCyclesModel.SliceKunnethFormula` and its mirror, for the
restriction of the product to `V ×_S W`); conclude by
`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`.
-/
theorem exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace Y]
    [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (hsrc : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
      (L((f₁')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((M.nearbyCycles (Profinite.padicAlgClRingObj
          ℓ)).obj A) ⊗
        L((f₂')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((N.nearbyCycles (Profinite.padicAlgClRingObj
            ℓ)).obj B)))
    (htgt : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left)
      ((P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj (L((f₁)^*⟦Profinite.padicAlgClRingObj
          ℓ⟧).obj A ⊗ L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B))) :
    ∃ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (kunnethMap
          (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  exact exists_finset_isIso_of_forall_exists_coordinates Z' _ hsrc htgt
    (exists_local_coordinates_isIso_kunnethMap (Profinite.padicAlgClRingObj ℓ)
      hM hN hpb hP hgen hm hm' hslice heM heN hA hB)

end FiniteSupport

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
