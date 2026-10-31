/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom

/-! # Comparing specified and standing exceptional normalizations

Source: the normalized comparison-class adjunction, clauses (2)--(3).
(blueprint: lem-sf-specified-standing-normalized-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- Two source-natural Hom representations are related by the transpose of the
universal evaluation at the first representing object.
Source: uniqueness of a relative representing object
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: source naturality and injectivity of the first equivalence identify its
universal evaluation after the transpose of a with a. Apply source naturality of
the second equivalence to this equality. -/
theorem relative_transpose_transport
    {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
    (F : C ⥤ D) (K : D) (R S : C) (hR : P R)
    (e : ∀ M, P M → (F.obj M ⟶ K) ≃ (M ⟶ R))
    (d : ∀ M, P M → (F.obj M ⟶ K) ≃ (M ⟶ S))
    (he : ∀ M N (hM : P M) (hN : P N) (v : M ⟶ N) (a : F.obj N ⟶ K),
      e M hM (F.map v ≫ a) = v ≫ e N hN a)
    (hd : ∀ M N (hM : P M) (hN : P N) (v : M ⟶ N) (a : F.obj N ⟶ K),
      d M hM (F.map v ≫ a) = v ≫ d N hN a)
    (M : C) (hM : P M) (a : F.obj M ⟶ K) :
    e M hM a ≫ d R hR ((e R hR).symm (𝟙 R)) = d M hM a := by
  have h : F.map (e M hM a) ≫ (e R hR).symm (𝟙 R) = a := by
    apply (e M hM).injective
    rw [he M R hM hR, Equiv.apply_symm_apply, Category.comp_id]
  rw [← hd M R hM hR, h]

/-- Two natural relative Hom representations by objects in the source class have a
canonical comparison isomorphism.
Source: uniqueness of a representing object, applied within a full subcategory
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: transpose the inverse image of the identity in each direction. Source
naturality shows that postcomposition with either map identifies the two Hom
bijections. Apply this identity twice, at the representing objects, to prove the
two inverse laws. -/
def relativeRepresentingIso
    {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
    (F : C ⥤ D) (K : D) (R S : C) (hR : P R) (hS : P S)
    (e : ∀ M, P M → (F.obj M ⟶ K) ≃ (M ⟶ R))
    (d : ∀ M, P M → (F.obj M ⟶ K) ≃ (M ⟶ S))
    (he : ∀ M N (hM : P M) (hN : P N) (v : M ⟶ N) (a : F.obj N ⟶ K),
      e M hM (F.map v ≫ a) = v ≫ e N hN a)
    (hd : ∀ M N (hM : P M) (hN : P N) (v : M ⟶ N) (a : F.obj N ⟶ K),
      d M hM (F.map v ≫ a) = v ≫ d N hN a) : R ≅ S where
  hom := d R hR ((e R hR).symm (𝟙 R))
  inv := e S hS ((d S hS).symm (𝟙 S))
  hom_inv_id := by
    simpa only [Equiv.apply_symm_apply] using
      relative_transpose_transport P F K S R hS d e hd he R hR
        ((e R hR).symm (𝟙 R))
  inv_hom_id := by
    simpa only [Equiv.apply_symm_apply] using
      relative_transpose_transport P F K R S hR e d he hd S hS
        ((d S hS).symm (𝟙 S))

/-- The canonical comparison identifies the relative Hom bijections.
Source: uniqueness of a representing object
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: source naturality at the first representing object identifies every map
with its universal evaluation followed by its transpose. -/
theorem relativeRepresentingIso_transport
    {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
    (F : C ⥤ D) (K : D) (R S : C) (hR : P R) (hS : P S)
    (e : ∀ M, P M → (F.obj M ⟶ K) ≃ (M ⟶ R))
    (d : ∀ M, P M → (F.obj M ⟶ K) ≃ (M ⟶ S))
    (he : ∀ M N (hM : P M) (hN : P N) (v : M ⟶ N) (a : F.obj N ⟶ K),
      e M hM (F.map v ≫ a) = v ≫ e N hN a)
    (hd : ∀ M N (hM : P M) (hN : P N) (v : M ⟶ N) (a : F.obj N ⟶ K),
      d M hM (F.map v ≫ a) = v ≫ d N hN a)
    (M : C) (hM : P M) (a : F.obj M ⟶ K) :
    e M hM a ≫ (relativeRepresentingIso P F K R S hR hS e d he hd).hom =
      d M hM a :=
  relative_transpose_transport P F K R S hR e d he hd M hM a

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
  [HasCompactification f] (c : Compactification f)
  [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsLeftAdjoint]

/-- The normalized relative adjunction with the specified chart right adjoint.
Source: comparison-class adjunction clauses (2)--(3)
(blueprint: lem-sf-specified-standing-normalized-iso). -/
def specifiedStandingClass :
    FixedComparisonClassAdjunction A f c
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint
      (Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c))
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
      DerivedCategory.TStructure.t.plus :=
  (nonempty_fixedComparisonClassAdjunction_of_boundedBelow A c _ _
    (fun K hK ↦ specifiedExceptionalEtale_boundedBelow A c ⟨K, hK⟩)).some

/-- The canonical map from the specified exceptional value to the standing one,
including the difference between their site-comparison normalizations.
Source: normalized comparison-class adjunction clauses (2)--(3)
(blueprint: lem-sf-specified-standing-normalized-iso). -/
def specifiedExceptionalStandingIso
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    (sfFiniteExceptionalAt A c).obj K.obj ≅ (rightDerivedUpperShriek A f).obj K.obj :=
  relativeRepresentingIso
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) K.obj _ _
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
      (specifiedExceptionalEtale_boundedBelow A c K))
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f K.property)
    (fun M hM ↦ (specifiedStandingClass A c).homEquiv
      (HasCompactification.compactification f) M hM K.obj K.property)
    (fun _ hM ↦ rightDerivedUpperShriekHomEquiv f hM K.property)
    (fun M N hM hN v a ↦ (specifiedStandingClass A c).naturality_left
      (HasCompactification.compactification f) M N hM hN K.obj K.property v a)
    (fun _ _ hM hN v a ↦
      rightDerivedUpperShriekHomEquiv_naturality_left f hM hN K.property v a)

/-- The comparison isomorphism identifies the normalized relative bijection with
its upstream standing counterpart.
Source: uniqueness of relative right adjoints
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: apply the relative representing-object transport identity. -/
theorem specifiedExceptionalStandingIso_transport
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M ⟶ K.obj) :
    (specifiedStandingClass A c).homEquiv (HasCompactification.compactification f)
        M hM K.obj K.property a ≫ (specifiedExceptionalStandingIso A c K).hom =
      rightDerivedUpperShriekHomEquiv f hM K.property a := by
  unfold specifiedExceptionalStandingIso
  exact relativeRepresentingIso_transport
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) K.obj _ _
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
      (specifiedExceptionalEtale_boundedBelow A c K))
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f K.property)
    (fun M hM ↦ (specifiedStandingClass A c).homEquiv
      (HasCompactification.compactification f) M hM K.obj K.property)
    (fun _ hM ↦ rightDerivedUpperShriekHomEquiv f hM K.property)
    (fun M N hM hN v a ↦ (specifiedStandingClass A c).naturality_left
      (HasCompactification.compactification f) M N hM hN K.obj K.property v a)
    (fun _ _ hM hN v a ↦
      rightDerivedUpperShriekHomEquiv_naturality_left f hM hN K.property v a)
    M hM a

omit [HasCompactification f] in
/-- On a retained etale origin the relative chart bijection is the specified Hom chain.
Source: normalized comparison-class adjunction clause (2)
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: use normalization on the ordinary representative, then source naturality
along its realization isomorphism. The site comparison and its inverse cancel. -/
theorem specifiedStandingClass_chart
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A M)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M.obj)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M.obj ⟶
      K.obj) :
    (specifiedStandingClass A c).homEquiv c M.obj hM K.obj K.property a =
      specifiedExceptionalHomEquiv A c M W K a := by
  let C := specifiedStandingClass A c
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  have hW := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj W.complex.property
  let b := (fixedCompactSupportComparisonIso A c).inv.app W.complex ≫ F.map W.iso.hom ≫ a
  let t := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj b
  have hn := C.homEquiv_normalized W.complex hW K.obj K.property t
  have hl := C.naturality_left c _ _ hW hM K.obj K.property W.iso.hom a
  dsimp only [t] at hn
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_app_assoc] at hn
  rw [hl] at hn
  apply (cancel_epi W.iso.hom).mp
  change W.iso.hom ≫ C.homEquiv c M.obj hM K.obj K.property a = _
  rw [hn]
  change N.map ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)).homEquiv
        _ _ t) = W.iso.hom ≫ W.iso.inv ≫ N.map
      ((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)).homEquiv
          _ _ t)
  rw [Iso.hom_inv_id_assoc]
  rfl

omit [HasCompactification f] in
/-- The canonical compactification comparison on any retained etale realization.
Source: normalized comparison-class adjunction clause (3)
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: apply naturality to the realization isomorphism, use the normalization on
its representative, and cancel the compact-support image of that isomorphism. -/
theorem specifiedStandingClass_comparison
    (d : Compactification f)
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A M)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M.obj) :
    ((specifiedStandingClass A c).comparison d c).hom.app ⟨M.obj, hM⟩ =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map W.iso.inv ≫
        (fixedCompactSupportOriginIso A d c).hom.app W.complex ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map W.iso.hom := by
  let C := specifiedStandingClass A c
  have hW := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj W.complex.property
  let v : (⟨_, hW⟩ :
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) ⟶
      ⟨M.obj, hM⟩ := ObjectProperty.homMk W.iso.hom
  have hn := (C.comparison d c).hom.naturality v
  rw [C.comparison_normalized d c W.complex hW] at hn
  apply (cancel_epi
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map W.iso.hom)).mp
  change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
      W.iso.hom ≫ (C.comparison d c).hom.app ⟨M.obj, hM⟩ =
        (fixedCompactSupportOriginIso A d c).hom.app W.complex ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            W.iso.hom at hn
  rw [← Category.assoc, ← Functor.map_comp, W.iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact hn

/-- Evaluating the normalized specified-to-standing transpose by the actual standing
counit gives the prescribed change of compactification followed by the input arrow.
Source: normalized comparison-class adjunction clauses (2)--(3)
(blueprint: lem-sf-specified-standing-normalized-iso).
Proof: compatibility of the class bijections with compactification change, followed
by the representing-object comparison, identifies the result with the upstream
standing transpose. Apply its inverse, which is compact support followed by counit. -/
theorem specifiedExceptionalStandingIso_counit
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A M)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M.obj ⟶
      K.obj) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (specifiedExceptionalHomEquiv A c M W K a ≫
          (specifiedExceptionalStandingIso A c K).hom) ≫
        rightDerivedUpperShriekCounit f K.obj K.property =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map W.iso.inv ≫
        (fixedCompactSupportOriginIso A (HasCompactification.compactification f) c).hom.app
          W.complex ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map W.iso.hom ≫ a := by
  let C := specifiedStandingClass A c
  have hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M.obj :=
    ⟨W.complex.obj, W.complex.property, ⟨W.iso⟩⟩
  let s := HasCompactification.compactification f
  have hc := C.comparison_homEquiv s c M.obj hM K.obj K.property a
  rw [specifiedStandingClass_chart A c M W hM K a] at hc
  have ht := specifiedExceptionalStandingIso_transport A c K M.obj hM
    ((C.comparison s c).hom.app ⟨M.obj, hM⟩ ≫ a)
  rw [hc] at ht
  have hi := congrArg (rightDerivedUpperShriekHomEquiv f hM K.property).symm ht
  rw [Equiv.symm_apply_apply, rightDerivedUpperShriekHomEquiv_symm_apply] at hi
  rw [hi, specifiedStandingClass_comparison A c s M W hM]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale
