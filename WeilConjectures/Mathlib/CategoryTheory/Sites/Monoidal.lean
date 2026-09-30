/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!

# The tensor product of sheaves is preadditive and linear,
  the pushforward of sheaves is lax braided, the pullback is monoidal

Let `A` be an abelian monoidal category whose tensor product is additive in each variable
and `J` a Grothendieck topology with `HasSheafify J A` such that the localized monoidal
structure `Sheaf.monoidalCategory` on `Sheaf J A` is available (`(J.W).IsMonoidal`).
We show that this monoidal structure is compatible with the preadditive structure on
`Sheaf J A`, i.e. `MonoidalPreadditive (Sheaf J A)`, and, when `A` is moreover `R`-linear
with `R`-linear tensor product, that it is compatible with the `R`-linear structure,
i.e. `MonoidalLinear R (Sheaf J A)`.

The sheafification functor `presheafToSheaf J A` is braided, hence its right adjoint
`sheafToPresheaf J A` is lax braided.

If `F : C ⥤ D` is a continuous functor of sites, the pushforward
`F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is obtained by sheafifying the
restriction along `F.op` of the underlying presheaf. As restriction is a braided functor
between the (pointwise monoidal) categories of presheaves, the pushforward is lax braided.
When `A` is symmetric this says that `F.sheafPushforwardContinuous A J K` is lax symmetric
monoidal.

Its left adjoint, the pullback `sheafPullbackConstruction.sheafPullback F A J K` (left Kan
extension along `F.op` followed by sheafification), is therefore oplax monoidal. If `F` is
representably flat and the tensor product of `A` preserves the colimits of shape
`CostructuredArrow F.op X` in each variable (for example if `A` is closed), then the pullback
is strong monoidal. The proof compares the sheaf-level adjunction, precomposed with
sheafification, with the composite of the presheaf-level adjunction
`F.op.lan ⊣ (whiskeringLeft _ _ A).obj F.op` and sheafification: both have right adjoint the
underlying presheaf of the pushforward, as lax monoidal functors up to a monoidal isomorphism,
so their oplax structures correspond (`CategoryTheory.isIso_δ_of_conjugateIso`). The left Kan
extension is strong monoidal by `CategoryTheory.Functor.isIso_lan_δ`, and so is
sheafification.

## Main results

- `CategoryTheory.Sheaf.monoidalPreadditive`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is preadditive.
- `CategoryTheory.Sheaf.monoidalLinear`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is `R`-linear.
- `CategoryTheory.sheafToPresheafLaxBraided`: the underlying presheaf functor is lax braided.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxBraided`: the pushforward of sheaves
  along a continuous functor of sites is lax braided.
- `CategoryTheory.Functor.sheafPullbackConstruction.isIso_δ_sheafPullback` and
  `CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback`: the comparison
  maps of the oplax monoidal pullback along a representably flat continuous functor are
  isomorphisms.
- `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackMonoidal`: the pullback of
  sheaves along a representably flat continuous functor is strong monoidal.
-/




@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf

open MonoidalCategory CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [Abelian A] [MonoidalPreadditive A]
  [HasSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] monoidalCategory

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
tensorLeft P ⋙ presheafToSheaf J A` in the second variable. -/
noncomputable def presheafToSheafCompTensorLeftIso (P : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
      tensorLeft P ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun Q ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
tensorRight Q ⋙ presheafToSheaf J A` in the first variable. -/
noncomputable def presheafToSheafCompTensorRightIso (Q : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
      tensorRight Q ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun P ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- Tensoring on the left with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorLeftIso (X : Sheaf J A) :
    tensorLeft X ≅ sheafToPresheaf J A ⋙ tensorLeft X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorLeft _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorLeftIso X.obj)

/-- Tensoring on the right with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorRightIso (X : Sheaf J A) :
    tensorRight X ≅ sheafToPresheaf J A ⋙ tensorRight X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).flip.mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorRight _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorRightIso X.obj)

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Additive :=
  Functor.additive_of_iso (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Additive :=
  Functor.additive_of_iso (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is preadditive when `A` is an abelian monoidal category with additive tensor product. -/
instance monoidalPreadditive : MonoidalPreadditive (Sheaf J A) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} _ _ := (tensorLeft X).map_add
  add_whiskerRight {X _ _} _ _ := (tensorRight X).map_add

section Linear

variable (R : Type*) [Semiring R] [Linear R A] [MonoidalLinear R A]

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Linear R :=
  Functor.linear_of_iso R (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Linear R :=
  Functor.linear_of_iso R (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is `R`-linear when `A` is an abelian `R`-linear monoidal category with `R`-linear tensor
product. -/
instance monoidalLinear : MonoidalLinear R (Sheaf J A) where
  whiskerLeft_smul X {_ _} r f := (tensorLeft X).map_smul r f
  smul_whiskerRight r {_ _} f X := (tensorRight X).map_smul r f

end Linear

end CategoryTheory.Sheaf

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The functor sending a sheaf to its underlying presheaf is lax monoidal, being the right
adjoint of the (strong) monoidal sheafification functor. -/
noncomputable instance sheafToPresheafLaxMonoidal : (sheafToPresheaf J A).LaxMonoidal :=
  (sheafificationAdjunction J A).rightAdjointLaxMonoidal

/-- The functor sending a sheaf to its underlying presheaf is lax braided, being the right
adjoint of the braided sheafification functor. -/
noncomputable instance sheafToPresheafLaxBraided : (sheafToPresheaf J A).LaxBraided :=
  (sheafificationAdjunction J A).rightAdjointLaxBraided

namespace Functor

variable [F.IsContinuous J K] [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

/-- The pushforward of sheaves along a continuous functor `F : C ⥤ D` is the sheafification of
the restriction along `F.op` of the underlying presheaf. -/
noncomputable def sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso :
    sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op ⋙ presheafToSheaf J A ≅
      F.sheafPushforwardContinuous A J K :=
  isoWhiskerLeft (F.sheafPushforwardContinuous A J K)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (F.sheafPushforwardContinuous A J K).rightUnitor

/-- The pushforward of sheaves along a continuous functor of sites is lax monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxMonoidal :
    (F.sheafPushforwardContinuous A J K).LaxMonoidal :=
  LaxMonoidal.transport (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

/-- The pushforward of sheaves along a continuous functor of sites is lax braided. When `A` is
symmetric, this says that the pushforward is lax symmetric monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxBraided :
    (F.sheafPushforwardContinuous A J K).LaxBraided :=
  have := LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)
  LaxBraided.ofNatIso (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

end Functor

namespace Functor.sheafPullbackConstruction

open Limits MonoidalCategory OplaxMonoidal

variable [F.IsContinuous J K] [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]

/-- The pullback of sheaves along a continuous functor of sites is oplax monoidal, being left
adjoint to the lax monoidal pushforward. -/
noncomputable instance sheafPullbackOplaxMonoidal : (sheafPullback F A J K).OplaxMonoidal :=
  (sheafAdjunctionContinuous F A J K).leftAdjointOplaxMonoidal

/-- The adjunction between the pullback and the pushforward of sheaves is monoidal. -/
instance isMonoidal_sheafAdjunctionContinuous : (sheafAdjunctionContinuous F A J K).IsMonoidal :=
  inferInstanceAs (letI := (sheafAdjunctionContinuous F A J K).leftAdjointOplaxMonoidal
    (sheafAdjunctionContinuous F A J K).IsMonoidal)

/-- The comparison from the restriction along `F.op` of the underlying presheaf of a sheaf to
the underlying presheaf of its pushforward: the unit of sheafification followed by the
isomorphism `sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso`. Both functors send a
sheaf `P` to `F.op ⋙ P.obj`, and this is a monoidal isomorphism between them. -/
noncomputable def sheafToPresheafCompWhiskeringLeftToPushforward :
    sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op ⟶
      F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A :=
  (sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op).rightUnitor.inv ≫
    whiskerLeft _ (sheafificationAdjunction J A).unit ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (Functor.associator _ _ _).hom _ ≫
    whiskerRight (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K).hom _

instance : NatTrans.IsMonoidal (sheafToPresheafCompWhiskeringLeftToPushforward F A J K) := by
  have := LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)
  dsimp only [sheafToPresheafCompWhiskeringLeftToPushforward]
  infer_instance

instance : IsIso (sheafToPresheafCompWhiskeringLeftToPushforward F A J K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  -- the unit of sheafification is an isomorphism on the sheaf `F.op ⋙ P.obj`
  have : IsIso (toSheafify J (F.op ⋙ P.obj)) :=
    isIso_toSheafify J ((F.sheafPushforwardContinuous A J K).obj P).property
  dsimp [sheafToPresheafCompWhiskeringLeftToPushforward]
  simp only [Category.id_comp]
  infer_instance

instance : NatTrans.IsMonoidal
    (asIso (sheafToPresheafCompWhiskeringLeftToPushforward F A J K)).symm.hom :=
  have : NatTrans.IsMonoidal (asIso (sheafToPresheafCompWhiskeringLeftToPushforward F A J K)).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (sheafToPresheafCompWhiskeringLeftToPushforward F A J K))
  inferInstanceAs
    (NatTrans.IsMonoidal (asIso (sheafToPresheafCompWhiskeringLeftToPushforward F A J K)).inv)

variable [RepresentablyFlat F]
  [∀ (X : Dᵒᵖ) (M : A), PreservesColimitsOfShape (CostructuredArrow F.op X) (tensorLeft M)]
  [∀ (X : Dᵒᵖ) (M : A), PreservesColimitsOfShape (CostructuredArrow F.op X) (tensorRight M)]

/-- The comparison map `δ` of the pullback of sheaves along a representably flat functor is
an isomorphism on sheafifications of presheaves. The pullback precomposed with sheafification
is left adjoint to the underlying presheaf of the pushforward, as is left Kan extension along
`F.op` followed by sheafification, which is strong monoidal. -/
lemma isIso_δ_sheafPullback_presheafToSheaf_obj (P Q : Cᵒᵖ ⥤ A) :
    IsIso (δ (sheafPullback F A J K) ((presheafToSheaf J A).obj P)
      ((presheafToSheaf J A).obj Q)) := by
  have : IsIso (δ (F.op.lan ⋙ presheafToSheaf K A) P Q) := by
    rw [comp_δ]
    infer_instance
  have := isIso_δ_of_conjugateIso
    ((sheafificationAdjunction J A).comp (sheafAdjunctionContinuous F A J K))
    ((F.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (asIso (sheafToPresheafCompWhiskeringLeftToPushforward F A J K)).symm P Q
  rw [comp_δ] at this
  exact IsIso.of_isIso_comp_left ((sheafPullback F A J K).map (δ (presheafToSheaf J A) P Q)) _

/-- The comparison map `δ : F^*(S ⊗ T) ⟶ F^*S ⊗ F^*T` of the pullback of sheaves along a
representably flat functor is an isomorphism. -/
instance isIso_δ_sheafPullback (S T : Sheaf J A) : IsIso (δ (sheafPullback F A J K) S T) := by
  have := isIso_δ_sheafPullback_presheafToSheaf_obj F A J K S.obj T.obj
  have h := δ_natural (sheafPullback F A J K) ((sheafificationAdjunction J A).counit.app S)
    ((sheafificationAdjunction J A).counit.app T)
  rw [← IsIso.inv_comp_eq] at h
  change _ = δ _ S T at h
  rw [← h]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

/-- The comparison map `η : F^*𝟙 ⟶ 𝟙` of the pullback of sheaves along a representably flat
functor is an isomorphism. -/
instance isIso_η_sheafPullback : IsIso (η (sheafPullback F A J K)) := by
  have : IsIso (η (F.op.lan ⋙ presheafToSheaf K A)) := by
    rw [comp_η]
    infer_instance
  have := isIso_η_of_conjugateIso
    ((sheafificationAdjunction J A).comp (sheafAdjunctionContinuous F A J K))
    ((F.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (asIso (sheafToPresheafCompWhiskeringLeftToPushforward F A J K)).symm
  rw [comp_η] at this
  exact IsIso.of_isIso_comp_left ((sheafPullback F A J K).map (η (presheafToSheaf J A))) _

/-- The pullback of sheaves along a representably flat continuous functor is strong monoidal,
its oplax structure `sheafPullbackOplaxMonoidal` having invertible comparison maps. -/
@[instance_reducible]
noncomputable def sheafPullbackMonoidal : (sheafPullback F A J K).Monoidal :=
  .ofOplaxMonoidal _

end Functor.sheafPullbackConstruction

end CategoryTheory
