/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction along a continuous and cocontinuous functor commutes with sheafification

Let `H : C ⥤ D` be a functor between sites which is both continuous and cocontinuous, and let
`A` be a concrete category in which sheafification is characterised by local bijectivity.
For a presheaf `P` on `D`, the restriction `H.op ⋙ sheafify K P` is a sheaf on `C`, and the
restriction of the sheafification map `P ⟶ sheafify K P` is locally bijective, so that
`H.op ⋙ sheafify K P` is the sheafification of `H.op ⋙ P`.

## Main definitions

- `CategoryTheory.Sheaf.isoOfIsLocallyBijective`: a locally bijective map from a presheaf to a
  sheaf identifies the sheaf with the sheafification of the presheaf.
- `CategoryTheory.Functor.sheafifyCompIso`: the isomorphism
  `sheafify J (H.op ⋙ P) ≅ H.op ⋙ sheafify K P`.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- A locally bijective morphism `φ : P ⟶ Q.obj` from a presheaf to a sheaf identifies `Q` with
the sheafification of `P`; the isomorphism is the one induced by `φ`. -/
noncomputable def Sheaf.isoOfIsLocallyBijective (J : GrothendieckTopology C)
    [HasWeakSheafify J A] [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)] {P : Cᵒᵖ ⥤ A} {Q : Sheaf J A} (φ : P ⟶ Q.obj)
    [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ] :
    (presheafToSheaf J A).obj P ≅ Q :=
  have hφ : CategoryTheory.toSheafify J P ≫
      (((sheafificationAdjunction J A).homEquiv P Q).symm φ).hom = φ :=
    toSheafify_sheafifyLift J φ Q.property
  have : IsIso ((sheafificationAdjunction J A).homEquiv P Q |>.symm φ) := by
    rw [← Sheaf.isLocallyBijective_iff_isIso (FA := FA) (CA := CA)]
    refine ⟨?_, ?_⟩
    · rw [Sheaf.IsLocallyInjective, ← Presheaf.comp_isLocallyInjective_iff J
        (CategoryTheory.toSheafify J P), hφ]
      infer_instance
    · rw [Sheaf.IsLocallySurjective, ← Presheaf.comp_isLocallySurjective_iff J
        (CategoryTheory.toSheafify J P), hφ]
      infer_instance
  asIso ((sheafificationAdjunction J A).homEquiv P Q |>.symm φ)

/-- **Restriction along a continuous and cocontinuous functor commutes with sheafification**:
for `H : C ⥤ D` continuous and cocontinuous and a presheaf `P` on `D`, the sheafification of
`H.op ⋙ P` is the restriction of the sheafification of `P`, through the map induced by the
restriction of `P ⟶ sheafify K P`. -/
noncomputable def Functor.sheafifyCompIso (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (H : C ⥤ D) [H.IsContinuous J K] [H.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A] [J.WEqualsLocallyBijective A]
    [K.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)] (P : Dᵒᵖ ⥤ A) :
    (presheafToSheaf J A).obj (H.op ⋙ P) ≅
      (H.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P) :=
  have := Presheaf.isLocallyInjective_whisker J K H (CategoryTheory.toSheafify K P)
  have := Presheaf.isLocallySurjective_whisker J K H (CategoryTheory.toSheafify K P)
  Sheaf.isoOfIsLocallyBijective J (Q := (H.sheafPushforwardContinuous A J K).obj
    ((presheafToSheaf K A).obj P)) (whiskerLeft H.op (CategoryTheory.toSheafify K P))

end CategoryTheory
