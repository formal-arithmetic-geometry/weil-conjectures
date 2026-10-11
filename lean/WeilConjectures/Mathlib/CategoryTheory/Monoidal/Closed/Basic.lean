/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Zero objects and internal homs along monoidal functors

In a monoidal closed category with zero morphisms, `K ⊗ M` is a zero object if `M` is, since
`K ⊗ -` is a left adjoint. If the category is moreover braided, the same holds if `K` is a
zero object, and the internal hom `[K, B]` out of a zero object `K` is a zero object.

A lax monoidal functor `G : C ⥤ D` between monoidal closed categories has a comparison map
`G [A, B] ⟶ [G A, G B]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), the mate of its
tensorator. This is the monoidal generalisation of `CategoryTheory.expComparison` asked for in
the TODO of `Mathlib.CategoryTheory.Monoidal.Closed.Functor`. If `G` is monoidal and an
equivalence, the comparison map is an isomorphism (`CategoryTheory.Functor.Monoidal.commIhom`);
compare `CategoryTheory.MonoidalClosed.ofEquiv`, which transports the closed structure along a
monoidal equivalence. The comparison maps of a composite are composites of comparison maps
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison_comp_app`), and they are compatible with
monoidal natural transformations
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison_app_comp_map_app`).

A pairing `b : X ⊗ Y ⟶ 𝟙_ C` is *perfect* (`CategoryTheory.MonoidalClosed.IsPerfectPairing`)
if its adjoint `Y ⟶ [X, 𝟙_ C]` is an isomorphism. Perfectness is preserved by precomposition
with an isomorphism in the first variable
(`CategoryTheory.MonoidalClosed.IsPerfectPairing.whiskerRight_comp`).
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] [HasZeroMorphisms C]

/-- In a monoidal closed category, `K ⊗ M` is a zero object if `M` is. -/
lemma isZero_tensorObj_of_isZero_right (K : C) {M : C} (hM : IsZero M) : IsZero (K ⊗ M) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((ihom.adjunction K).homEquiv _ _).injective (hM.eq_of_src _ _)

/-- In a braided monoidal closed category, `K ⊗ M` is a zero object if `K` is. -/
lemma isZero_tensorObj_of_isZero_left [BraidedCategory C] {K : C} (hK : IsZero K) (M : C) :
    IsZero (K ⊗ M) :=
  (isZero_tensorObj_of_isZero_right M hK).of_iso (β_ K M)

/-- In a braided monoidal closed category, the internal hom `[K, B]` out of a zero object `K`
is a zero object. -/
lemma isZero_ihom_obj_of_isZero [BraidedCategory C] {K : C} (hK : IsZero K) (B : C) :
    IsZero ((ihom K).obj B) := by
  rw [IsZero.iff_id_eq_zero]
  exact ((ihom.adjunction K).homEquiv _ _).symm.injective
    ((isZero_tensorObj_of_isZero_left hK _).eq_of_src _ _)

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D)

namespace LaxMonoidal

variable [G.LaxMonoidal]

/-- The tensorator `μ : G A ⊗ G X ⟶ G (A ⊗ X)` of a lax monoidal functor, as a square
```
          tensorLeft A
       C ─────────────▶ C
       │                │
      G│       ↗        │G
       ▼                ▼
       D ─────────────▶ D
         tensorLeft (G A)
```
-/
@[simps!]
def μTwoSquare (A : C) : TwoSquare G (tensorLeft A) (tensorLeft (G.obj A)) G :=
  .mk _ _ _ _ { app X := μ G A X }

/-- The comparison map `G [A, B] ⟶ [G A, G B]` of a lax monoidal functor between monoidal closed
categories, as a square
```
            ihom A
       C ─────────────▶ C
       │                │
      G│       ↘        │G
       ▼                ▼
       D ─────────────▶ D
          ihom (G A)
```
It is the mate of the tensorator `μ : G A ⊗ G X ⟶ G (A ⊗ X)`
(`CategoryTheory.Functor.LaxMonoidal.μTwoSquare`); for a cartesian closed functor this is
`CategoryTheory.expComparison`. -/
def ihomComparison (A : C) : TwoSquare (ihom A) G G (ihom (G.obj A)) :=
  mateEquiv (ihom.adjunction A) (ihom.adjunction (G.obj A)) (μTwoSquare G A)

/-- The comparison map `G [A, B] ⟶ [G A, G B]` is compatible with evaluation:
```
  G A ⊗ G [A, B] ──────▶ G A ⊗ [G A, G B]
        │                       │
       μ│                       │ev
        ▼                       ▼
  G (A ⊗ [A, B]) ──G ev──▶     G B
```
-/
@[reassoc]
lemma ihomComparison_ev (A B : C) :
    G.obj A ◁ (ihomComparison G A).natTrans.app B ≫ (ihom.ev (G.obj A)).app (G.obj B) =
      μ G A _ ≫ G.map ((ihom.ev A).app B) :=
  mateEquiv_counit _ _ (μTwoSquare G A) B

/-- The comparison map `G [A, B] ⟶ [G A, G B]` is compatible with coevaluation:
```
       G B ──────G coev──────▶ G [A, A ⊗ B]
        │                           │
    coev│                           │
        ▼                           ▼
  [G A, G A ⊗ G B] ──[G A, μ]──▶ [G A, G (A ⊗ B)]
```
-/
@[reassoc]
lemma coev_ihomComparison (A B : C) :
    G.map ((ihom.coev A).app B) ≫ (ihomComparison G A).natTrans.app (A ⊗ B) =
      (ihom.coev (G.obj A)).app (G.obj B) ≫ (ihom (G.obj A)).map (μ G A B) :=
  unit_mateEquiv _ _ (μTwoSquare G A) B

end LaxMonoidal

namespace Monoidal

variable [G.Monoidal] [G.IsEquivalence]

instance (A : C) : IsIso (LaxMonoidal.μTwoSquare G A).natTrans :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun X ↦ inferInstanceAs (IsIso (LaxMonoidal.μ G A X))

/-- A monoidal functor which is an equivalence preserves internal homs: the comparison map
`G [A, B] ⟶ [G A, G B]` is an isomorphism. Taking mates once more, along the adjunction
`G ⊣ G⁻¹`, gives the conjugate of the tensorator, which is an isomorphism; and taking mates along
adjoint equivalences preserves isomorphisms. -/
instance (A : C) : IsIso (LaxMonoidal.ihomComparison G A).natTrans := by
  let adj : G ⊣ G.inv := G.asEquivalence.toAdjunction
  have h := iterated_mateEquiv_conjugateEquiv (ihom.adjunction A) (ihom.adjunction (G.obj A))
    adj adj (LaxMonoidal.μTwoSquare G A)
  have : IsIso (mateEquiv adj adj (LaxMonoidal.ihomComparison G A)).natTrans := by
    rw [LaxMonoidal.ihomComparison, h]
    infer_instance
  have : IsIso adj.unit := inferInstanceAs (IsIso G.asEquivalence.unitIso.hom)
  have : IsIso adj.counit := inferInstanceAs (IsIso G.asEquivalence.counitIso.hom)
  rw [← (mateEquiv adj adj).symm_apply_apply (LaxMonoidal.ihomComparison G A)]
  simp only [mateEquiv_symm_apply]
  infer_instance

/-- A monoidal functor `G` which is an equivalence between monoidal closed categories commutes
with internal homs, `G [A, -] ≅ [G A, G -]`:
```
            ihom A
       C ─────────────▶ C
       │                │
      G│       ≅        │G
       ▼                ▼
       D ─────────────▶ D
          ihom (G A)
```
-/
noncomputable def commIhom (A : C) : ihom A ⋙ G ≅ G ⋙ ihom (G.obj A) :=
  asIso (LaxMonoidal.ihomComparison G A).natTrans

/-- A monoidal functor `G` which is an equivalence between monoidal closed categories preserves
internal homs: `G [A, B] ≅ [G A, G B]`. -/
@[simps!]
noncomputable def ihomObjIso (A B : C) :
    G.obj ((ihom A).obj B) ≅ (ihom (G.obj A)).obj (G.obj B) :=
  (commIhom G A).app B

end Monoidal

end CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- A pairing `b : X ⊗ Y ⟶ 𝟙_ C` is *perfect* if its tensor–internal-hom adjoint
`curry b : Y ⟶ [X, 𝟙_ C]` is an isomorphism,
```
 X ⊗ Y ──b──▶ 𝟙_ C        Y ──curry b──▶ [X, 𝟙_ C]   (iso)
```
i.e. if `b` identifies `Y` with the dual `[X, 𝟙_ C]` of `X`. No braiding is needed: the adjoint
is taken in the second variable.

This is weaker than an exact pairing (`CategoryTheory.ExactPairing`), which also asks for a
coevaluation `𝟙_ C ⟶ Y ⊗ X` satisfying the zigzag identities: the evaluation of an exact
pairing `ExactPairing X Y` is a perfect pairing `Y ⊗ X ⟶ 𝟙_ C`, but a perfect pairing of an
object that is not dualizable is not part of an exact pairing. It is not to be confused with
`LinearMap.IsPerfPair`, perfectness of a bilinear form on modules.

This is the perfectness of a pairing of blueprint `sk-def-pairing` and
`def-pod-perfect-derived-pairing`; its symmetry in the two variables (blueprint
`rem-ptr-pod-perfect-derived-pairing-6`) is
`CategoryTheory.MonoidalClosed.isPerfectPairing_braiding_hom_comp_iff`. -/
structure IsPerfectPairing {X Y : C} (b : X ⊗ Y ⟶ 𝟙_ C) : Prop where
  /-- The adjoint `Y ⟶ [X, 𝟙_ C]` of the pairing is an isomorphism. -/
  isIso : IsIso (curry b)

/-- A perfect pairing `b : X ⊗ Y ⟶ 𝟙_ C` identifies `Y` with the dual `[X, 𝟙_ C]`. -/
noncomputable def IsPerfectPairing.iso {X Y : C} {b : X ⊗ Y ⟶ 𝟙_ C}
    (h : IsPerfectPairing b) : Y ≅ (ihom X).obj (𝟙_ C) :=
  @asIso _ _ _ _ _ h.isIso

instance isIso_pre {X X' : C} (f : X' ⟶ X) [IsIso f] : IsIso (pre f) :=
  ⟨pre (inv f), by rw [← pre_map, IsIso.inv_hom_id, pre_id],
    by rw [← pre_map, IsIso.hom_inv_id, pre_id]⟩

/-- Precomposing a perfect pairing `b : X ⊗ Y ⟶ 𝟙_ C` with an isomorphism `f : X' ⟶ X` in the
first variable gives a perfect pairing `X' ⊗ Y ⟶ 𝟙_ C`: the adjoint of the composite is the
adjoint of `b` followed by the isomorphism `pre f`,
```
         curry b                 pre f
  Y ─────────────▶ [X, 𝟙_ C] ─────────▶ [X', 𝟙_ C]
``` -/
lemma IsPerfectPairing.whiskerRight_comp {X X' Y : C} {b : X ⊗ Y ⟶ 𝟙_ C}
    (h : IsPerfectPairing b) (f : X' ⟶ X) [IsIso f] : IsPerfectPairing (f ▷ Y ≫ b) :=
  ⟨by
    have := h.isIso
    rw [← curry_pre_app]
    infer_instance⟩

end CategoryTheory.MonoidalClosed

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory MonoidalClosed

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E] [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalClosed E]

/-- The comparison map `G [A, B] ⟶ [G A, G B]` is characterised by its compatibility with
evaluation. -/
lemma ihomComparison_app_eq_curry (G : C ⥤ D) [G.LaxMonoidal] (A B : C) :
    (ihomComparison G A).natTrans.app B = curry (μ G A _ ≫ G.map ((ihom.ev A).app B)) := by
  rw [← ihomComparison_ev, ← uncurry_eq, curry_uncurry]

/-- The comparison map of a composite of lax monoidal functors is the composite of the comparison
maps. -/
lemma ihomComparison_comp_app (F : C ⥤ D) (G : D ⥤ E) [F.LaxMonoidal] [G.LaxMonoidal]
    (A B : C) :
    (ihomComparison (F ⋙ G) A).natTrans.app B =
      G.map ((ihomComparison F A).natTrans.app B) ≫
        (ihomComparison G (F.obj A)).natTrans.app (F.obj B) := by
  rw [ihomComparison_app_eq_curry, curry_eq_iff, uncurry_eq]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, ihomComparison_ev, μ_natural_right_assoc,
    ← G.map_comp, ihomComparison_ev, comp_μ]
  simp

/-- The comparison maps are compatible with monoidal natural transformations. -/
lemma ihomComparison_app_comp_map_app {F F' : C ⥤ D} [F.LaxMonoidal] [F'.LaxMonoidal]
    (τ : F ⟶ F') [NatTrans.IsMonoidal τ] (A B : C) :
    (ihomComparison F A).natTrans.app B ≫ (ihom (F.obj A)).map (τ.app B) =
      τ.app _ ≫ (ihomComparison F' A).natTrans.app B ≫ (pre (τ.app A)).app (F'.obj B) := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_eq, ihomComparison_ev, uncurry_natural_left,
    uncurry_pre_app, uncurry_eq, ihomComparison_ev, Category.assoc, ← tensorHom_def'_assoc,
    ← NatTrans.IsMonoidal.tensor_assoc]
  exact congrArg _ (τ.naturality _)

/-- If `τ : F ≅ F'` is a monoidal natural isomorphism, the comparison maps of `F` are isomorphisms
if those of `F'` are. -/
lemma isIso_ihomComparison_of_iso {F F' : C ⥤ D} [F.LaxMonoidal] [F'.LaxMonoidal]
    (τ : F ≅ F') [NatTrans.IsMonoidal τ.hom] (A : C)
    [IsIso (ihomComparison F' A).natTrans] : IsIso (ihomComparison F A).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  have h := ihomComparison_app_comp_map_app τ.hom A B
  have : IsIso ((ihomComparison F A).natTrans.app B ≫ (ihom (F.obj A)).map (τ.hom.app B)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((ihom (F.obj A)).map (τ.hom.app B))

end CategoryTheory.Functor.LaxMonoidal
