/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Splitting data for the trace of a finite étale morphism

Let `f : Y ⟶ X` be a morphism of schemes and `T` an object of the small étale site of `X`.
A *splitting* of `f` over `T` is a finite family of open and closed immersions
`i_j : V_j ⟶ T ×_X Y` exhibiting `T ×_X Y` as the coproduct of the `V_j`, such that each
composite `V_j ⟶ T ×_X Y ⟶ T` is an isomorphism, with explicitly given inverse `t_j`.

For an étale `f`, write `B_f T = T ×_X Y` viewed as an object of the small étale site of `X`.
The sheet sections `t_j ≫ i_j : T ⟶ B_f T` give, for every sheaf `F` with values in a
preadditive category, the *splitting sum* `∑_j F(t_j ≫ i_j) : F(B_f T) ⟶ F(T)`.
The predicate `Etale.FiniteEtaleTraceLocalSums f F τ` asks that a morphism
`τ : f_* f^* F ⟶ F` is given by these splitting sums on every split object, after
identifying `(f_* f^* F)(W)` with `F(B_f W)` through the restriction isomorphism
`Etale.upperStarIsoLocalizationRestriction`.

## Main definitions

- `AlgebraicGeometry.Etale.FiniteEtaleTraceSplitting`: splitting data.
- `AlgebraicGeometry.Etale.finiteEtaleTraceSplitPresieve`: the split presieve.
- `AlgebraicGeometry.Etale.FiniteEtaleTraceSplitting.sum`: the splitting sum.
- `AlgebraicGeometry.Etale.FiniteEtaleTraceLocalSums`: the local sum predicate.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- A *splitting* of `f : Y ⟶ X` over an object `T` of the small étale site of `X`: a finite
index type `ι`, schemes `V j`, a coproduct cofan `i j : V j ⟶ T ×_X Y` of open and closed
immersions, and inverses `t j : T ⟶ V j` of the composites `i j ≫ pullback.fst`. The index type
may be empty. All data are explicit.
(blueprint: `def-weil-pbc-finite-etale-trace-splitting-data`) -/
structure FiniteEtaleTraceSplitting (T : X.Etale) where
  /-- The finite index type of the sheets. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The sheets. -/
  V : ι → Scheme.{u}
  /-- The inclusions of the sheets into `T ×_X Y`. -/
  i (j : ι) : V j ⟶ pullback T.hom f
  /-- The sheets form a coproduct decomposition of `T ×_X Y`. -/
  isColimit : IsColimit (Cofan.mk (pullback T.hom f) i)
  isOpenImmersion (j : ι) : IsOpenImmersion (i j)
  isClosedImmersion (j : ι) : IsClosedImmersion (i j)
  /-- The inverse of the projection of the `j`-th sheet to `T`. -/
  t (j : ι) : T.left ⟶ V j
  t_i_fst (j : ι) : t j ≫ i j ≫ pullback.fst T.hom f = 𝟙 T.left
  i_fst_t (j : ι) : i j ≫ pullback.fst T.hom f ≫ t j = 𝟙 (V j)

attribute [instance] FiniteEtaleTraceSplitting.fintype

/-- The *split presieve* on `W`: all arrows `T ⟶ W` of the small étale site of `X` whose
source `T` admits a splitting of `f`.
(blueprint: `def-weil-pbc-finite-etale-trace-splitting-data`) -/
def finiteEtaleTraceSplitPresieve (W : X.Etale) : Presieve W :=
  fun T _ ↦ Nonempty (FiniteEtaleTraceSplitting f T)

variable {f} (hf : Etale f)

/-- For an étale `f : Y ⟶ X`, the functor `B_f : W ↦ W ×_X Y` on the small étale site of `X`,
base change along `f` followed by composition with `f`. -/
noncomputable def finiteEtaleTraceBaseChange : X.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf

namespace FiniteEtaleTraceSplitting

variable {T : X.Etale} (s : FiniteEtaleTraceSplitting f T)

/-- The `j`-th sheet section `t j ≫ i j : T ⟶ B_f T` of a splitting, as a morphism of the small
étale site of `X`. -/
noncomputable def sheetSection (j : s.ι) : T ⟶ (finiteEtaleTraceBaseChange hf).obj T :=
  MorphismProperty.Over.homMk (s.t j ≫ s.i j) (by
    simp only [finiteEtaleTraceBaseChange, Functor.comp_obj, MorphismProperty.Over.map_obj_hom,
      MorphismProperty.Over.pullback_obj_hom, assoc, ← pullback.condition]
    rw [reassoc_of% s.t_i_fst j])

lemma sheetSection_left (j : s.ι) : (s.sheetSection hf j).left = s.t j ≫ s.i j :=
  rfl

variable (A : Type u') [Category.{u + 1} A] [Preadditive A]

/-- The *splitting sum* `∑_j F(t_j ≫ i_j) : F(B_f T) ⟶ F(T)` of a splitting, for a sheaf `F`
on the small étale site of `X` with values in a preadditive category. For abelian groups it
sends a section `s ∈ F(B_f T)` to `∑_j F(t_j ≫ i_j) s`.
(blueprint: `def-weil-pbc-finite-etale-trace-splitting-data`) -/
noncomputable def sum (F : Sheaf X.smallEtaleTopology A) :
    F.obj.obj (op ((finiteEtaleTraceBaseChange hf).obj T)) ⟶ F.obj.obj (op T) :=
  ∑ j, F.obj.map (s.sheetSection hf j).op

end FiniteEtaleTraceSplitting

section LocalSums

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction isomorphism `c_{F,W} : (f_* f^* F)(W) ≅ F(W ×_X Y)` for an étale `f`,
induced by `Etale.upperStarIsoLocalizationRestriction`. -/
noncomputable def finiteEtaleTraceRestrictionIso (F : Sheaf X.smallEtaleTopology A)
    (W : X.Etale) :
    ((f)_*[A].obj ((f)^*[A].obj F)).obj.obj (op W) ≅
      F.obj.obj (op ((finiteEtaleTraceBaseChange hf).obj W)) :=
  ((sheafToPresheaf _ _).mapIso ((Etale.upperStarIsoLocalizationRestriction A f hf).app F)).app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))

/-- The predicate `LocalSums(f, F, τ)` for an étale `f : Y ⟶ X`, a sheaf `F` on the small étale
site of `X` and a morphism `τ : f_* f^* F ⟶ F`: for every object `W` and every splitting of `f`
over `W`, the composite `τ_W ∘ c_{F,W}⁻¹ : F(W ×_X Y) ⟶ F(W)` is the splitting sum. This is
only a predicate; it chooses no trace.
(blueprint: `def-weil-pbc-finite-etale-trace-local-sums`) -/
def FiniteEtaleTraceLocalSums (F : Sheaf X.smallEtaleTopology A)
    (τ : (f)_*[A].obj ((f)^*[A].obj F) ⟶ F) : Prop :=
  ∀ (W : X.Etale) (s : FiniteEtaleTraceSplitting f W),
    (finiteEtaleTraceRestrictionIso hf A F W).inv ≫ τ.hom.app (op W) = s.sum hf A F

end LocalSums

end Etale

end AlgebraicGeometry
