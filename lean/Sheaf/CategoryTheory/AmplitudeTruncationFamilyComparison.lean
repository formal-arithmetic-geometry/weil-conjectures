/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle

/-! # Uniform finite cohomological windows for families

Source: blueprint sec-six-functors-basics, sk-prop-ctf-finite-proper-localizing.proof.md,
Étale statements and Transfer; Stacks Tags 07D9 and 08J5.
(blueprint: lem-sfb-amplitude-truncation-family-comparison)

Families are diagrams on `Discrete I`. Each of the four arrows below is explicitly
an evaluation of a natural transformation on this diagram category. Thus its naturality
in all morphisms of families is part of its type. `colim` is the ambient derived
coproduct functor, and its action on a transformation is the map induced by coprojections.
The first two transformations take the coproduct before `G`, the last two after `G`.
-/

@[expose] public section

universe uA uB vA vB w dA dB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

open ZeroObject CategoryTheory.Pretriangulated

namespace DerivedCategory

private theorem isIso_map_colimMap_of_sigmaMap
    {C : Type*} [Category* C] [HasCoproducts.{w} C]
    {D : Type*} [Category* D] (F : C ⥤ D) {I : Type w}
    {X Y : Discrete I ⥤ C} (f : X ⟶ Y)
    (h : IsIso (F.map (Limits.Sigma.map (fun i ↦ f.app ⟨i⟩)))) :
    IsIso (F.map (colim.map f)) := by
  have he : (Limits.Sigma.isoColimit X).hom ≫ colim.map f =
      Limits.Sigma.map (fun i ↦ f.app ⟨i⟩) ≫ (Limits.Sigma.isoColimit Y).hom := by
    apply Limits.Sigma.hom_ext
    intro i
    simp
  have he' := congrArg F.map he
  rw [F.map_comp, F.map_comp] at he'
  have : IsIso (F.map (Limits.Sigma.isoColimit X).hom ≫ F.map (colim.map f)) := by
    rw [he']
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (Limits.Sigma.isoColimit X).hom) _

/-- Good truncations give a uniform window `[m-c,m]` and four natural cohomological
comparison isomorphisms, without any boundedness assumption on the input family.

Source: blueprint sec-six-functors-basics, sk-prop-ctf-finite-proper-localizing.proof.md,
Étale statements and Transfer; Stacks Tags 07D9 and 08J5.
(blueprint: lem-sfb-amplitude-truncation-family-comparison)

Proof: Grothendieck coproducts are exact, and the source library proves that derived
cohomology preserves them. Its truncation lemmas show that U = truncLE m K and
V = truncGE (m-c) U retain P-cohomology, with V in the asserted interval. For the
triangle U → K → truncGT m K, apply G: the last term is ≥ m+1, so the long exact
cohomology sequence makes the degree-m first arrow invertible. For the triangle
truncLE (m-c-1) U → U → V, the first term has P-cohomology, and its image under G
is ≤ m-1, so the degree-m second arrow is invertible. Apply the same arguments to
the coproducts of these distinguished triangles; their outer terms retain the
required bounds and P-cohomology. This proves the two comparisons with the sum
inside G, without commuting truncation with coproducts. Preservation of coproducts
by cohomology proves the two comparisons with the sum after G. Finally the
canonical coproduct-to-colimit isomorphisms identify these maps with the displayed
natural transformation components. This includes the empty family and uses no
bound on the original K, nor extension closure of P. -/
theorem amplitude_truncation_family_comparison
    (A : Type uA) [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] (hPzero : P 0)
    (hPsum : ∀ (J : Type w) (X : J → A), (∀ j, P (X j)) → P (∐ X))
    (G : DerivedCategory A ⥤ DerivedCategory B) [G.CommShift ℤ] [G.IsTriangulated]
    (c : ℕ)
    (hGge : ∀ (L : DerivedCategory A) (a : ℤ), L.IsGE a → (G.obj L).IsGE a)
    (hGle : ∀ (L : DerivedCategory A) (b : ℤ), L.IsLE b →
      (∀ j : ℤ, P ((homologyFunctor A j).obj L)) → (G.obj L).IsLE (b + (c : ℤ)))
    (I : Type w) (K : Discrete I ⥤ DerivedCategory A)
    (hK : ∀ (s : I) (j : ℤ), P ((homologyFunctor A j).obj (K.obj ⟨s⟩))) (m : ℤ) :
    (∀ s : I,
      ((TStructure.t.truncGE (m - (c : ℤ))).obj
        ((TStructure.t.truncLE m).obj (K.obj ⟨s⟩))).IsGE (m - (c : ℤ)) ∧
      ((TStructure.t.truncGE (m - (c : ℤ))).obj
        ((TStructure.t.truncLE m).obj (K.obj ⟨s⟩))).IsLE m ∧
      ∀ j : ℤ, P ((homologyFunctor A j).obj
        ((TStructure.t.truncGE (m - (c : ℤ))).obj
          ((TStructure.t.truncLE m).obj (K.obj ⟨s⟩))))) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory A)).map
        (TStructure.t.truncLEι m)) (colim ⋙ G ⋙ homologyFunctor B m)).app K) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory A)).map
        (whiskerLeft (TStructure.t.truncLE m) (TStructure.t.truncGEπ (m - (c : ℤ)))))
      (colim ⋙ G ⋙ homologyFunctor B m)).app K) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory B)).map
        (whiskerRight (TStructure.t.truncLEι m) G))
      (colim ⋙ homologyFunctor B m)).app K) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory B)).map
        (whiskerRight
          (whiskerLeft (TStructure.t.truncLE m) (TStructure.t.truncGEπ (m - (c : ℤ)))) G))
      (colim ⋙ homologyFunctor B m)).app K) := by
  classical
  let : P.ContainsZero := ⟨0, isZero_zero _, hPzero⟩
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  let : Abelian.HasKInjectiveResolutions B :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  let M (s : I) := K.obj ⟨s⟩
  let U (s : I) := (TStructure.t.truncLE m).obj (M s)
  let V (s : I) := (TStructure.t.truncGE (m - (c : ℤ))).obj (U s)
  let u (s : I) : U s ⟶ M s := (TStructure.t.truncLEι m).app (M s)
  let v (s : I) : U s ⟶ V s := (TStructure.t.truncGEπ (m - (c : ℤ))).app (U s)
  have hU (s : I) : homologyProperty P (U s) := homologyProperty_truncLE (hK s) m
  have hV (s : I) : homologyProperty P (V s) :=
    homologyProperty_truncGE (hU s) (m - (c : ℤ))
  have hsum (X : I → DerivedCategory A) (hX : ∀ i, homologyProperty P (X i)) :
      homologyProperty P (∐ X) := by
    intro j
    exact P.prop_of_iso (asIso (sigmaComparison (homologyFunctor A j) X))
      (hPsum I _ (fun i ↦ hX i j))
  have stepA (T : Triangle (DerivedCategory A))
      (hT : T ∈ distTriang _)
      (h₃ : T.obj₃.IsGE (m + 1)) :
      IsIso ((homologyFunctor B m).map (G.map T.mor₁)) := by
    have hG := hGge T.obj₃ (m + 1) h₃
    exact isIso_homologyMap_mor₁ _ (G.map_distinguished _ hT) (m - 1) m (by omega)
      (isZero_of_isGE _ (m + 1) _ (by omega) (hX := hG))
      (isZero_of_isGE _ (m + 1) _ (by omega) (hX := hG))
  have stepB (T : Triangle (DerivedCategory A))
      (hT : T ∈ distTriang _)
      (h₁ : T.obj₁.IsLE (m - (c : ℤ) - 1)) (hP : homologyProperty P T.obj₁) :
      IsIso ((homologyFunctor B m).map (G.map T.mor₂)) := by
    have hG := hGle T.obj₁ (m - (c : ℤ) - 1) h₁ hP
    exact isIso_homologyMap_mor₂ _ (G.map_distinguished _ hT) m (m + 1) rfl
      (isZero_of_isLE _ (m - (c : ℤ) - 1 + (c : ℤ)) _ (by omega) (hX := hG))
      (isZero_of_isLE _ (m - (c : ℤ) - 1 + (c : ℤ)) _ (by omega) (hX := hG))
  let TA (s : I) := (TStructure.t.triangleLEGT m).obj (M s)
  have hTA (s : I) : TA s ∈ distTriang _ :=
    TStructure.t.triangleLEGT_distinguished m (M s)
  let TB (s : I) := (TStructure.t.triangleLEGE (m - (c : ℤ) - 1)
    (m - (c : ℤ)) (by omega)).obj (U s)
  have hTB (s : I) : TB s ∈ distTriang _ :=
    TStructure.t.triangleLEGE_distinguished _ _ (by omega) (U s)
  have hA (s : I) : IsIso ((homologyFunctor B m).map (G.map (u s))) :=
    stepA (TA s) (hTA s) (inferInstanceAs
      (TStructure.t.IsGE ((TStructure.t.truncGT m).obj (M s)) (m + 1)))
  have hB (s : I) : IsIso ((homologyFunctor B m).map (G.map (v s))) :=
    stepB (TB s) (hTB s) (inferInstanceAs
      (TStructure.t.IsLE ((TStructure.t.truncLE (m - (c : ℤ) - 1)).obj (U s)) _))
      (homologyProperty_truncLE (hU s) _)
  have hAsum : IsIso ((homologyFunctor B m).map (G.map (Limits.Sigma.map u))) :=
    stepA (coproductTriangle TA)
      (coproductTriangle_distinguished TA hTA)
      (isGE_sigma _ (m + 1) (fun s ↦ inferInstanceAs
        (TStructure.t.IsGE ((TStructure.t.truncGT m).obj (M s)) (m + 1))))
  have hBsum : IsIso ((homologyFunctor B m).map (G.map (Limits.Sigma.map v))) :=
    stepB (coproductTriangle TB)
      (coproductTriangle_distinguished TB hTB)
      (isLE_sigma _ (m - (c : ℤ) - 1) (fun s ↦ inferInstanceAs
        (TStructure.t.IsLE ((TStructure.t.truncLE (m - (c : ℤ) - 1)).obj (U s)) _)))
      (hsum _ (fun s ↦ homologyProperty_truncLE (hU s) _))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨inferInstanceAs (TStructure.t.IsGE (V s) (m - (c : ℤ))),
      inferInstanceAs (TStructure.t.IsLE (V s) m), hV s⟩
  · exact isIso_map_colimMap_of_sigmaMap (G ⋙ homologyFunctor B m)
      (whiskerLeft K (TStructure.t.truncLEι m)) hAsum
  · exact isIso_map_colimMap_of_sigmaMap (G ⋙ homologyFunctor B m)
      (whiskerLeft K (whiskerLeft (TStructure.t.truncLE m)
        (TStructure.t.truncGEπ (m - (c : ℤ))))) hBsum
  · exact isIso_map_colimMap_of_sigmaMap (homologyFunctor B m)
      (whiskerLeft K (whiskerRight (TStructure.t.truncLEι m) G))
      (isIso_homologyFunctor_map_sigmaMap _ m hA)
  · exact isIso_map_colimMap_of_sigmaMap (homologyFunctor B m)
      (whiskerLeft K (whiskerRight (whiskerLeft (TStructure.t.truncLE m)
        (TStructure.t.truncGEπ (m - (c : ℤ)))) G))
      (isIso_homologyFunctor_map_sigmaMap _ m hB)

end DerivedCategory
