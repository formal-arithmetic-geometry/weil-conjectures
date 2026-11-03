/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence

/-!
# Scalar extension of integration and its actual adjoint transpose

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, final sentence
(blueprint: lem-pur-integration-transpose-scalar-mate).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Etale
namespace IntegrationScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {X Y : Scheme.{u}}

/-- The orientation-twisted pullback object G₀(K).
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-scalar-mate). -/
def object (f : X ⟶ Y) (W : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) : DerivedCategoryModule A X :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj W

/-- Integration is inverse projection, then tensoring the trace, then the right unitor.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-scalar-mate). -/
def integration {f : X ⟶ Y} (c : Compactification f)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactScalarProjection A c K W))
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (object f W K) ⟶ K :=
  @inv _ _ _ _ (compactScalarProjection A c K W) (hP K) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map t ≫
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- The actual adjoint transpose of integration, for the specified adjunction.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-scalar-mate). -/
def gamma {f : X ⟶ Y} (c : Compactification f)
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactScalarProjection A c K W))
    (K : DerivedCategoryModule A Y) : object f W K ⟶ R.obj K :=
  adj.homEquiv _ _ (integration c W t hP K)

/-- The specified scalar tensor/pullback comparison followed by the orientation map.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-scalar-mate). -/
def comparison (φ : A →+* B) (f : X ⟶ Y)
    (W : DerivedCategoryModule A X) (W' : DerivedCategoryModule B X)
    (l : (scalarExtension φ X).obj W ≅ W') (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj (object f W K) ⟶
      object f W' ((scalarExtension φ Y).obj K) :=
  compactScalarProjectionTarget φ f K W ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).map l.hom

/-- The actual counit mate b, using the canonical inverse of the proper/open scalar map.
The published comparisonInverse is the inverse on its isomorphism domain, which contains
every input here by compactScalarMap_coherence, including right-adjoint unit inputs.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-scalar-mate). -/
def mate (φ : A →+* B) {f : X ⟶ Y} (c : Compactification f)
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (R' : DerivedCategoryModule B Y ⥤ DerivedCategoryModule B X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ R')
    (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj (R.obj K) ⟶ R'.obj ((scalarExtension φ Y).obj K) :=
  adj'.homEquiv _ _ (ExceptionalCoefficients.comparisonInverse φ c (R.obj K) ≫
    (scalarExtension φ Y).map (adj.counit.app K))

private theorem projection_naturality (S : Type (u + 1)) [CommRing S]
    {f : X ⟶ Y} (c : Compactification f) (K : DerivedCategoryModule S Y)
    {M N : DerivedCategoryModule S X} (a : M ⟶ N) :
    ((derivedTensor (ModuleCat.{u + 1} S) Y).obj K).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} S) c).map a) ≫
        compactScalarProjection S c K N =
      compactScalarProjection S c K M ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} S) c).map
          (((derivedTensor (ModuleCat.{u + 1} S) X).obj
            ((upperStar (ModuleCat.{u + 1} S) f).leftDerivedFunctor.obj K)).map a) := by
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} S) c
  let L := (upperStar (ModuleCat.{u + 1} S) f).leftDerivedFunctor
  let T := derivedTensor (ModuleCat.{u + 1} S) Y
  let U := derivedTensor (ModuleCat.{u + 1} S) X
  have hY := ((derivedTensorSymmetry (ModuleCat.{u + 1} S) Y).hom.app K).naturality
    (F.map a)
  have hP := NatTrans.congr_app
    ((projectionMapOfCompactification (ModuleCat.{u + 1} S) c).naturality a) K
  have hX := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat.{u + 1} S) X).hom.naturality a) (L.obj K)
  change (T.obj K).map (F.map a) ≫ _ = _ ≫ (T.map (F.map a)).app K at hY
  change (T.map (F.map a)).app K ≫ _ =
    _ ≫ F.map ((U.map a).app (L.obj K)) at hP
  change (U.map a).app (L.obj K) ≫ _ = _ ≫ (U.obj (L.obj K)).map a at hX
  dsimp only [compactScalarProjection]
  rw [← Category.assoc, hY, Category.assoc, ← Category.assoc
    ((T.map (F.map a)).app K), hP]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ ((derivedTensorSymmetry (ModuleCat.{u + 1} S) Y).hom.app K).app (F.obj M) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} S) c).app M).app K ≫ F.map z) hX

set_option backward.isDefEq.respectTransparency false in
/-- Integration commutes with the specified scalar map, and its actual adjoint transpose
commutes with the counit mate. Invertible gamma components consequently make b invertible.
The quantifier includes the coefficient unit, with its normalized multiplication map.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2, final sentence
(blueprint: lem-pur-integration-transpose-scalar-mate).
Proof: (1) use the all-input projection square of
lem-pur-etale-compact-scalar-coherence, displaying the normalized tensor and pullback maps.
(2) Apply naturality of the primed projection in W along l. (3) Postcompose with primed
integration, insert the trace equation, and use naturality and the ordinary-balancing unit
normalization of def-pur-exceptional-coefficient-normalizations. Cancel the invertible
projection and scalar maps to obtain the first equality. (4) Expand the counit definition
of the mate as in def-weil-pbc-adjunction-mate and use naturality of q at gamma. The inverse
transpose of the left side of the second equality is the left side of the first equality.
(5) The inverse transpose of the other side is its right side. Injectivity of the actual
adjunction Hom equivalence proves equality. (6) Conjugate by the two invertible gammas and
the scalar tensor/pullback orientation isomorphism to prove invertibility of b. All inputs
are unbounded; substitute the coefficient unit and use the normalized unit identifications.
This uses neither flatness nor preservation of arbitrary isomorphisms by mates. -/
theorem integrationTransposeScalarMate
    [Finite A] [Finite B] (φ : A →+* B)
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (R' : DerivedCategoryModule B Y ⥤ DerivedCategoryModule B X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ R')
    (W : DerivedCategoryModule A X) (W' : DerivedCategoryModule B X)
    (l : (scalarExtension φ X).obj W ≅ W')
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (t' : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj W' ⟶
      𝟙_ (DerivedCategoryModule B Y))
    (ht : (compactScalarMap φ c).app W ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map l.hom ≫ t' =
      (scalarExtension φ Y).map t ≫ (ExceptionalCoefficients.unitIso φ Y).hom)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactScalarProjection A c K W))
    (hP' : ∀ L : DerivedCategoryModule B Y, IsIso (compactScalarProjection B c L W'))
    (K : DerivedCategoryModule A Y) :
    (ExceptionalCoefficients.comparisonInverse φ c (object f W K) ≫
        (scalarExtension φ Y).map (integration c W t hP K) =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (comparison φ f W W' l K) ≫
        integration c W' t' hP' ((scalarExtension φ Y).obj K)) ∧
    ((scalarExtension φ X).map (gamma c R adj W t hP K) ≫ mate φ c R R' adj adj' K =
      comparison φ f W W' l K ≫
        gamma c R' adj' W' t' hP' ((scalarExtension φ Y).obj K)) ∧
    (IsIso (gamma c R adj W t hP K) →
      IsIso (gamma c R' adj' W' t' hP' ((scalarExtension φ Y).obj K)) →
      IsIso (mate φ c R R' adj adj' K)) := by
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let F' := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let Q := scalarExtension φ Y
  let QX := scalarExtension φ X
  let T := (derivedTensor (ModuleCat.{u + 1} A) Y).obj K
  let T' := (derivedTensor (ModuleCat.{u + 1} B) Y).obj (Q.obj K)
  let P := compactScalarProjection A c K W
  let P' := compactScalarProjection B c (Q.obj K) W'
  let q := compactScalarMap φ c
  let δ := ExceptionalCoefficients.tensorIso φ Y
  have hc := compactScalarMap_coherence φ f c
  have (M : DerivedCategoryModule A X) : IsIso (q.app M) := hc.1 M
  have : IsIso P := hP K
  have : IsIso P' := hP' (Q.obj K)
  have hinv (M : DerivedCategoryModule A X) :
      ExceptionalCoefficients.comparisonInverse φ c M = inv (q.app M) := by
    dsimp only [ExceptionalCoefficients.comparisonInverse]
    have h : IsIso (ExceptionalCoefficients.compactSupportMap φ c M) := hc.1 M
    rw [dif_pos h]
    rfl
  have hn := projection_naturality B c (Q.obj K) l.hom
  have hproj : Q.map P ≫ q.app (object f W K) ≫
      F'.map (comparison φ f W W' l K) =
      δ.hom.app (K, F.obj W) ≫ T'.map (q.app W ≫ F'.map l.hom) ≫ P' := by
    have hs := hc.2.1 K W
    change Q.map P ≫ q.app (object f W K) ≫
      F'.map (compactScalarProjectionTarget φ f K W) =
      δ.hom.app (K, F.obj W) ≫ T'.map (q.app W) ≫
        compactScalarProjection B c (Q.obj K) (QX.obj W) at hs
    dsimp only [comparison]
    rw [F'.map_comp]
    calc
      _ = (δ.hom.app (K, F.obj W) ≫ T'.map (q.app W) ≫
          compactScalarProjection B c (Q.obj K) (QX.obj W)) ≫
          F'.map (((derivedTensor (ModuleCat.{u + 1} B) X).obj
            ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
              (Q.obj K))).map l.hom) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ F'.map (((derivedTensor (ModuleCat.{u + 1} B) X).obj
            ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
              (Q.obj K))).map l.hom)) hs
      _ = _ := by
        simp only [Category.assoc, Functor.map_comp]
        rw [← hn]
  have hδ := δ.hom.naturality (show (K, F.obj W) ⟶ (K, 𝟙_ _) from (𝟙 K, t))
  have hδ' : Q.map (T.map t) ≫ δ.hom.app (K, 𝟙_ _) =
      δ.hom.app (K, F.obj W) ≫ T'.map (Q.map t) := by
    change Q.map (((derivedTensor (ModuleCat.{u + 1} A) Y).map (𝟙 K)).app
        (F.obj W) ≫ T.map t) ≫ δ.hom.app (K, 𝟙_ _) =
      δ.hom.app (K, F.obj W) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) Y).map (Q.map (𝟙 K))).app (Q.obj (F.obj W)) ≫
          T'.map (Q.map t) at hδ
    simp only [_root_.CategoryTheory.Functor.map_id, NatTrans.id_app] at hδ
    change Q.map (𝟙 (T.obj (F.obj W)) ≫ T.map t) ≫ δ.hom.app (K, 𝟙_ _) =
      δ.hom.app (K, F.obj W) ≫ 𝟙 (T'.obj (Q.obj (F.obj W))) ≫ T'.map (Q.map t) at hδ
    rw [Category.id_comp] at hδ
    erw [Category.id_comp] at hδ
    exact hδ
  have hu := ExceptionalCoefficients.tensorIso_right_unit φ Y
  have hu' : δ.hom.app (K, 𝟙_ _) ≫ T'.map (ExceptionalCoefficients.unitIso φ Y).hom ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} B) Y (Q.obj K)).hom =
      Q.map (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom := hu K
  have hi : ExceptionalCoefficients.comparisonInverse φ c (object f W K) ≫
      Q.map (integration c W t hP K) =
      F'.map (comparison φ f W W' l K) ≫
        integration c W' t' hP' (Q.obj K) := by
    rw [hinv]
    apply (cancel_epi (q.app (object f W K))).1
    apply (cancel_epi (Q.map P)).1
    simp only [IsIso.hom_inv_id_assoc]
    have hp := congrArg (fun z ↦ z ≫ integration c W' t' hP' (Q.obj K)) hproj
    simp only [Category.assoc] at hp
    rw [hp]
    simp only [integration, Functor.map_comp, Category.assoc]
    rw [← Category.assoc P', IsIso.hom_inv_id, Category.id_comp]
    change Q.map P ≫ Q.map (inv P) ≫ Q.map (T.map t) ≫ _ =
      δ.hom.app (K, F.obj W) ≫ T'.map (q.app W) ≫
        T'.map (F'.map l.hom) ≫ T'.map t' ≫ _
    rw [← T'.map_comp_assoc, ← T'.map_comp_assoc, Category.assoc, ht, T'.map_comp_assoc]
    rw [← Category.assoc (δ.hom.app (K, F.obj W)), ← hδ', Category.assoc, hu']
    simp only [← Q.map_comp, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  let hg := gamma c R adj W t hP K
  have hnat : F'.map (QX.map hg) ≫ inv (q.app (R.obj K)) =
      inv (q.app (object f W K)) ≫ Q.map (F.map hg) := by
    apply (cancel_epi (q.app (object f W K))).1
    have hnq := q.naturality hg
    change Q.map (F.map hg) ≫ q.app (R.obj K) =
      q.app (object f W K) ≫ F'.map (QX.map hg) at hnq
    rw [← Category.assoc, ← hnq, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  have hm : QX.map (gamma c R adj W t hP K) ≫ mate φ c R R' adj adj' K =
      comparison φ f W W' l K ≫ gamma c R' adj' W' t' hP' (Q.obj K) := by
    unfold mate
    rw [← adj'.homEquiv_naturality_left]
    change (adj'.homEquiv _ _)
      (F'.map (QX.map hg) ≫ ExceptionalCoefficients.comparisonInverse φ c (R.obj K) ≫
        Q.map (adj.counit.app K)) = _
    rw [hinv, ← Category.assoc, hnat, Category.assoc, ← Q.map_comp]
    have he : F.map hg ≫ adj.counit.app K =
        integration c W t hP K := (adj.homEquiv _ _).symm_apply_apply _
    rw [he, ← hinv, hi]
    exact adj'.homEquiv_naturality_left _ _
  refine ⟨hi, hm, ?_⟩
  intro hγ hγ'
  have := hγ
  have := hγ'
  have ha : IsIso (comparison φ f W W' l K) := by
    dsimp only [comparison, compactScalarProjectionTarget]
    infer_instance
  have hb : mate φ c R R' adj adj' K =
      inv (QX.map (gamma c R adj W t hP K)) ≫
        comparison φ f W W' l K ≫ gamma c R' adj' W' t' hP' (Q.obj K) := by
    rw [← hm, IsIso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

end IntegrationScalar
end AlgebraicGeometry.Etale
