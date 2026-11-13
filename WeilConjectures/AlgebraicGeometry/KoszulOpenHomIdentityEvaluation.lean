/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
import WeilConjectures.AlgebraicGeometry.KoszulOpenStructureEvaluation
import WeilConjectures.AlgebraicGeometry.KoszulOpenAugmentedIdentityClass
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit

/-! # Natural evaluation normalized on the Koszul identity

Source: Stacks Project, Tags 08DC, 08DD, 08D1 and 09M1.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
-- Nested derived restriction functors require extra elaboration heartbeats.
/-- Natural evaluation, normalized only on the identity of each Koszul tail.
Source: Stacks Project, Tags 09M1, 08DC, 08DD and 08D1.
Proof: Identify the restricted extended tilde of A[0] with O_U[0]. Evaluation
at one on a K-injective representative identifies maps from this object with
zeroth derived global sections; the comparison with affineOpenSections restricts
scalars to A and gives the equivalences b. Evaluation and the comparison commute
with postcomposition by every derived arrow. For the identity of I_e, restrict
the tail augmentation to U. On D(f_j), exterior multiplication by the j-th basis
vector divided by f_j^(e+1) contracts the full Koszul complex, giving its inverse.
On an intersection indexed by J the iterated contractions evaluate on the ordered
wedge and divide by the product of the f_j to exponent e+1. Converting the Hom
and alternating Cech differentials multiplies the row by
(-1)^(pq+p(p-1)/2), with p=card(J)-1 and q=-p, exactly as in Tag 08D1.
Thus the explicit cocone sends the identity cycle to the Cech class of this
inverse. The Cech comparison computes derived sections and gives the equality.
The augmentation is invertible, so any left inverse v is this inverse. If the
cover is empty, restriction and sections vanish and both classes are zero;
the same construction covers the zero ring. No target F or chain map into F
occurs in this normalization. -/
theorem koszulOpenHom_identity_evaluation
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    ∃ b : ∀ E : schemeDerivedCategory (Spec (.of A)),
      (R.obj (koszulOpenStructure A) ⟶ R.obj E) ≃ H.obj (G.obj E),
      (∀ (E E' : schemeDerivedCategory (Spec (.of A))) (g : E ⟶ E')
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E),
        b E' (ψ ≫ R.map g) = H.map (G.map g) (b E ψ)) ∧
      ∀ (e : ℕ) (v : R.obj (koszulOpenStructure A) ⟶
          R.obj (koszulOpenObject A r f e)),
        R.map (koszulOpenUnit A r f e) ≫ v = 𝟙 _ →
        b (koszulOpenObject A r f e) v =
          H.map (koszulCechDerivedComparison A r f (koszulOpenSheafComplex A r f e))
            (H.map (DerivedCategory.Q.map (colimit.ι
              (koszulCechHomDiagram A r f
                (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj
                  (koszulOpenSheafComplex A r f e))) e))
              (koszulOpenHomStageClass A r f (koszulOpenSheafComplex A r f e) e (𝟙 _)))
      := by
  classical
  dsimp only
  let F₀ := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)
  let G₀ := Equivalence.functor
    (C := SheafOfModules.{u}
      ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
    (D := SheafOfModules.{u}
      (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (koszulOpen A r f))
  let R := (F₀ ⋙ G₀).mapDerivedCategory
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  let c := fun e : ℕ ↦ H.map (koszulCechDerivedComparison A r f (koszulOpenSheafComplex A r f e))
      (H.map (DerivedCategory.Q.map (colimit.ι
        (koszulCechHomDiagram A r f
        (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj
          (koszulOpenSheafComplex A r f e))) e))
        (koszulOpenHomStageClass A r f (koszulOpenSheafComplex A r f e) e (𝟙 _)))
  obtain ⟨b, hb, h₀⟩ := koszulOpen_structure_evaluation.{u, w, v} A r f
  refine ⟨b, hb, ?_⟩
  intro e v hv
  change R.map (koszulOpenUnit A r f e) ≫ v = 𝟙 _ at hv
  have hi : IsIso (F₀.mapDerivedCategory.map (koszulOpenUnit A r f e)) := by
    have h := (affine_perfect_koszul_principal_unit A r f (e + 1)
      (Nat.le_add_left 1 e)).2
    have hU : (⨆ i : Fin r, (Spec (.of A)).basicOpen
        ((Scheme.ΓSpecIso (.of A)).inv (f i))) = koszulOpen A r f := by
      unfold koszulOpen
      congr 1
      funext i
      exact basicOpen_eq_of_affine (R := .of A) (f i)
    rw [hU] at h
    exact h
  have hiso : IsIso (R.map (koszulOpenUnit A r f e)) := by
    apply (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso F₀ G₀) _).1
    change IsIso (G₀.mapDerivedCategory.map
      (F₀.mapDerivedCategory.map (koszulOpenUnit A r f e)))
    infer_instance
  let z := (b (koszulOpenObject A r f e)).symm (c e)
  have hz : b (koszulOpenObject A r f e) z = c e := Equiv.apply_symm_apply _ _
  have hclass := koszulOpen_augmented_identity_class.{u, w, v} A r f e
  have hright : z ≫ R.map (koszulOpenUnit A r f e) = 𝟙 _ := by
    apply (b (koszulOpenStructure A)).injective
    rw [hb, hz, hclass, h₀]
  have hvright : v ≫ R.map (koszulOpenUnit A r f e) = 𝟙 _ := by
    apply (cancel_epi (R.map (koszulOpenUnit A r f e))).mp
    rw [← Category.assoc, hv, Category.id_comp, Category.comp_id]
  have hvz : v = z := by
    apply (cancel_mono (R.map (koszulOpenUnit A r f e))).mp
    rw [hvright, hright]
  change b (koszulOpenObject A r f e) v = c e
  rw [hvz, hz]


end AlgebraicGeometry
