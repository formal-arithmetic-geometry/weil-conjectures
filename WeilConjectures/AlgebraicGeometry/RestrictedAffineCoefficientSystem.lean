/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleCoherence
/-! # Base change and the restricted coefficient complex system

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

-- The existential proof witnesses record required properties even though the final
-- morphism equality does not refer to them. Keep the original binder names.
set_option linter.unusedVariables false in
/-- Construct the base-changed schemes and their degree-zero coefficient complexes,
including the coefficient colimit and its restriction comparisons. -/
theorem exists_restricted_affine_coefficient_system {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left] :
    ∃
    (D' : Iᵒᵖ ⥤ Scheme.{v})
    (c' : Cone D')
    (hc : IsLimit c')
    (compact : ∀ i : Iᵒᵖ, CompactSpace (D'.obj i))
    (quasiSeparated : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D'.obj i))
    (affine : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f))
    (K : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (D'.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (hbelow : ∀ (i : Iᵒᵖ) (n : ℤ), n < 0 → IsZero ((K i).X n))
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (hbelowL : ∀ n : ℤ, n < 0 → IsZero (L.pt.X n))
    (r : ∀ i : Iᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U ≅
        (cohomology AddCommGrpCat.{v + 1} (D'.obj i) (p : ℤ)).obj
          (DerivedCategory.Q.obj (K i)))
    (rL : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅
      (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).obj
        (DerivedCategory.Q.obj L.pt)),
    ∀ i : Iᵒᵖ,
      (r i).hom ≫ rawAffineComplexPullback (p : ℤ) (c'.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))) =
      rawAffineRestrictedCohomologyMap (c.π.app (op i.unop)).left
        (D.obj (op i.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop))) p
        (F i.unop) (colimit H) ((eH i.unop).inv ≫ colimit.ι H i.unop) U ≫ rL.hom := by
  let D' := restrictedAffineDiagram D U
  let c' := restrictedAffineCone D c U
  let K := restrictedAffineK D F U
  let G := restrictedAffineG D c H U
  let L := restrictedAffineL D c H U
  obtain ⟨ψ, hidentity, hcomposition, eG, hG, hcoeff⟩ :=
    exists_restricted_affine_single_coherence D c F φ hφid hφcomp H eH hH U
      D' c' K G L rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
  refine ⟨D', c', restrictedAffineConeIsLimit D c hc U,
    restrictedAffineDiagram_compact D U, restrictedAffineDiagram_quasiSeparated D U,
    fun _ _ f ↦ restrictedAffineDiagram_affine D U f,
    K, @ψ, hidentity, hcomposition, ?_, G, eG, hG, L,
    restrictedAffineLIsColimit D c H U, ?_, fun _ ↦ Iso.refl _, Iso.refl _, ?_⟩
  · intro i n hn
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
        (F i.unop)) n (ne_of_lt hn)
  · intro n hn
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom c.pt.hom)).obj
        (colimit H)) n (ne_of_lt hn)
  · intro i
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rw [eq_of_heq (hcoeff i)]
    rfl

end AlgebraicGeometry.Etale
