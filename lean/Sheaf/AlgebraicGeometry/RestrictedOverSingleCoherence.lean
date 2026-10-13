/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology

/-! # Coherence of restricted fixed-coefficient single complexes

Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of fixed coefficients.
(blueprint: lem-sbc-restricted-over-single-coherence).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Actual fibre products and their canonical transition arrows.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-single-coherence). -/
@[implicit_reducible]
noncomputable def restrictedOverDiagram {W S : Scheme.{u}} (k : W ⟶ S)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (U : S.Etale) :
    I ⥤ Scheme.{u} where
  obj i := pullback U.hom ((D.obj i).hom ≫ k)
  map f := rawAffineRestrictedMap (D.map f).left ((D.obj _).hom ≫ k)
    ((D.obj _).hom ≫ k) (by rw [← Category.assoc, Over.w]) U
  map_id i := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap]
  map_comp f g := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap, Category.assoc]

/-- The fibre-product cone, constructed without choosing a limit witness.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-single-coherence). -/
@[implicit_reducible]
noncomputable def restrictedOverCone {W S : Scheme.{u}} (k : W ⟶ S)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Cone (restrictedOverDiagram k D U) where
  pt := pullback U.hom (c.pt.hom ≫ k)
  π :=
    { app := fun i ↦ rawAffineRestrictedMap (c.π.app i).left ((D.obj i).hom ≫ k)
        (c.pt.hom ≫ k) (by rw [← Category.assoc, Over.w]; rfl) U
      naturality := by
        intro i j f
        apply pullback.hom_ext <;>
          simp [restrictedOverDiagram, rawAffineRestrictedMap, Category.assoc,
            ← Over.comp_left, c.w f] }

/-- A fixed sheaf restricted to an actual fibre product, placed in degree zero.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-single-coherence). -/
@[implicit_reducible]
noncomputable def restrictedOverSingle {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (A : Over W) (U : S.Etale) :=
  (CochainComplex.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (A.hom ≫ k))).obj
      ((upperStar AddCommGrpCat.{u + 1} A.hom).obj F))

/-- The explicit isomorphism for a triangle, including the single-functor comparison.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-single-coherence). -/
noncomputable def restrictedOverSingleIso {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    ((upperStar AddCommGrpCat.{u + 1}
      (rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictedOverSingle k F B U) ≅
      restrictedOverSingle k F A U := by
  let w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k := by rw [← Category.assoc, Over.w]
  let a := rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k) w U
  let r := pullback.snd U.hom (B.hom ≫ k)
  let r' := pullback.snd U.hom (A.hom ≫ k)
  let R := (upperStar AddCommGrpCat.{u + 1} B.hom).obj F
  have hw : r' ≫ f.left = a ≫ r := by simp [a, r, r', rawAffineRestrictedMap]
  let e := ((upperStar AddCommGrpCat.{u + 1} a).mapCochainComplexSingleFunctor 0).app
    ((upperStar AddCommGrpCat.{u + 1} r).obj R) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso
      (((upperStarComp AddCommGrpCat.{u + 1} a r).app R).symm ≪≫
        (upperStarComp AddCommGrpCat.{u + 1} r' f.left (a ≫ r) hw.symm).app R ≪≫
        (upperStar AddCommGrpCat.{u + 1} r').mapIso
          (((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).app F).symm))
  -- Expose the canonical hom directly, avoiding repeated normalization of mapIso.
  -- Its inverse is uniquely determined by the proved IsIso instance.
  let h := ((upperStar AddCommGrpCat.{u + 1} a).mapCochainComplexSingleFunctor 0).hom.app
    ((upperStar AddCommGrpCat.{u + 1} r).obj R) ≫
    (CochainComplex.singleFunctor _ 0).map
      (rawAffineRestrictedCoefficient f.left (B.hom ≫ k) (A.hom ≫ k) w
        R ((upperStar AddCommGrpCat.{u + 1} A.hom).obj F)
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app F) U)
  have : IsIso h := by
    change IsIso e.hom
    infer_instance
  exact asIso h

/-- The constant complex on the limiting fibre product.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-single-coherence). -/
@[implicit_reducible]
noncomputable def restrictedOverSingleG {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :=
  (Functor.const Iᵒᵖ).obj (restrictedOverSingle k F c.pt U)

/-- The cone comparison is the inverse of the explicitly constructed leg isomorphism.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-single-coherence). -/
@[implicit_reducible]
noncomputable def restrictedOverSingleConeIso {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale)
    (i : I) :=
  (restrictedOverSingleIso k F (c.π.app i) U).symm

/-- Identity, composition, and constant-diagram coherence of the explicit single complexes.
Source: Stacks Project, Tag 09Z1, affine-object restriction in lemma-relative-colimit;
Tag 0EZM, fixed-coefficient complexes in lemma-colimit-variant-complexes.
(blueprint: lem-sbc-restricted-over-single-coherence).

Proof: Substitute the equality identifying D and the heterogeneous equalities
identifying c, K, phi, G, and eG with the displayed concrete constructions.
Write r_A for the second projection U times_S A to A. For each arrow f,
expand the coefficient comparison as the inverse comparison for a_f and r_B,
the comparison for r_A and f.left, and r_A inverse image of the inverse comparison
for f.left and B.hom. These compare the two iterated inverse images of the same
fixed sheaf F. The identity comparison is the inverse-image unit law. For two
arrows, inverse-image associativity identifies their composite with the comparison
for the composite arrow; naturality moves the comparisons through the coefficient
maps and cancels each hom with its inverse. Apply the single-complex functor and
its natural comparison with inverse image to obtain the displayed identity and
composition equations. For the cone equation, substitute the cone relation
c_j followed by D(f) equals c_i into this composition equation. The comparison
for c_i cancels its inverse, leaving the identity map on the fixed apex complex.
This proof needs neither a limit hypothesis nor affineness, boundedness,
cohomology, or a cohomology continuity theorem. Empty schemes and zero sheaves
obey the same functorial identities. -/
theorem restrictedOverSingle_coherence {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D₀ : I ⥤ Over W) (c₀ : Cone D₀) (U : S.Etale)
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (K : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (_hD : D = restrictedOverDiagram k D₀ U)
    (_hc : HEq c (restrictedOverCone k D₀ c₀ U))
    (_hK : HEq K (fun i ↦ restrictedOverSingle k F (D₀.obj i) U))
    (_hφ : HEq @φ
      (fun {i j : I} (f : j ⟶ i) ↦ (restrictedOverSingleIso k F (D₀.map f) U).hom))
    (_hG : HEq G (restrictedOverSingleG k F D₀ c₀ U))
    (_heG : HEq eG (restrictedOverSingleConeIso k F D₀ c₀ U)) :
    (∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (K i)) ∧
    (∀ (i j l : I) (f : j ⟶ i) (g : l ⟶ j), φ (g ≫ f) =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
          (D.map (g ≫ f)) (D.map_comp g f)) (ComplexShape.up ℤ)).hom.app (K i) ≫
      ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : j ⟶ i),
      G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv) := by sorry

end AlgebraicGeometry.Etale
