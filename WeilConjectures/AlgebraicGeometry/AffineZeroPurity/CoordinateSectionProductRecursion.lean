/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductPresentations
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSupportedProductRecursion
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateAdjunctionComposition
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSupportedProductPullback
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateClosedSourceExchange
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductInterchange
import Mathlib.GroupTheory.Perm.Sign
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerDescent
import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint latest, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: lem-pur-coordinate-section-product-recursion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The ordinary etale witness of an actual arrow, obtained by the canonical
bounded-below comparison Hom bijection with its specified endpoint identifications.
Source: proof Step 9 (blueprint: lem-pur-coordinate-section-product-recursion). -/
@[irreducible]
def ordinaryWitness (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : DerivedCategory.TStructure.t.plus L)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (eK : (VectorIntegrationSite.comparison A X).obj K ≅ M)
    (eL : (VectorIntegrationSite.comparison A X).obj L ≅ N) (α : M ⟶ N) : K ⟶ L :=
  (Equiv.ofBijective
    (fun f : K ⟶ L ↦ (VectorIntegrationSite.comparison A X).map f)
    (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL)).symm
      (eK.hom ≫ α ≫ eL.inv)

/-- Equality in every ordinary etale witness presentation of the specified parallel
arrows. All arrows are lifted by the exact comparison Hom bijection, including
compositions and their canonical projection and adjunction comparisons.
Source: proof Step 9 (blueprint: lem-pur-coordinate-section-product-recursion). -/
def OrdinaryWitnessEquation (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α β : M ⟶ N) : Prop :=
  ∀ (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : DerivedCategory.TStructure.t.plus L)
    (eK : (VectorIntegrationSite.comparison A X).obj K ≅ M)
    (eL : (VectorIntegrationSite.comparison A X).obj L ≅ N),
    ordinaryWitness A X hL eK eL α = ordinaryWitness A X hL eK eL β

/-- Exact comparison preserves the uniquely specified ordinary witness arrow,
with the given endpoint identifications. Source: proof Step 9
(blueprint: lem-pur-coordinate-section-product-recursion).
Proof: apply the defining inverse property of the bounded-below comparison Hom
bijection. For Cartier factors this is realizeBoundary; exact monoidality,
proper projection comparison and bounded adjunction transposition identify the
lifts of all cup products, projection components, counits and composition maps
with their ordinary etale constructions. No unbounded full faithfulness is used. -/
theorem ordinaryWitness_compare (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : DerivedCategory.TStructure.t.plus L)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (eK : (VectorIntegrationSite.comparison A X).obj K ≅ M)
    (eL : (VectorIntegrationSite.comparison A X).obj L ≅ N) (α : M ⟶ N) :
    (VectorIntegrationSite.comparison A X).map (ordinaryWitness A X hL eK eL α) =
      eK.hom ≫ α ≫ eL.inv := by
  unfold ordinaryWitness
  exact (Equiv.ofBijective
    (fun f : K ⟶ L ↦ (VectorIntegrationSite.comparison A X).map f)
    (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL)).apply_symm_apply _

private theorem compactProduct_adjunct (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
      (target_plus P n _ (towerBase aB c) c) (compactProduct P n B aB c) =
        thom P n B aB c := by
  let := tower_noetherian (setting P n) B aB c
  unfold compactProduct
  exact (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).apply_symm_apply _

set_option maxRecDepth 2048 in
/-- Rank-zero normalization and the two recursive identities for the actual maps.
Source: proof Steps 1--6 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: coordinate nonzerodivisors remain Cartier after adjoining or killing the
other coordinates. Pull back the first r factors. The cup coefficient map and
the proper projection at the supported coefficient unit both multiply restricted
sections, so agree, with the tensor symmetry. Naturality of projection at C_r
then gives the supported recursion. Transpose it: substitute both exceptional
counits, use their naturality, and paste them to the composite-adjunction counit.
Conjugating the compact-support compositor gives precisely the displayed
exceptional recursion. At zero, the empty product and identity adjunction give
the two identity formulas. All reordered shifts are even, with sign +1. -/
theorem coordinate_section_product_recursion (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    compactProduct P n B aB 0 = coordinateIdentity P n B ∧
    thom P n B aB 0 =
      coordinateIdentityAdjunct P n B aB ∧
    (∀ r : ℕ, compactProduct P n B aB (r + 1) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r) ∧
    ∀ r : ℕ, thom P n B aB (r + 1) =
      thom P n B aB r ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B r)).map (sectionAdjunct P n B aB r) ≫
        coordinateExceptionalComposition P n B aB r := by
  obtain ⟨h₀, hC⟩ := coordinate_supported_product_recursion P n B aB
  refine ⟨h₀, ?_, hC, ?_⟩
  · rw [← compactProduct_adjunct P n B aB 0, h₀]
    unfold coordinateIdentityAdjunct
    rfl
  · intro r
    let := isNoetherian_of_locallyOfFiniteType aB
    let := tower_noetherian (setting P n) B aB r
    let := tower_noetherian (setting P n) B aB (r + 1)
    rw [← compactProduct_adjunct P n B aB (r + 1), hC r]
    rw [coordinateAdjunction_composition P n B aB r,
      compactProduct_adjunct P n B aB r]


section CoordinateBaseChangeProof


private theorem transpose_composite
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (F : C ⥤ D) (G : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D') (R' : D' ⥤ C')
    {K R : C} {L : D} {K' : C'} {L' : D'}
    (s : K' ⟶ U.obj K) (θ : K ⟶ R) (m : U.obj R ⟶ R'.obj (V.obj L))
    (t : V.obj L ⟶ L') (ε : F.obj R ⟶ L)
    (ε₀ : G.obj (R'.obj (V.obj L)) ⟶ V.obj L)
    (ε₁ : G.obj (R'.obj L') ⟶ L')
    (eK : G.obj (U.obj K) ⟶ V.obj (F.obj K))
    (eR : G.obj (U.obj R) ⟶ V.obj (F.obj R))
    (a : F.obj K ⟶ L)
    (ha : F.map θ ≫ ε = a)
    (hm : G.map m ≫ ε₀ = eR ≫ V.map ε)
    (hn : G.map (U.map θ) ≫ eR = eK ≫ V.map (F.map θ))
    (ht : G.map (R'.map t) ≫ ε₁ = ε₀ ≫ t) :
    G.map (s ≫ U.map θ ≫ m ≫ R'.map t) ≫ ε₁ =
      G.map s ≫ eK ≫ V.map a ≫ t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ht, reassoc_of% hm, reassoc_of% hn, ← V.map_comp_assoc, ha]

private theorem pullback_comp
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (V : C ⥤ D) {K S T : C} {K' S' T' : D}
    (e : K ⟶ S) (a : S ⟶ T) (p : K' ⟶ V.obj K) (q : S' ⟶ V.obj S)
    (t : V.obj T ⟶ T') (e' : K' ⟶ S') (a' : S' ⟶ T')
    (he : p ≫ V.map e = e' ≫ q) (ha : q ≫ V.map a ≫ t = a') :
    p ≫ V.map (e ≫ a) ≫ t = e' ≫ a' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc p, he, Category.assoc, ha]

private theorem closedExchange_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    [HasCompactification i] [HasCompactification i'] (sq : IsPullback g i' i h)
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z K)
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z L) (f : K ⟶ L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i').map
        ((inverseImage A g).map f) ≫ (closedExchange A g i' i h sq L hL).inv =
      (closedExchange A g i' i h sq K hK).inv ≫
        (inverseImage A h).map ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).map f) := by
  let e : rightDerivedLowerShriek (ModuleCat.{u + 1} A) i ⋙ inverseImage A h ⟶
      inverseImage A g ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} A) i' :=
    Functor.whiskerRight
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) i).hom (inverseImage A h) ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq ≫
      Functor.whiskerLeft (inverseImage A g)
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) i').inv
  have hn := e.naturality f
  have hnh :
      (inverseImage A h).map ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).map f) ≫
          (closedExchange A g i' i h sq L hL).hom =
        (closedExchange A g i' i h sq K hK).hom ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i').map
            ((inverseImage A g).map f) := by
    simpa only [e, closedExchange, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.comp_map,
      Category.assoc] using hn
  apply (cancel_epi (closedExchange A g i' i h sq K hK).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hnh]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]


private theorem thom_transpose (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    let := zero_exact P n B aB c
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B c)).map (thom P n B aB c) ≫
        rightDerivedUpperShriekCounit (zero B c) _
          (target_plus P n _ (towerBase aB c) c) =
      (closedSingleIso (setting P n).Coefficient (zero B c)
        ((setting P n).constant B)).hom ≫ supportedClass P n B aB c := by
  let := tower_noetherian (setting P n) B aB c
  let := zero_exact P n B aB c
  unfold thom coordinateThomAdjunct
  change (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).symm
      ((rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
        (target_plus P n _ (towerBase aB c) c)) _) = _
  exact Equiv.symm_apply_apply _ _

private theorem coordinate_mate_transpose (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    let := tower_noetherian (setting P n) B' (g ≫ aB) c
    let := zero_exact P n B aB c
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B' c)).map
      ((unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (setting P n).Coefficient (zero B' c)).map
          (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom) ≫
      rightDerivedUpperShriekCounit (zero B' c) _
        (target_plus P n _ (towerBase (g ≫ aB) c) c) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B' c)).map (unitPullback P n g).inv ≫
        (closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
          (spaceMap g c) (zero_square g c) _ (unit_origin P n B)).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          ((closedSingleIso (setting P n).Coefficient (zero B c)
            ((setting P n).constant B)).hom ≫ supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom := by
  let := tower_noetherian (setting P n) B aB c
  let := tower_noetherian (setting P n) B' (g ≫ aB) c
  let := zero_exact P n B aB c
  let hM := pulledExceptional_origin P n g aB c
  let hT := pulledTarget_plus P n g aB c
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)
  let U := inverseImage (setting P n).Coefficient g
  let V := inverseImage (setting P n).Coefficient (spaceMap g c)
  let R' := rightDerivedUpperShriek (setting P n).Coefficient (zero B' c)
  let t := (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom
  let ε := rightDerivedUpperShriekCounit (zero B c) _
    (target_plus P n _ (towerBase aB c) c)
  let ε₀ := rightDerivedUpperShriekCounit (zero B' c) _ hT
  let ε₁ := rightDerivedUpperShriekCounit (zero B' c) _
    (target_plus P n _ (towerBase (g ≫ aB) c) c)
  let eK := closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) _ (unit_origin P n B)
  let eR := closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) _
      (plusEtaleOrigin_rightDerivedUpperShriek_obj (zero B c)
        (target_plus P n _ (towerBase aB c) c))
  have hm : G.map (coordinateExceptionalExchange P n g aB c) ≫ ε₀ =
      eR.inv ≫ V.map ε := by
    refine (rightDerivedUpperShriekHomEquiv_symm_apply (zero B' c) hM hT
      (coordinateExceptionalExchange P n g aB c)).symm.trans ?_
    unfold coordinateExceptionalExchange
    exact (rightDerivedUpperShriekHomEquiv (zero B' c) hM hT).symm_apply_apply _
  exact transpose_composite F G U V R' (unitPullback P n g).inv (thom P n B aB c)
    (coordinateExceptionalExchange P n g aB c) t ε ε₀ ε₁ eK.inv eR.inv
    ((closedSingleIso (setting P n).Coefficient (zero B c)
      ((setting P n).constant B)).hom ≫ supportedClass P n B aB c)
    (thom_transpose P n B aB c) hm
    (closedExchange_naturality (setting P n).Coefficient g (zero B' c) (zero B c)
      (spaceMap g c) (zero_square g c) (unit_origin P n B)
      (plusEtaleOrigin_rightDerivedUpperShriek_obj (zero B c)
        (target_plus P n _ (towerBase aB c) c)) (thom P n B aB c))
    (rightDerivedUpperShriekCounit_naturality (zero B' c) hT
      (target_plus P n _ (towerBase (g ≫ aB) c) c) t)


/-- Arbitrary base-change identities for the actual supported product and its
specified exceptional adjunct, with canonical source and Tate identifications.
Source: proof Steps 7--9 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: the first equality is coordinate_supported_product_pullback. For the
second, transpose both sides through the closed exceptional adjunction, whose
counit-composition map is bijective. The mate's defining counit equation,
naturality of inverse closed exchange and counit naturality turn the left
transpose into the pullback of closedSingleIso followed by the supported class.
coordinate_closed_source_exchange identifies the pulled-back source with
coordinateSourcePullback; the first equality then gives the primed supported
class, which is the transpose of the primed Thom map. Invertibility of the
exceptional mate is not used. -/
theorem coordinate_section_product_baseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    (coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      supportedClass P n B' (g ≫ aB) c ∧
    (unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B' c)).map
            (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      thom P n B' (g ≫ aB) c := by
  have hC := coordinate_supported_product_pullback P n g aB c
  refine ⟨hC, ?_⟩
  let := tower_noetherian (setting P n) B aB c
  let := tower_noetherian (setting P n) B' (g ≫ aB) c
  let := zero_exact P n B aB c
  let := zero_exact P n B' (g ≫ aB) c
  apply (bijective_rightDerivedLowerShriek_map_comp_counit (zero B' c)
    (unit_origin P n B') (target_plus P n _ (towerBase (g ≫ aB) c) c)).injective
  let V := inverseImage (setting P n).Coefficient (spaceMap g c)
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)
  let s := (unitPullback P n g).inv
  let eK := closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) _ (unit_origin P n B)
  let e := (closedSingleIso (setting P n).Coefficient (zero B c)
    ((setting P n).constant B)).hom
  let e' := (closedSingleIso (setting P n).Coefficient (zero B' c)
    ((setting P n).constant B')).hom
  let t := (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom
  have he : (G.map s ≫ eK.inv) ≫ V.map e =
      e' ≫ (coordinateSourcePullback P n g c).inv :=
    (Category.assoc (G.map s) eK.inv (V.map e)).trans
      (coordinate_closed_source_exchange P n g aB c)
  have hcomp := pullback_comp V e (supportedClass P n B aB c) (G.map s ≫ eK.inv)
    (coordinateSourcePullback P n g c).inv t e' (supportedClass P n B' (g ≫ aB) c) he hC
  have hθ : G.map (thom P n B' (g ≫ aB) c) ≫
      rightDerivedUpperShriekCounit (zero B' c) _
        (target_plus P n _ (towerBase (g ≫ aB) c) c) =
      e' ≫ supportedClass P n B' (g ≫ aB) c :=
    thom_transpose P n B' (g ≫ aB) c
  exact (coordinate_mate_transpose P n g aB c).trans
    ((Category.assoc (G.map s) eK.inv
      (V.map (e ≫ supportedClass P n B aB c) ≫ t)).symm.trans (hcomp.trans hθ.symm))

end CoordinateBaseChangeProof

private theorem normalized_product_eq (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (is : List (Fin c)) (his : is = List.finRange c)
    (e : support B c is ≅ B) (he : e.hom ≫ zero B c = supportMap B c is)
    (hLen : is.length = c) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((setting P n).functorialCupSupportMap true (zero B c) (supportMap B c is)
          e.hom he) ≫
      eqToHom (classSource_eq P n B c is).symm ≫ product P n B aB c is ≫
      eqToHom (congrArg (target P n (iteratedAffineLine B c)) hLen) =
        supportedClass P n B aB c := by
  subst is
  have heq : e = supportIso B c :=
    (supportIso_existsUnique B c).unique he
      (supportIso_existsUnique B c).exists.choose_spec
  subst e
  rfl

private theorem permutedClass_one (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    permutedClass P n B aB c 1 = supportedClass P n B aB c := by
  unfold permutedClass
  exact normalized_product_eq P n B aB c _ (by simp)
    (permutedSupportIso_existsUnique B c 1).exists.choose
    (permutedSupportIso_existsUnique B c 1).exists.choose_spec (by simp)


/-- Coordinate permutations preserve the actual map: every adjacent interchange
has Koszul sign (-1)^(2*2)=1. Source: proof Step 10
(blueprint: lem-pur-coordinate-section-product-recursion).
Proof: at the identity enumeration, uniqueness of the support identification
over the zero section gives supportedClass (permutedClass_one). Induct over
products of transpositions (Equiv.Perm.swap_induction_on). Each step exchanges
two labels by coordinate_product_interchange, whose factors have degree two,
so the sign is one. -/
theorem coordinate_section_product_permutation (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (σ : Equiv.Perm (Fin c)) :
    permutedClass P n B aB c σ = supportedClass P n B aB c := by
  refine Equiv.Perm.swap_induction_on σ (permutedClass_one P n B aB c) ?_
  intro τ i j hij hτ
  exact (coordinate_product_interchange P n B aB c τ i j hij).trans hτ

private theorem root_arrow_transport {C : Type*} [Category* C]
    {S L L' J : C} (α : S ⟶ L) (β : S ⟶ L') (e : L ≅ J) (e' : L' ≅ J)
    (h : α ≫ e.hom = β ≫ e'.hom) : α ≫ (e ≪≫ e'.symm).hom = β := by
  apply (cancel_mono e'.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using h

private theorem root_boundary_transport
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
    [HasDerivedCategory.{u + 1} D] [CategoryTheory.HasExt.{u + 1} C]
    [CategoryTheory.HasExt.{u + 1} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S L L' : C} {M J : D} (s : M ≅ F.obj S) (e : F.obj L ≅ J)
    (e' : F.obj L' ≅ J) (α : CategoryTheory.Abelian.Ext.{u + 1} S L 2)
    (β : CategoryTheory.Abelian.Ext.{u + 1} S L' 2)
    (h : (α.mapExactFunctor F : CategoryTheory.Abelian.Ext.{u + 1} _ _ 2).comp
        (CategoryTheory.Abelian.Ext.mk₀ e.hom) (Nat.add_zero 2) =
      (β.mapExactFunctor F : CategoryTheory.Abelian.Ext.{u + 1} _ _ 2).comp
        (CategoryTheory.Abelian.Ext.mk₀ e'.hom) (Nat.add_zero 2)) :
    let root {L : C} (e : F.obj L ≅ J) :
        F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧) ≅
          ((DerivedCategory.singleFunctor D 0).obj J)⟦(2 : ℤ)⟧ :=
      (F.mapDerivedCategory.commShiftIso (2 : ℤ)).app
          ((DerivedCategory.singleFunctor C 0).obj L) ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso
          ((F.mapDerivedCategorySingleFunctor 0).app L ≪≫
            (DerivedCategory.singleFunctor D 0).mapIso e)
    ((DerivedCategory.singleFunctor D 0).map s.hom ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫ F.mapDerivedCategory.map α.hom) ≫
        (root e ≪≫ (root e').symm).hom =
      (DerivedCategory.singleFunctor D 0).map s.hom ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫ F.mapDerivedCategory.map β.hom := by
  dsimp only
  apply root_arrow_transport
    (β := (DerivedCategory.singleFunctor D 0).map s.hom ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫ F.mapDerivedCategory.map β.hom)
  have hh := congrArg CategoryTheory.Abelian.Ext.hom h
  simp only [CategoryTheory.Abelian.Ext.comp_hom,
    CategoryTheory.Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    CategoryTheory.Abelian.Ext.mapExactFunctor_hom, ShiftedHom.map,
    Category.assoc] at hh
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Nat.cast_ofNat] using
      congrArg (fun f ↦ (DerivedCategory.singleFunctor D 0).map s.hom ≫ f) hh

attribute [local irreducible] comparisonUpperStar lowerStar

private theorem realized_root_transport (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {J : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)}
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L ≅ J)
    (e' : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj L' ≅ J)
    (α : CategoryTheory.Abelian.Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj M) L 2)
    (β : CategoryTheory.Abelian.Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj M) L' 2)
    (h : (α.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) X) :
        CategoryTheory.Abelian.Ext.{u + 1} _ _ 2).comp
        (CategoryTheory.Abelian.Ext.mk₀ e.hom) (Nat.add_zero 2) =
      (β.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) X) :
        CategoryTheory.Abelian.Ext.{u + 1} _ _ 2).comp
        (CategoryTheory.Abelian.Ext.mk₀ e'.hom) (Nat.add_zero 2)) :
    coordinateRealizeRootBoundary A j M L L' α e e' = realizeBoundary A j M L' β := by
  let := isIso_lowerStarComparisonUpperStarBaseChange j (ModuleCat.{u + 1} A)
  unfold coordinateRealizeRootBoundary coordinateArrowComparison coordinateIsoThrough
    realizeBoundary
  dsimp only
  exact root_boundary_transport (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (asIso ((lowerStarComparisonUpperStarBaseChange j
      (ModuleCat.{u + 1} A)).app M)).symm e e' α β h

set_option maxHeartbeats 1000000 in
-- Comparing simultaneous realization witnesses needs a larger elaboration budget.
/-- Exponent independence is equality of the factors used in the actual recursive
product, hence also of its adjuncts and the displayed identities.
Source: proof Step 10 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: the simultaneous Cartier realization at exponents r and n+1 gives two
source and two target comparisons. The source comparisons agree after the mapped
supported unit, which is epic, so they are equal. Uniqueness of root-normalized
site comparisons identifies both targets with coordinateRootComparison. Hence the
two Ext classes agree after exact comparison and the common Tate target; applying
Ext.hom, precomposing with the closed site exchange and cancelling the shifted
root comparison gives the stated equality of realized boundaries. -/
theorem coordinate_section_product_exponent (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) (i : Fin c) (r : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : (setting P n).Coefficient) = 0) :
    boundaryAtExponent P n B aB c i r hA = boundary P n B aB c i := by
  let l := P.coefficients.l
  let E := P.extension
  let X := iteratedAffineLine B c
  let j := inclusion B c i
  let hX := AffineLinePurity.primeUnit (setting P n) X (towerBase aB c)
  have hc := (Etale.cartier_kummer_map l E).2.exists.choose_spec.2.2.1
  rw [Etale.CartierKummerRealization] at hc
  obtain ⟨α, q, hq, hα, he⟩ := hc n r hA j (coordinate_cartier B c i) hX
  obtain ⟨α₀, q₀, hq₀, hα₀, he₀⟩ :=
    hc n (n + 1) (annihilates (setting P n)) j (coordinate_cartier B c i) hX
  have hroot (s : ℕ)
      (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
      (e : (comparisonUpperStar (ModuleCat.{u + 1}
          (Scheme.finiteTateCoefficient l E n)) X).obj
        (Scheme.finiteEtaleTateLine X (l ^ (s + 1)) _ hs) ≅
          Scheme.finiteTateProSheaf l E n X 1)
      (he : Scheme.IsFiniteTateSiteComparison l E n X s hs 1 e) :
      e = coordinateRootComparison l E n X hX s hs := by
    have hnorm : Scheme.IsFiniteTateSiteComparison l E n X s hs 1
        (VectorIntegrationSite.twistComparison l E n X hX s hs 1) := by
      unfold VectorIntegrationSite.twistComparison
      exact (Scheme.finite_tate_site_descent l E n).choose_spec.1 X hX s hs 1
    have heq := eq_of_heq
      (coordinateRootComparison_existsUnique l E n X hX s hs).exists.choose_spec
    exact ((adicPurityRootComparison_existsUnique l E n X hX s hs 1).unique
      he hnorm).trans heq.symm
  have hq' := hroot r hA q hq
  have hq₀' := hroot (n + 1) (annihilates (setting P n)) q₀ hq₀
  let := Etale.mapped_supported_unit_epi (Scheme.finiteTateCoefficient l E n) j
  have hα' : α.hom = α₀.hom := (cancel_epi _).mp (hα.trans hα₀.symm)
  have hαiso : α = α₀ := Iso.ext hα'
  have hnorm := he.symm.trans (by simpa only [hαiso] using he₀)
  rw [hq', hq₀'] at hnorm
  unfold boundaryAtExponent coordinateBoundaryRaw
  change coordinateRealizeRootBoundary _ _ _ _ _ _ _ _ = _
  unfold boundary ordinaryBoundary
  apply realized_root_transport
  simpa only [l, E, X, j, hX] using hnorm

/-- The same recursive equations in every bounded ordinary etale witness, with
exact comparison preserving the specified arrows. The witness of a Cartier
factor is ordinaryBoundary; witnesses of cup products, proper projection,
compositors and exceptional adjuncts use the comparison Hom bijection above.
Source: proof Steps 1--6 and 9 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: ordinary closed constants and Tate lines are bounded. Their actual
Cartier maps realize boundary. Exact monoidality identifies the iterated cups,
the closed exchanges and normalized Tate multiplication. Finite proper projection
comparison identifies sectionArrow. The bounded site adjunction-transpose theorem
identifies sectionAdjunct, the pasted counits, and the conjugate compositor.
Consequently both sides of every ordinary equation realize the corresponding
specified pro-etale side. Faithfulness gives these ordinary equalities. This
argument works in every endpoint presentation and assumes no unbounded comparison
adjunction or relative supported Kunneth isomorphism. -/
theorem coordinate_section_product_ordinary (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    OrdinaryWitnessEquation (setting P n).Coefficient B
      (compactProduct P n B aB 0) (coordinateIdentity P n B) ∧
    OrdinaryWitnessEquation (setting P n).Coefficient B
      (thom P n B aB 0) (coordinateIdentityAdjunct P n B aB) ∧
    (∀ r : ℕ, OrdinaryWitnessEquation (setting P n).Coefficient
      (iteratedAffineLine B (r + 1)) (compactProduct P n B aB (r + 1))
      ((coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r)) ∧
    ∀ r : ℕ, OrdinaryWitnessEquation (setting P n).Coefficient B
      (thom P n B aB (r + 1))
      (thom P n B aB r ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B r)).map (sectionAdjunct P n B aB r) ≫
        coordinateExceptionalComposition P n B aB r) := by
  obtain ⟨h₀, hθ₀, hC, hθ⟩ := coordinate_section_product_recursion P n B aB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K L hL eK eL
    rw [h₀]
  · intro K L hL eK eL
    rw [hθ₀]
  · intro r K L hL eK eL
    rw [hC r]
  · intro r K L hL eK eL
    rw [hθ r]

/-- Ordinary witnesses of arbitrary base change, with the same closed exchange
and the specified exceptional mate. Source: proof Steps 7--9
(blueprint: lem-pur-coordinate-section-product-recursion).
Proof: coordinate Cartier pullbacks stay Cartier without flatness. Ordinary
Cartier naturality and cup pullback give the supported identity. Transpose it
through the ordinary closed adjunction: the mate is pullback of the counit
following inverse closed exchange. The defining counit equation and naturality
give the exceptional identity. Exact comparison preserves every map in that
calculation, by closed exchange and bounded site adjunction transposition. -/
theorem coordinate_section_product_ordinary_baseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    OrdinaryWitnessEquation (setting P n).Coefficient (iteratedAffineLine B' c)
      ((coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom)
      (supportedClass P n B' (g ≫ aB) c) ∧
    OrdinaryWitnessEquation (setting P n).Coefficient B'
      ((unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (zero B' c)).map
            (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom)
      (thom P n B' (g ≫ aB) c) := by
  obtain ⟨hC, hθ⟩ := coordinate_section_product_baseChange P n g aB c
  constructor
  · intro K L hL eK eL
    rw [hC]
  · intro K L hL eK eL
    rw [hθ]

/-- Exponent and permutation independence also hold in every ordinary witness.
Source: proof Steps 9--10 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: Cartier exponent transitions fix every normalized factor. Exact comparison
identifies the ordinary factors and the cups with their realized maps. The
supported symmetry has sign (-1)^(2*2)=1; uniqueness of total-support transport
identifies the source comparison. Faithfulness yields both ordinary equalities. -/
theorem coordinate_section_product_ordinary_invariance (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    (∀ σ : Equiv.Perm (Fin c), OrdinaryWitnessEquation (setting P n).Coefficient
      (iteratedAffineLine B c) (permutedClass P n B aB c σ) (supportedClass P n B aB c)) ∧
    ∀ (i : Fin c) (r : ℕ)
      (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : (setting P n).Coefficient) = 0),
      OrdinaryWitnessEquation (setting P n).Coefficient (iteratedAffineLine B c)
        (boundaryAtExponent P n B aB c i r hA) (boundary P n B aB c i) := by
  constructor
  · intro σ K L hL eK eL
    rw [coordinate_section_product_permutation P n B aB c σ]
  · intro i r hA K L hL eK eL
    rw [coordinate_section_product_exponent P n B aB c i r hA]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
