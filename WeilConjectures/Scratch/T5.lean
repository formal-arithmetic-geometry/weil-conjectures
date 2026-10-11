module

public import WeilConjectures.Scratch.T4

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

open scoped ProEtale

/-- The comparison `j₀! F ⟶ j₀* F` on the underlying sheaves, with target `j̄_* F`. -/
noncomputable abbrev extensionByZeroToDirectImageSheaf (F : WeilSheaf k₀ l U) :
    ((extensionByZero j).obj F).obj.carrier.X ⟶ (j̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X :=
  (ProEtale.AdicSheaf.forget _).map ((extensionByZeroToDirectImage j).app F).hom.hom.f

set_option profiler true in
/-- On the underlying sheaves, the pullback along `j̄` of the comparison `j₀! F ⟶ j₀* F` is
invertible: its transpose under `j̄_! ⊣ j̄^*` is the inverse of the counit of `j̄^* ⊣ j̄_*`. -/
instance isIso_upperStar_map_extensionByZeroToDirectImageSheaf (F : WeilSheaf k₀ l U) :
    IsIso ((j̄)^*[WeilCoefficients.{u} l].map (extensionByZeroToDirectImageSheaf j F)) := by
  have h := ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    (j̄) F.obj.carrier
  have : IsIso ((j̄)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l (j̄)).app F.obj.carrier)) := by
    have : IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l (j̄)).unit.app F.obj.carrier ≫
        (j̄)^*ᵃ[l].map ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l (j̄)).app
          F.obj.carrier)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.adicOpenImmersionLowerShriekAdjunction l (j̄)).unit.app F.obj.carrier) _
  exact (inferInstance : IsIso ((ProEtale.AdicSheaf.forget _).map ((j̄)^*ᵃ[l].map
    ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l (j̄)).app F.obj.carrier))))

omit [Finite k₀] in
/-- The cardinality of the residue field at a closed point is `q ^ deg`. -/
private lemma natCard_residueField_eq_pow {Y : Scheme.{u}} (f : Y.Hom (Spec (.of k₀))) {y : Y}
    (hy : y ∈ Y.finitePoints) : Nat.card (Y.residueField y) = Nat.card k₀ ^ f.degreeOver y := by
  let := (f.residueFieldAlgebraMap y).toAlgebra
  have : Finite (Y.residueField y) := hy
  have : Module.Finite k₀ (Y.residueField y) := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] in
/-- An open immersion preserves the degrees of the closed points. -/
lemma degreeOver_base_eq (z : U.finitePoints) :
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver (j.base z.1) =
      (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
  have hx := Scheme.Hom.map_mem_finitePoints j z.2
  have e : Nat.card (X.residueField (j.base z.1)) = Nat.card (U.residueField z.1) :=
    Nat.card_congr (asIso (j.residueFieldMap z.1)).commRingCatIsoToRingEquiv.toEquiv
  have hj : j ≫ (X ↘ Spec (CommRingCat.of k₀)) = U ↘ Spec (CommRingCat.of k₀) :=
    comp_over j _
  rw [natCard_residueField_eq_pow (X ↘ Spec (CommRingCat.of k₀)) hx,
    natCard_residueField_eq_pow (U ↘ Spec (CommRingCat.of k₀)) z.2] at e
  exact Nat.pow_right_injective (Finite.one_lt_card (α := k₀)) e

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
set_option profiler true in
/-- The comparison `j₀! F ⟶ j₀* F` is compatible with the Weil structures on the underlying
sheaves. -/
lemma map_extensionByZeroToDirectImageSheaf_comp_frobeniusStr (F : WeilSheaf k₀ l U) :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map
      (extensionByZeroToDirectImageSheaf j F) ≫ ((lowerStar j).obj F).frobeniusStr =
      ((extensionByZero j).obj F).frobeniusStr ≫ extensionByZeroToDirectImageSheaf j F :=
  map_comp_frobeniusStr ((extensionByZeroToDirectImage j).app F)

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
set_option profiler true in
/-- The map `j̄^* j₀! F ⟶ j̄^* j̄_* F ⟶ F` is compatible with the Weil structures. -/
lemma extensionByZero_stalk_compatible (F : WeilSheaf k₀ l U) :
    (ProEtale.upperStarComp _ (U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
      (j̄)).hom.app ((extensionByZero j).obj F).obj.carrier.X ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map
          ((j̄)^*[_].map (extensionByZeroToDirectImageSheaf j F) ≫
            (ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X) ≫
        F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          j (comp_over j (Spec (CommRingCat.of k₀)))).symm).hom.app
          ((extensionByZero j).obj F).obj.carrier.X ≫
        (ProEtale.upperStarComp _ (j̄)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app
          ((extensionByZero j).obj F).obj.carrier.X ≫
        (j̄)^*[_].map ((extensionByZero j).obj F).frobeniusStr ≫
        ((j̄)^*[_].map (extensionByZeroToDirectImageSheaf j F) ≫
            (ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X) := by
  rw [map_comp_lowerStar_counit_frobeniusStr_compatible j _
    (map_extensionByZeroToDirectImageSheaf_comp_frobeniusStr j F)]

set_option profiler true in
/-- At a closed point of `U`, the local Frobenius of `j₀! F` has the characteristic polynomial
of the local Frobenius of `F`: through the comparison `j₀! F ⟶ j₀* F` and the counit of
`j̄^* ⊣ j̄_*`, the geometric stalks agree with their Frobenius. -/
theorem charpoly_frobeniusEnd_stalk_extensionByZero (F : WeilSheaf k₀ l U) (z : U.finitePoints) :
    (((extensionByZero j).obj F).stalk
      ⟨j.base z.1, Scheme.Hom.map_mem_finitePoints j z.2⟩).frobeniusEnd.charpoly =
      (F.stalk z).frobeniusEnd.charpoly := by
  set G := (extensionByZero j).obj F
  set x : X.finitePoints := ⟨j.base z.1, Scheme.Hom.map_mem_finitePoints j z.2⟩
  have hdeg := degreeOver_base_eq (k₀ := k₀) j z
  set s := (U ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (U ↘ Spec (CommRingCat.of k₀)) z
  have ht' : (s ≫ j̄) ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).hom =
      (specGeometricFrobenius k₀ ^ (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).hom ≫
        (s ≫ j̄) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have := isIso_upperStar_map_extensionByZeroToDirectImageSheaf j F
  obtain ⟨e₁⟩ := nonempty_equiv_stalkAt_of_upperStar (φ := j) (F := G) (G := F)
    (θ := (j̄)^*[_].map (extensionByZeroToDirectImageSheaf j F) ≫
      (ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X)
    (extensionByZero_stalk_compatible j F)
    s _ ht ht'
  have hbase : (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x
  have hss' : (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ j̄) ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg j.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hc' := G.charpoly_frobeniusEnd_stalkAt_of_dvd _ _ hss' (hbase ▸ x.2) (hdeg ▸ dvd_rfl)
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ x) ht'
  have hpos : 0 < (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 :=
    Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ z.2)
  have hr : (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 = 1 := by
    rw [show x.1 = j.base z.1 from rfl, hdeg, Nat.div_self hpos]
  rw [hr, pow_one] at hc'
  exact hc'.symm.trans e₁.charpoly_frobeniusEnd.symm

end WeilSheaf

end AlgebraicGeometry
