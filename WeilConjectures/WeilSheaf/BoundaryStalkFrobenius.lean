/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DirectImageStalk
public import WeilConjectures.WeilSheaf.StalkTransportGeneral

/-!
# The Frobenius of boundary stalks of direct images through a neighbourhood

Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of `k₀`-schemes, `F` a Weil sheaf on `U₀`
and `G = j_* F`. Let `h : Spec A ⟶ C̄` be a morphism with a point `c` over a geometric point `s`
of `C̄`, `α` an endomorphism of `Spec A` lifting `Frᵐ` (`α ≫ h = h ≫ Frᵐ`) with
`σᵐ ≫ c = c ≫ α`, and `ε : Spec Ω ⟶ Spec A` a point over a point `η` of `Ū` (`ε ≫ h = η ≫ j̄`)
with an endomorphism `a` of `Spec Ω` such that `a ≫ η = η ≫ Frᵐ` and `a ≫ ε = ε ≫ α`.

Then:

* the restriction `Γ(Spec A, h^* G) ⟶ G_s` along `c` intertwines the transport along `α` and the
  Weil structure `φ_m` with the Frobenius of the stalk
  (`AlgebraicGeometry.WeilSheaf.resOver_stalkAt_frobenius`);
* the restriction to `Spec Ω` along `ε` followed by the counit `j̄^* j̄_* F ⟶ F`,
  `Γ(Spec A, h^* G) ⟶ Γ(Spec Ω, (η ≫ j̄)^* G) ⟶ Γ(Spec Ω, η^* F)`
  (`AlgebraicGeometry.WeilSheaf.genericSpecialization`), intertwines the transport along `α` with
  the transport along `a ≫ η = η ≫ Frᵐ` and the Weil structure of `F`
  (`AlgebraicGeometry.WeilSheaf.genericSpecialization_frobenius`).

For a strictly henselian neighbourhood of a boundary point and `a` the residue Frobenius lift,
this is the Frobenius equivariance of blueprint `lem-wf-boundary-stalk-invariants`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

/-- Category algebra for the compatibility of the counit: a morphism `i ≫ θ` built from a
morphism `i` compatible with structure maps and a morphism `θ` compatible with structure maps. -/
lemma comp_map_comp_eq_of_compatible {𝒞 : Type*} [Category 𝒞] (T : 𝒞 ⥤ 𝒞) {W Z Z' M N F' : 𝒞}
    (u : W ⟶ T.obj M) (v : W ⟶ Z') (w : Z' ⟶ Z) (ψ' : Z ⟶ M) (i : M ⟶ N) (θ : N ⟶ F')
    (ψN : T.obj N ⟶ N) (ψF : T.obj F' ⟶ F') (hc : u ≫ T.map i ≫ ψN = v ≫ w ≫ ψ' ≫ i)
    (hn : T.map θ ≫ ψF = ψN ≫ θ) :
    u ≫ T.map (i ≫ θ) ≫ ψF = v ≫ w ≫ ψ' ≫ i ≫ θ := by
  rw [T.map_comp, Category.assoc, hn, reassoc_of% hc]

/-- The counit `j̄^* j̄_* F ⟶ F` of the underlying sheaves, as a morphism out of the underlying
sheaf of the Weil sheaf `j^* j_* F`. -/
noncomputable abbrev directImageCounit :
    ((upperStar j).obj ((directImage j).obj F)).obj.carrier.X ⟶ F.obj.carrier.X :=
  ((upperStarLowerStarAdjunction j).counit.app F).hom.hom.f.hom

/-- The counit `j̄^* j̄_* F ⟶ F`, out of `j̄^*` of the underlying sheaf of `j_* F`. -/
noncomputable abbrev directImageCounit' :
    (j̄)^*[WeilCoefficients.{u} l].obj ((directImage j).obj F).obj.carrier.X ⟶ F.obj.carrier.X :=
  (𝟙 _ : (j̄)^*[_].obj ((directImage j).obj F).obj.carrier.X ⟶
    ((upperStar j).obj ((directImage j).obj F)).obj.carrier.X) ≫ directImageCounit j F

set_option maxHeartbeats 4000000 in
-- unifying the Weil structures of `j^* j_* F` and of the source of the counit is slow
/-- The counit `j^* j_* F ⟶ F` commutes with the Weil structures. -/
lemma directImageCounit_naturality :
    ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
        (directImageCounit j F) ≫ F.frobeniusStr =
      ((upperStar j).obj ((directImage j).obj F)).frobeniusStr ≫ directImageCounit j F :=
  frobeniusStr_naturality ((upperStarLowerStarAdjunction j).counit.app F)

set_option maxHeartbeats 4000000 in
-- unifying the underlying sheaves of `j^* j_* F` and `j̄^* j̄_* F` is slow
/-- The counit `j̄^* j̄_* F ⟶ F` is compatible with the Weil structures. -/
lemma directImageCounit_frobeniusStr_compatible :
    (ProEtale.upperStarComp _ (U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
      (j̄)).hom.app ((directImage j).obj F).obj.carrier.X ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map
          (directImageCounit' j F) ≫ F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          j (comp_over j (Spec (CommRingCat.of k₀)))).symm).hom.app
          ((directImage j).obj F).obj.carrier.X ≫
        (ProEtale.upperStarComp _ (j̄)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app
          ((directImage j).obj F).obj.carrier.X ≫
        (j̄)^*[_].map ((directImage j).obj F).frobeniusStr ≫ directImageCounit' j F :=
  comp_map_comp_eq_of_compatible _ _ _ _ _ _ _ _ _
    (upperStar_frobeniusStr_compatible j ((directImage j).obj F))
    (directImageCounit_naturality j F)

end AlgebraicGeometry.WeilSheaf
