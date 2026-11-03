module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModulePullbackExact

/-! # Exact condensed module pullback and Frobenius mate compatibility

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, paragraphs 1--2
(blueprint: lem-sf-native-adic-pullback-frobenius-mates).

The statement uses the actual condensed coefficient module functors and the canonical
composition and congruence comparisons.  The Frobenius pushforward comparison is required
to be the adjunction mate of the inverse pullback comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pushforward along an isomorphism, with the canonical identity/composition words.
Source: lem-fix-weil-operations.proof.md, automorphism-square paragraph
(blueprint: lem-sf-native-adic-pullback-frobenius-mates). -/
def frobeniusMateLowerEquivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (a : X ≅ Y) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ≌
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  CategoryTheory.Equivalence.mk (lowerStar Λ a.hom) (lowerStar Λ a.inv)
    ((lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ a.hom_inv_id.symm ≪≫
      (lowerStarComp Λ a.hom a.inv).symm)
    (lowerStarComp Λ a.inv a.hom ≪≫ lowerStarCongr Λ a.inv_hom_id ≪≫ lowerStarId Λ Y)

/-- The specified identification by uniqueness of left adjoints to the same pushforward.
Source: lem-fix-weil-operations.proof.md, ordinary adjunction paragraph
(blueprint: lem-sf-native-adic-pullback-frobenius-mates). -/
def frobeniusMateUpperIsoLowerInv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (a : X ≅ Y) :
    upperStar Λ a.hom ≅ lowerStar Λ a.inv :=
  (upperStarLowerStarAdjunction Λ a.hom).leftAdjointUniq
    (frobeniusMateLowerEquivalence Λ a).symm.toAdjunction

/-- The geometric base-change map commutes with both Frobenius automorphisms.
Source: lem-fix-weil-operations.proof.md, pullback square, node proof step 1
(blueprint: lem-sf-native-adic-pullback-frobenius-mates).
Proof: the two composites have first projection f₀ and second projection inverse field
Frobenius, hence agree by pullback uniqueness. Compose with the inverse automorphisms
on both sides to get the inverse-square equation. -/
theorem frobeniusMateGeometricSquares
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    let J := ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
    let a := D.geometricFrobenius X₀
    let c := D.geometricFrobenius Y₀
    (J ≫ c.hom = a.hom ≫ J) ∧ (J ≫ c.inv = a.inv ≫ J) := by
  sorry

/-- Exact condensed module pullback and Frobenius mate compatibility.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, paragraphs 1--2
(blueprint: lem-sf-native-adic-pullback-frobenius-mates).

Proof plan, following the six steps of the DAG:
1. `def-weil-finite-field-fiber` and `def-weil-frobenius-detailed` give the commuting
   squares: both projections agree, as stated in `frobeniusMateGeometricSquares`.
2. `det-def-sfb-module-pushforward-pullback` supplies the actual extension/restriction
   functors and scalar actions. `det-prop-sfb-module-pullback-exact-main` gives finite
   limit/colimit preservation and additivity; `def-sfb-module-lower-star` gives R additive.
3. `def-sfb-module-lower-star-comp` and identity/congruence give the inverse equivalences.
   Their triangle identities hold on sections, since the composite restrictions are
   identities. Faithfulness of forgetting module structure gives equality of module maps.
   `def-weil-pbc-adjunction-conjugate` identifies the two left adjoints of F_* by the
   conjugate of its identity, exactly `frobeniusMateUpperIsoLowerInv`.
4. Expand e inverse. Under the composite adjunctions, its endpoint identifications
   conjugate to identities; its middle factors conjugate to the direct-image word
   C : R F_X* -> F_Y* R by `def-sfb-module-upper-star-comp`. Congruence is substitution,
   and `lem-weil-pbc-mate-pasting` identifies the whiskered factors.
5. On underlying abelian sheaves `lem-sf-proetale-pushforward-unit-compositor` says
   C_(P_X M) after R of the inverse-equivalence unit equals F_Y* of b_M after the target
   unit. The module compositors forget to these section restriction maps, including
   coefficient actions. Injectivity of the adjunction Hom bijection identifies the
   second mate of b with C, by `def-weil-pbc-adjunction-mate`.
6. `lem-trf-iterated-square-mates` identifies the second mate of e inverse with the
   same C. Injectivity of mates gives b as the first mate. Its component formula is
   exactly the unit--comparison--counit formula of `CategoryTheory.mateEquiv`.
-/
theorem nativeAdicPullbackFrobeniusMates
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated X₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    let Λ := Profinite.padicAlgClRingObj l
    let X := (D.geometricFiber X₀).left
    let J := ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left
    let F_X := D.geometricFrobenius X₀
    let F_Y := D.geometricFrobenius Y₀
    let L := (J)^*⟦Λ⟧
    let R := (J)_*⟦Λ⟧
    let P_X := (F_X.inv)_*⟦Λ⟧
    let P_Y := (F_Y.inv)_*⟦Λ⟧
    let e : L ⋙ P_X ≅ P_Y ⋙ L :=
      Functor.isoWhiskerLeft L (frobeniusMateUpperIsoLowerInv Λ F_X).symm ≪≫
        (upperStarComp Λ F_X.hom J).symm ≪≫
        upperStarCongr Λ (frobeniusMateGeometricSquares D f₀).1.symm ≪≫
        upperStarComp Λ J F_Y.hom ≪≫
        Functor.isoWhiskerRight (frobeniusMateUpperIsoLowerInv Λ F_Y) L
    let b : R ⋙ P_Y ≅ P_X ⋙ R :=
      lowerStarComp Λ J F_Y.inv ≪≫
        lowerStarCongr Λ (frobeniusMateGeometricSquares D f₀).2 ≪≫
        (lowerStarComp Λ F_X.inv J).symm
    PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧ L.Additive ∧ R.Additive ∧
      P_X.IsEquivalence ∧ P_Y.IsEquivalence ∧ P_X.Additive ∧ P_Y.Additive ∧
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
        b.hom.app M =
          (upperStarLowerStarAdjunction Λ J).unit.app (P_Y.obj (R.obj M)) ≫
            R.map (e.inv.app (R.obj M)) ≫
            R.map (P_X.map ((upperStarLowerStarAdjunction Λ J).counit.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
