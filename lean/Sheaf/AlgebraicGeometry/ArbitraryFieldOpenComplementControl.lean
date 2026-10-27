module

public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionAbelianDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Ordinary etale open-complement control over arbitrary fields

Source: current blueprint, sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation,
closed-immersion paragraph; Stacks Project, Tag 0F10, lemma-finite-cd (1).
(blueprint: lem-pur-etale-arbitrary-field-open-complement-control)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact open immersion into a finite-type scheme over any field has
uniformly bounded higher direct images of all coefficient module sheaves and preserves
constructibility in every integer degree. Every uniform field-extension dimension bound
`d` gives the same constant `2 * d` in the ordinary etale open-complement condition.

Source: current blueprint, sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation,
closed-immersion paragraph; Stacks Project, Tag 0F10, lemma-finite-cd (1).
(blueprint: lem-pur-etale-arbitrary-field-open-complement-control)

Proof:
1. By lem-weil-pbc-qc-open-immersion-finite-type, j is finite type. Composition
   (lem-sfb-finite-type-composition-base-change) makes j followed by aT finite type.
   Apply lem-kun-uniform-field-extension-dimension-bound to this composite to obtain
   the first conjunct, allowing empty schemes. Then fix any d satisfying this bound.
2. Every section of the underlying abelian sheaf of an A-module sheaf M is killed
   by N, since (N : A) = 0. It is therefore torsion. Apply
   lem-kun-torsion-abelian-direct-image-dimension-bound to j and the two structure
   morphisms to get vanishing above 2d. The isomorphism of
   lem-sbc-higher-direct-image-forget-comparison identifies this with the underlying
   abelian sheaf of the module higher direct image. The forgetful functor reflects
   zero objects, giving vanishing for every M, without constructibility.
3. A constructible sheaf F in degree zero is bounded constructible. Apply
   thm-dg-finite-type-constructibility to j with coefficients A, using positivity of
   N, its invertibility in k and (N : A) = 0. Each integer cohomology sheaf of the
   resulting bounded constructible direct image is constructible, including negative
   degrees. These are precisely the higher direct images of F.
4. Steps 2 and 3 are the two clauses of def-exc-open-complement-bound at c = 2d.
   No separable-closedness or absolute cohomological-dimension assumption on k is
   used. When W is empty its module sheaves are zero, and empty T forces empty W.
-/
theorem exists_uniform_dimension_bound_and_hasOpenComplementCondition
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 1 ≤ N) (hunit : IsUnit (N : k)) (hkill : (N : A) = 0)
    {W T : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    (∃ d : ℕ, ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k))
      {P : Scheme.{u}} (p₁ : P ⟶ W) (p₂ : P ⟶ Spec (.of L)),
      IsPullback p₁ p₂ (j ≫ aT) s → topologicalKrullDim P ≤ (d : WithBot ℕ∞)) ∧
    (∀ d : ℕ,
      (∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k))
        {P : Scheme.{u}} (p₁ : P ⟶ W) (p₂ : P ⟶ Spec (.of L)),
        IsPullback p₁ p₂ (j ≫ aT) s → topologicalKrullDim P ≤ (d : WithBot ℕ∞)) →
      HasOpenComplementCondition A j (2 * d)) := by
  refine ⟨exists_topologicalKrullDim_le_of_isPullback (j ≫ aT), ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · intro M q hq
    let U := sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    let M' := (sheafCompose W.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M
    have hM : M'.IsTorsion := by
      apply Sheaf.IsTorsion.of_forall_isAddTorsion
      intro V m
      apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      refine ⟨N, by omega, ?_⟩
      change M.obj.obj V at m
      change N • m = 0
      rw [← Nat.cast_smul_eq_nsmul A, hkill, zero_smul]
    have hz := Etale.isZero_torsion_higherDirectImage_of_forall_field_dimension_le
      (j ≫ aT) aT j rfl d hd M' hM q (by simpa using hq)
    obtain ⟨e⟩ := Etale.nonempty_higherDirectImage_forget_iso A j q M
    have hU : IsZero (U.obj (Etale.higherDirectImage A j q M)) := hz.of_iso e
    change IsZero (Etale.higherDirectImage A j q M)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply U.map_injective
    exact hU.eq_of_src _ _
  · intro F q hF
    have hcoeff : Etale.IsSmoothBaseChangeCoefficients N A (Spec (.of k)) := by
      refine ⟨by omega, inferInstance, hkill, ?_⟩
      simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
    have : IsConstructibleSheaf F :=
      (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
    have hsingle : Etale.DerivedCategory.isBoundedConstructible A W
        ((DerivedCategory.singleFunctor _ 0).obj F) := by
      refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
        ((Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F 0).2 i),
        0, 0, le_rfl, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    have hc := (Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
      k A N hcoeff (j ≫ aT) aT j rfl _ hsingle).1 q
    have : IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) :=
      (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hc
    have hcc : IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj
          (((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor).obj
            (DerivedCategory.Plus.ι.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := this
    apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    exact IsConstructibleSheaf.of_iso
      (F := (DerivedCategory.homologyFunctor _ q).obj
        (((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor).obj
          (DerivedCategory.Plus.ι.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm

end AlgebraicGeometry.Scheme
