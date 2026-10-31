/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.EtaleModuleStalkSpecialization
import WeilConjectures.AlgebraicGeometry.SmoothLocalAcyclicity
import WeilConjectures.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity
import WeilConjectures.AlgebraicGeometry.ProperLocallyAcyclicSpecialization
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleSpecializationAbelianIso

/-!
# Smooth proper specialization for general invertible finite coefficients

Source: current blueprint, `prop-zl-smooth-proper-relative-purity`, Step 1,
Local constancy at finite level; Stacks Project, Tag 0GKD.
(blueprint: lem-zl-finite-smooth-proper-specialization).

The coefficient category is the existing fixed-coefficient `ModuleCat` sheaf category.
The specialization map is the canonical map characterized on pointed neighbourhood germs.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Smooth proper specialization is an isomorphism for finite locally constant sheaves
of modules over any finite commutative ring annihilated by an integer invertible on the base.
Source: current blueprint, `prop-zl-smooth-proper-relative-purity`, Step 1,
Local constancy at finite level; Stacks Project, Tag 0GKD.
(blueprint: lem-zl-finite-smooth-proper-specialization).

Proof:
1. Forget scalars from F to an abelian sheaf G. On each member of a trivializing
etale cover, coefficient forgetting preserves sheafification, and Mathlib's constant-sheaf
composition instance makes the underlying abelian sheaf constant. Thus G is locally constant.
The equality (N : B) = 0 kills every section and every stalk of G,
so G is torsion. A unit N in each local ring of S maps to a unit in every residue field
of X. In positive residue characteristic p this implies p does not divide N. Since each
stalk element has additive order dividing N, its order is prime to p; characteristic
zero imposes no additional restriction.
2. Smooth local acyclicity gives universal local acyclicity of f, hence local acyclicity
by the identity base change. Neither a dimension bound nor a Noetherian base is used.
3. The locally constant torsion local acyclicity theorem applied to G gives local
acyclicity of f relative to G, using the stalkwise prime-to-characteristic condition.
4. Proper locally acyclic specialization applied to f and G in degree q shows that the
actual abelian restriction map on pointed neighbourhood germs is an isomorphism.
5. The canonical module/abelian derived direct-image comparison identifies the underlying
abelian sheaf of R^q f_* F with R^q f_* G: forgetting scalars is exact and commutes with
cohomology. The module-specialization abelian-iso theorem transfers invertibility of
abelian specialization to bijectivity of the germ-characterized module specialization.
This map is B-linear by construction from module stalk colimits. Its bijective inverse
is B-linear, since applying specialization reduces the scalar identity for the inverse
to linearity of specialization. Hence the displayed morphism is an isomorphism of modules.
-/
theorem isIso_etaleModuleStalkSpecialization_of_finite_smooth_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (N : ℕ) (hN : 0 < N) (hB : (N : B) = 0)
    (hunit : ∀ x : S, IsUnit (N : S.presheaf.stalk x))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    [Scheme.IsLocallyConstantSheaf F]
    (hfinite : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ X),
      Finite ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B) |>.obj F))
    (q : ℕ) {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (Scheme.etaleModuleStalkSpecialization s t
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  have _ := hfinite
  let U := forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}
  let G := (moduleAbelianForget B X).obj F
  have hkill (M : ModuleCat.{u + 1} B) (m : M) : N • m = 0 := by
    rw [← Nat.cast_smul_eq_nsmul B, hB, zero_smul]
  have : Scheme.IsLocallyConstantSheaf G := by
    obtain ⟨d⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    refine ⟨⟨⟨d.cover, fun i ↦ ?_⟩⟩⟩
    let := d.isConstant i
    have : GrothendieckTopology.PreservesSheafification
        (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)) U :=
      GrothendieckTopology.instPreservesSheafification _ _
    change ((sheafCompose (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
      U).obj (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
    infer_instance
  have hG : G.IsTorsion := by
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun V m ↦ ?_
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hN, hkill (F.obj.obj V) m⟩
  have hf : IsLocallyAcyclicRelative f G := by
    apply isLocallyAcyclicRelative_of_locallyConstant_torsion f (smooth_localAcyclicity f).2
    intro K _ _ x m
    have : PreservesFilteredColimitsOfSize.{u, u} U :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let e := ((Scheme.pointSmallEtale x).sheafFiberCompIso U).app F
    have hm : N • m = 0 := by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      simpa only [map_nsmul, map_zero] using
        hkill (((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B)).obj F)
          (e.hom m)
    refine ⟨isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hN, hm⟩, ?_⟩
    by_cases hc : ringChar (X.residueField (x default)) = 0
    · exact Or.inl hc
    · apply Or.inr
      have hu : IsUnit (N : X.residueField (x default)) := by
        simpa only [map_natCast] using
          (hunit (f (x default))).map
            ((X.residue (x default)).hom.comp (f.stalkMap (x default)).hom)
      have hp : N.Coprime (ringChar (X.residueField (x default))) := by
        apply Nat.Coprime.symm
        apply (CharP.char_prime_of_ne_zero (X.residueField (x default)) hc).coprime_iff_not_dvd.mpr
        exact fun h ↦ hu.ne_zero ((CharP.cast_eq_zero_iff _ _ N).mpr h)
      exact hp.of_dvd_left (addOrderOf_dvd_of_nsmul_eq_zero hm)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let M := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
    ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj K)
  let A := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G))
  let e : (moduleAbelianForget B S).obj M ≅ A :=
    ((moduleAbelianForget B S).mapDerivedCategoryPlusHomologyFunctorIso
      (q : ℤ)).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      ((moduleAbelianDerivedLowerStarIso B f).app K ≪≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).mapIso
          (((moduleAbelianForget B X).mapDerivedCategoryPlusSingleFunctor 0).app F))
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_moduleSpecialization_of_abelianIso M A e s t
      (isIso_etaleStalkSpecialization_of_proper_locallyAcyclic f G hG hf q s t))

end AlgebraicGeometry.Etale
