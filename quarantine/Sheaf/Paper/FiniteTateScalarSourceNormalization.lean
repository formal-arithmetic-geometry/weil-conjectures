/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.Paper.VectorPurityScalarSingle
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.FiniteTateScalarSourceData
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Paper.FiniteTateScalarSourceExistence
import all Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import all Sheaf.Paper.ScalarPullbackIsoUniqueness

/-! # Unique normalized finite Tate scalar comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.upperStar Etale.lowerStar
namespace WeilConjectures.PurityFiniteSetting
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

attribute [local instance 20000] Etale.sheafMonoidalCategory
attribute [local irreducible] purityScalarSingleMap purityScalarUnitMap
  finiteTateScalarZeroIso finiteTateScalarLineMap finiteTateScalarSourceMap
  IsFiniteTateScalarBalancing IsFiniteTateScalarLineNormalized
  IsFiniteTateScalarSourceInvertible IsFiniteTateScalarSourceUnitNormalized
  IsFiniteTateScalarSourceZeroNormalized

private theorem balancing_unique
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β γ : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r)
    (hβ : IsFiniteTateScalarBalancing φ N hA hB X β)
    (hγ : IsFiniteTateScalarBalancing φ N hA hB X γ) : β = γ := by
  unfold IsFiniteTateScalarBalancing at hβ hγ
  have h1 : (β 1).hom = (γ 1).hom := by
    apply (Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ |>.injective
    apply (Scheme.lineHomEquiv X N A hA _).injective
    ext U z
    simp only [Scheme.lineHomEquiv_generator]
    have hb := hβ.1 1 U 1 1 (fun _ ↦ z)
    have hg := hγ.1 1 U 1 1 (fun _ ↦ z)
    simp only [one_smul, map_one, one_mul, Scheme.finiteTateEtalePowerGenerator] at hb hg
    exact hb.trans hg.symm
  funext r
  apply Iso.ext
  induction r with
  | zero => exact hβ.2.1.trans hγ.2.1.symm
  | succ r hr =>
    cases r with
    | zero => exact h1
    | succ r => rw [hβ.2.2 r, hγ.2.2 r, hr, h1]

private theorem single_map_eq (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    purityScalarSingleMap φ X M = Etale.FiniteSmoothPurity.scalarSingleMap φ X M := by
  rfl
private theorem single_from_rep_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (E : DerivedCategory C ⥤ DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (M : C) [IsIso (rep ((CochainComplex.singleFunctor C 0).obj M))] :
    IsIso (puritySingleFromRepresentativeMap F E rep M) := by
  unfold puritySingleFromRepresentativeMap
  infer_instance

private theorem single_map_iso (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hM : exactFunctor _ _ (tensorRight M)) : IsIso (purityScalarSingleMap φ X M) := by
  have hflat : ObjectProperty.flat M := by
    refine ⟨?_, hM⟩
    exact (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight M).symm hM
  have hP := (CochainComplex.kFlat_single_obj_iff_flat M (0 : ℤ)).2 hflat
  have := Etale.scalarRepresentative_isIso φ X
    ((CochainComplex.singleFunctor _ 0).obj M) hP
  have hrep : Etale.scalarAdjunctionRepresentativeMap (Etale.purityScalarSheaf φ X)
      (Sheaf.restrictScalars X.smallEtaleTopology φ) (Etale.purityScalarSheafAdjunction φ X)
      (Etale.purityScalarExtension φ X)
      (Etale.purityScalarAdjunction φ X) = Etale.scalarExtensionRepresentative φ X := by
    funext P
    unfold Etale.scalarExtensionRepresentative Etale.purityScalarAdjunction
      Etale.scalarAdjunctionRepresentativeMap
    with_unfolding_all rfl
  unfold purityScalarSingleMap
  rw [CategoryTheory.purityAdjunctionSingleMap_eq_representative]
  unfold purityRepresentativeSingleMap
  rw [hrep]
  exact single_from_rep_isIso (Etale.purityScalarSheaf φ X)
    (Etale.purityScalarExtension φ X) (Etale.scalarExtensionRepresentative φ X) M

/-- All ordinary balancing maps, uniquely fixed on local scalar/root generators;
flat-single computation; the unit, tensor-power and shift normalizations; and the
source isomorphism for every unbounded input, with its two endpoint unit equations.
The generator equation includes an arbitrary new scalar b, so it says precisely
(a tensor z) tensor b maps to phi(a)b tensor z in degree one. At degree zero it is
ordinary coefficient multiplication. Higher-degree generators are the existing
ordered root tensors, and the successor equation fixes the actual tensor powers.

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6, 07A4, 06YS, 0G7E, 03PK and 03RV
(blueprint: lem-pur-finite-tate-scalar-source-normalization).

Proof:
1. Flatness makes the single complex K-flat: tensoring an acyclic complex with M[0]
   is termwise exact tensoring by M (def-pc-flat-sheaf-modules, def-pc-kflat-complex).
   Its identity resolution computes scalar extension (lem-pur-derived-change-of-rings).
2. The normalized adjunct of x maps to x tensor 1 is the identity on the ordinary
   extended tensor (lem-pur-sheaf-ring-derived-coefficient-adjunction). Thus the actual
   scalar/single map equals the representative comparison and is invertible.
3. On the coefficient unit, multiply a tensor b to phi(a)b, with inverse b maps to
   1 tensor b. Balancing proves both identities and identifies the published unit.
4. The Tate sheaves are flat (lem-asd-finite-etale-twist-line). Construct balancing
   sectionwise; its inverse inserts 1 in each old coefficient factor. Both maps
   commute with restrictions and sheafification (def-pur-sheaf-tensor-product).
   The generator formulas determine each map uniquely, including the zero power.
5. The scalar tensorator is ordinary balancing on K-flat representatives
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback). It gives the displayed power
   equation. Scalar extension commutes termwise with shifts; localize this comparison.
   Every shift is even, so the regrouping introduces no sign.
6. Compose the tensorator, the inverse scalar/pullback comparison, and the shifted
   line map. Each is invertible, for every unbounded K; only the unbounded introductory
   comparison of lem-pur-etale-scalar-mate-projection is used.
7. Use the published scalar tensor-unit and scalar/pullback-unit coherence. Naturality
   transports the left tensor-unit equation along the specified single/unit maps.
   Cancel the pullback comparison and use its naturality to transport the coefficient
   unit square along the same maps. This gives the coefficient-unit source equation.
   Transport the existing scalar right-unit equation along the degree-zero line
   normalization to obtain the zero-power source equation. All comparisons remain
   the published ones, and no flatness of B over A is used. -/
theorem finite_tate_scalar_source_normalization [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)) :
    (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      exactFunctor _ _ (tensorRight M) →
        purityScalarSingleMap φ X M = Etale.FiniteSmoothPurity.scalarSingleMap φ X M ∧
        IsIso (purityScalarSingleMap φ X M)) ∧
    ∃! β : ∀ r : ℕ,
        (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
          Scheme.finiteEtaleTateTwist X N B hB r,
      IsFiniteTateScalarBalancing φ N hA hB X β ∧
      IsFiniteTateScalarLineNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceInvertible φ N hA hB X β ∧
      IsFiniteTateScalarSourceUnitNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceZeroNormalized φ N hA hB X β := by
  constructor
  · intro M hM
    exact ⟨single_map_eq φ X M, single_map_iso φ X M hM⟩
  · obtain ⟨β, hβ⟩ := finite_tate_scalar_source_normalization_exists φ N hN hA hB X hX
    refine ⟨β, hβ, ?_⟩
    intro γ hγ
    exact balancing_unique φ N hA hB X γ β hγ.1 hβ.1

end WeilConjectures.PurityFiniteSetting
