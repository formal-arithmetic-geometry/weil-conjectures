/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

public import WeilConjectures.Topology.OpenModuleCohomology
import Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Affine-local cohomology of external coefficients

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, acyclic base case.
(blueprint: lem-sc-picard-external-coefficients-affine-local-cohomology).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def scalarCechIso
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type w} (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (q : ℕ) :
    (((ModuleCat.restrictScalars (scalarMap f ⊤)).mapHomologicalComplex (.up ℕ)).obj
      ((cechComplexFunctor U).obj F.presheafModuleCat)).homology q ≅
        scalarCohomology f F q := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let I := injectiveResolution F
  have : QuasiIso (moduleCechBeta U I) := moduleCechBeta_quasiIso_of_affine U hU F I
  have : IsIso (HomologicalComplex.homologyMap (moduleCechAlpha U I) q) :=
    moduleCechAlpha_isIso U hcover I q
  let e := asIso (HomologicalComplex.homologyMap (moduleCechBeta U I) q) ≪≫
    (asIso (HomologicalComplex.homologyMap (moduleCechAlpha U I) q)).symm ≪≫
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).symm
  let R := ModuleCat.restrictScalars (scalarMap f ⊤)
  let A := (cechComplexFunctor U).obj F.presheafModuleCat
  exact (A.sc q).mapHomologyIso R ≪≫ R.mapIso e


/-- Cohomology of external coefficients over an inverse-image affine open is the
tensor product of cohomology of F with sections of G. No acyclicity is required.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, paragraph
"Let V be an affine open".
(blueprint: lem-sc-picard-external-coefficients-affine-local-cohomology).

Proof: Choose a finite affine cover U_i of X. Affine diagonal makes its finite
nonempty intersections affine. The inverse image of V under the second projection
is X times V, covered by U_i times V, whose intersections are affine. Restricting
the external coefficient to this product agrees with the external coefficient of
F and G restricted to V, by the pullback adjunction units and tensor restriction.
The affine fibre-product, pullback-section and tensor-section formulas identify
its Cech complex with Cech(U,F) tensor_k G(V). On pure tensors these formulas commute
with restrictions, so they identify the differentials as well. Finite products
commute with tensor; over the field k tensor is exact, and therefore commutes with
cohomology. Affine Cech comparison identifies the result in degree q with
H^q(X,F) tensor_k G(V). Restriction of an injective resolution identifies
this cohomology with openModuleCohomology on the original product. The scalarObj
on the right is G restricted to V, evaluated at its top open; restriction of
scalars along V -> Y -> Spec k gives its k-vector-space structure. Empty X or V
and zero coefficients give zero complexes, so are included. -/
theorem picardExternalCupCoefficients_affine_local_cohomology
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (V : Y.Opens) (hV : IsAffineOpen V) (q : ℕ) :
    Nonempty
      (((RingedSpace.openModuleCohomology (Limits.pullback f g).toRingedSpace q
        ((pullback.snd f g) ⁻¹ᵁ V)).obj (externalCupCoefficients f g F G)) ≅
        AddCommGrpCat.of (scalarCohomology f F q ⊗[k]
          scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))) := by
  classical
  obtain ⟨s, hs, hsc⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp
      (isCompact_univ : IsCompact (⊤ : X.Opens).carrier)
  let : Fintype s := hs.fintype
  let U : s → X.Opens := fun i ↦ i.val.val
  have hcover : iSup U = ⊤ := by
    simpa only [U, iSup_subtype] using hsc.symm
  have hU : ∀ (n : ℕ) (y : Fin (n + 1) → s), IsAffineOpen (⨅ l, U (y l)) := by
    intro n y
    apply InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
    · intro A hA B hB
      exact (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
        A (by simp) B (by simp) hA hB
    · intro i
      exact (y i).val.property
  let R := ModuleCat.restrictScalars (scalarMap f ⊤)
  let C := (R.mapHomologicalComplex (.up ℕ)).obj
    ((cechComplexFunctor U).obj F.presheafModuleCat)
  let T := MonoidalCategory.tensorRight (scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))
  let : Module.Free k (scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤)) :=
    Module.Free.of_divisionRing k _
  let : PreservesFiniteLimits T := by dsimp [T]; infer_instance
  let : PreservesFiniteColimits T := by
    exact preservesFiniteColimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight _)
  obtain ⟨e⟩ := picardExternalCupCoefficients_affine_cech_comparison
    k X Y f g F G U hU hcover V hV q
  let a := (C.sc q).mapHomologyIso T
  let b := T.mapIso (scalarCechIso f F U hU hcover q)
  exact ⟨e ≪≫ (forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).mapIso (a ≪≫ b)⟩

end AlgebraicGeometry.Scheme.Modules
