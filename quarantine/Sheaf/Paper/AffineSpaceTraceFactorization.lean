module

public import Sheaf.Paper.AffineSpaceTraceProductData
import Sheaf.Paper.AffineSpaceTraceSuccessorContraction
import Sheaf.Paper.AffineSpaceTraceContractionProduct
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Binary factorization of the actual affine-space exceptional transpose

Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph
(blueprint: lem-pur-affine-space-trace-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpaceTrace
open AffineLinePurity AffineSpacePurity VectorIntegrationSite OrderedAffineTranspose

section UnitorCoherence
universe v w
variable {Cat : Type v} [Category.{w} Cat] [MonoidalCategory Cat]
private theorem unitors {I : Cat} (e : I ≅ 𝟙_ Cat) :
    ((curriedTensor Cat).obj I).map e.hom ≫ (ρ_ I).hom =
      ((curriedTensor Cat).map e.hom).app I ≫ (λ_ I).hom := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc]
  rw [← rightUnitor_naturality, ← leftUnitor_naturality]
  rw [← Category.assoc, ← Category.assoc, ← unitors_equal]
  exact congrArg (fun f ↦ f ≫ (λ_ _).hom)
    (((curriedTensor Cat).map e.hom).naturality e.hom)

private theorem naturality {I V U : Cat} (e : I ≅ 𝟙_ Cat) (i : V ⟶ I) (t : U ⟶ I) :
    ((curriedTensor Cat).obj V).map t ≫
      (((curriedTensor Cat).obj V).map e.hom ≫ (ρ_ V).hom) ≫ i =
      ((curriedTensor Cat).map i).app U ≫ ((curriedTensor Cat).obj I).map t ≫
        (((curriedTensor Cat).map e.hom).app I ≫ (λ_ I).hom) := by
  have hr : (((curriedTensor Cat).obj V).map e.hom ≫ (ρ_ V).hom) ≫ i =
      ((curriedTensor Cat).map i).app I ≫
        (((curriedTensor Cat).obj I).map e.hom ≫ (ρ_ I).hom) := by
    rw [Category.assoc, ← rightUnitor_naturality]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ (ρ_ _).hom)
      (((curriedTensor Cat).map i).naturality e.hom)
  rw [hr, ← Category.assoc, NatTrans.naturality, Category.assoc, unitors]
end UnitorCoherence

private theorem contract_naturality (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (V U : C A Y) (i : V ⟶ unit A Y) (t : U ⟶ unit A Y) :
    ((tensor A Y).obj V).map t ≫ (moduleRightUnit A Y V).hom ≫ i =
      ((tensor A Y).map i).app U ≫ ((tensor A Y).obj (unit A Y)).map t ≫
        (AffineLineEvaluation.comparedLeftUnit (ModuleCat.{u + 1} A) Y
          (unit A Y)).hom := by
  unfold moduleRightUnit coefficientRightUnit AffineLineEvaluation.comparedLeftUnit
  exact naturality (coefficientUnitIso (ModuleCat.{u + 1} A) Y) i t

/-- The actual exceptional transpose is the line trace at one, and factors through
kappa_(m,1) as I_m tensor t for every m>=1, with the coefficient-unit unitor restored.
Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph
(blueprint: lem-pur-affine-space-trace-factorization).

Proof:
1. The ordered recursion is the four-arrow map Theta of
   lem-pur-affine-line-composite-transpose. Tate powers are finite-Tor constructible
   by prop-weil-twist-preserves. Apply composite_transpose at p=p_m and M=T_m:
   its transpose is I_m Rp_m!(b_(q,T_m)) alpha inverse. At one, the identity
   normalization and evaluation_unit give exactly normalized integration t_Y.
2. Apply lem-pur-base-changed-line-trace-evaluation at f=p_m, M=T_m.
   The finite-Tor hypotheses are the assumed V_m and U; canonical projection and
   exchange are invertible on these objects. UniversalLineBaseChange gives the
   normalized trace equality over each base. Its evaluation formula replaces
   Rp_m!(b) alpha inverse by D followed by 1 tensor t_Y and the right unitor.
3. By lem-pur-affine-space-last-factor-product this D is the specified kappa_(m,1),
   the inverse of exactly binaryForward, under externalTateIso. Substitute in step 2.
   Tensor bifunctoriality and unitor naturality move I_m to the coefficient factor,
   yielding kappa followed by I_m tensor t_Y and the coefficient-unit unitor.
No coordinate permutation of a purity comparison enters this argument. -/
theorem affineSpaceTraceFactorization (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (_hV : ∀ d : ℕ, 1 ≤ d →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y
        ((compact P Y d).obj (tate P Y d)))
    (_ht : UniversalLineBaseChange P Y aY)
    (κ : ∀ d : ℕ, (compact P Y (d + 2)).obj (tate P Y (d + 2)) ≅
      ((tensor (Ring P) Y).obj ((compact P Y (d + 1)).obj (tate P Y (d + 1)))).obj
        ((compact P Y 1).obj (tate P Y 1)))
    (_hκ : ∀ d : ℕ, BinaryProductSpecified P Y aY d (κ d)) :
    integration P Y aY 1 = lineNormalizedIntegration P Y aY ∧
    ∀ d : ℕ, integration P Y aY (d + 2) =
      (κ d).hom ≫
        ((tensor (Ring P) Y).map (integration P Y aY (d + 1))).app _ ≫
        ((tensor (Ring P) Y).obj (unit (Ring P) Y)).map
          (lineNormalizedIntegration P Y aY) ≫
        (AffineLineEvaluation.comparedLeftUnit (ModuleCat.{u + 1} (Ring P)) Y
          (unit (Ring P) Y)).hom := by
  constructor
  · exact (orderedAffineTranspose_projection P Y aY (unitPlus (Ring P) Y)
      (Etale.ordinaryFiniteUnit (Ring P) Y)
      ((Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y).prop_of_iso
        (unitEtaleIso (Ring P) Y).symm (Etale.constructibleFiniteTor_unit (Ring P)))
      (Iso.refl _)).2.2.1
  · intro d
    rcases _hκ d with ⟨h, hk⟩
    have hVd := _hV (d + 1) (Nat.succ_pos _)
    have hV1 := _hV 1 le_rfl
    have hVnext := _hV (d + 2) (by omega)
    have hp := lastLineContraction_product (P := P) (Y := Y) (aY := aY) (d := d)
      hVd hV1 hVnext _ht (κ d) h hk
    obtain ⟨hq, hc⟩ := hp
    have hs := integration_successor_contraction P Y aY d h hq
    have he := congrArg (fun f ↦ f ≫ integration P Y aY (d + 1)) hc
    have hn := congrArg ((κ d).hom ≫ ·)
      (contract_naturality (Ring P) Y _ _ (integration P Y aY (d + 1))
        (lineNormalizedIntegration P Y aY))
    exact hs.trans (he.trans (by simpa only [Category.assoc] using hn))

end AlgebraicGeometry.ProEtale.AffineSpaceTrace
