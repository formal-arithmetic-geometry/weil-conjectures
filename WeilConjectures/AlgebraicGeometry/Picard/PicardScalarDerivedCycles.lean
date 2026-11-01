/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections

import WeilConjectures.AlgebraicGeometry.PicardOrdinaryScalarCoordinates
import WeilConjectures.AlgebraicGeometry.Picard.PicardConnectiveModelComparison

/-! # Scalar cycles as derived test sections

Source: Stacks Project, Tag 0BF2, the degree-zero cycle calculation.
(blueprint: lem-sc-picard-scalar-derived-cycles)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The scalar-cycle calculation for an arbitrary derived object with a fixed connective
strictly perfect model. No direct image or family of line bundles occurs in this lemma.
Source: Stacks Project, Tag 0BF2, degree-zero cycle calculation; Tags 08C4 and 0D5S.
(blueprint: lem-sc-picard-scalar-derived-cycles)

Proof: Apply picard_connective_model_comparison to the fixed model isomorphism hE.
It supplies simultaneous additive equivalences q from derived test sections to ordinary
cycles on all schemes factoring through U, compatible with the canonical composition
restriction. Apply picard_ordinary_scalar_coordinates to the section bases and hd.
It gives a raw residue coordinate equivalence b, proves that every residue morphism
is a cycle using hdw, and constructs a local ordinary cycle x for each annihilating
scalar a, with restricted b-coordinate a(w). Restrict b to the residue cycles subgroup;
its inverse sends a scalar z to the cycle with raw representative b.symm z. Compose
with q at the residue point to obtain c. The factorization of the residue point through
V and then U equals the direct factorization through U, since U.ι is mono. Put ξ=q_V.symm x.
Naturality of q identifies its derived restriction with the ordinary restriction of x.
The coordinate equality gives c of this restriction equal to a(w); injectivity of c
then gives the asserted equality with c.symm(a(w)). The fixed model makes c independent
of V. Rank m=0 has zero outgoing differential; w excludes empty V and U. -/
theorem picard_scalar_derived_cycles
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d)
    (hdw : ∀ i, W.evaluation U w hwU (d i) = 0) :
    ∃ c : picardDerivedModelSections E (W.fromSpecResidueField w) ≃+ W.residueField w,
      ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U) (a : Γ(W, V)),
        (a • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i)) = 0) →
        ∃ ξ : picardDerivedModelSections E V.ι,
          picardDerivedModelRestriction E (picardResidueLift W w V hwV) V.ι
              (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV) ξ =
            c.symm (W.evaluation V w hwV a) := by
  classical
  obtain ⟨q, hq⟩ := picard_connective_model_comparison W E U K hK hneg hE
  obtain ⟨b, hb, hlift⟩ :=
    picard_ordinary_scalar_coordinates W w U hwU hU m d K hK e0 e1 hd hdw
  let p := picardResidueLift W w U hwU
  let qκ := q (W.fromSpecResidueField w) p (picardResidueLift_comp W w U hwU)
  let bκ : picardOrdinaryModelCycles W U K (W.fromSpecResidueField w) p ≃+
      W.residueField w :=
    { toFun := fun x ↦ b x.val
      invFun := fun a ↦ ⟨b.symm a, hb _⟩
      left_inv := fun x ↦ Subtype.ext (b.symm_apply_apply x.val)
      right_inv := fun a ↦ b.apply_symm_apply a
      map_add' := fun x y ↦ b.map_add x.val y.val }
  refine ⟨qκ.trans bκ, ?_⟩
  intro V hwV hVU a ha
  have hVUι : W.homOfLE hVU ≫ U.ι = V.ι := by simp
  have hp : picardResidueLift W w V hwV ≫ W.homOfLE hVU = p := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, hVUι, picardResidueLift_comp, picardResidueLift_comp]
  obtain ⟨x, hx⟩ := hlift V hwV hVU hp a ha
  let qV := q V.ι (W.homOfLE hVU) hVUι
  refine ⟨qV.symm x, ?_⟩
  apply (qκ.trans bκ).injective
  rw [AddEquiv.apply_symm_apply]
  change b (qκ (picardDerivedModelRestriction E (picardResidueLift W w V hwV)
    V.ι (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV)
      (qV.symm x))).val = _
  rw [hq (picardResidueLift W w V hwV) V.ι (W.fromSpecResidueField w)
    (W.homOfLE hVU) p (picardResidueLift_comp W w V hwV) hp hVUι
    (picardResidueLift_comp W w U hwU)]
  simpa only [qV, AddEquiv.apply_symm_apply] using hx

end AlgebraicGeometry.Scheme
