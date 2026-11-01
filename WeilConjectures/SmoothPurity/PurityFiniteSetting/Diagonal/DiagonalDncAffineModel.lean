/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Restricted.RestrictedAffineDiagonalDncTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Restricted.RestrictedAffineDiagonalTraceBaseChange

/-! # The local DNC orientation on affine space

Source: blueprint latest, diagonal-dualizing-object proof, Steps 1--3 and canonicity.
(blueprint: lem-pur-diagonal-dnc-affine-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem assemble_section_trace
    {C : Type*} [Category C] {A B C₀ D E F G : C}
    (t : A ≅ B) (ρ : C₀ ≅ D) (α : E ≅ D) (δ : E ≅ F) (β : F ≅ B)
    (c : C₀ ≅ G) (s : B ⟶ E) (m : A ⟶ G)
    (hD : s ≫ δ.hom ≫ β.hom = 𝟙 B)
    (hB : s ≫ α.hom ≫ ρ.inv ≫ c.hom = t.inv ≫ m) :
    (t ≪≫ (ρ ≪≫ α.symm ≪≫ δ ≪≫ β).symm ≪≫ c).hom = m := by
  have hs : β.inv ≫ δ.inv = s := by
    apply (cancel_mono (δ.hom ≫ β.hom)).mp
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, hD]
  have hs' : β.inv ≫ δ.inv ≫ α.hom ≫ ρ.inv ≫ c.hom =
      s ≫ α.hom ≫ ρ.inv ≫ c.hom := by
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ α.hom ≫ ρ.inv ≫ c.hom) hs
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [hs', hB]
  simp only [Iso.hom_inv_id_assoc]

/-- On the affine projection the local DNC orientation is the actual counit mate.
There is no arbitrary smooth morphism or etale coordinate neighbourhood in this assertion.
Source: diagonal-dualizing-object proof, Steps 1--3; smooth-purity sketch,
Agreement on the model paragraph
(blueprint: lem-pur-diagonal-dnc-affine-model).

Proof: on the self-product of affine space use the automorphism (x,y) maps to
(x,y-x). It carries the diagonal to the zero section of the trivial vector bundle.
The conormal generators are the ordered differences y_i-x_i, so the Rees coordinates
are y_i-x_i=t*u_i. The deformation is the trivial vector bundle over the affine
line. The readings at one and zero in the normalized DNC family equation coincide;
uniqueness identifies delta with this standard comparison. BetaNormalized identifies
beta inverse with the zero restriction of the actual integration adjunct. Integration
in the trivial frame is the ordered affine trace. Translation invariance identifies
this trace with the trace before the change y maps to y-x. The base-change equation
for integration and adjunction mate pasting identify alpha with the section restriction
of that same adjunct. Cancel the section compositor. Restrict to V using arbitrary
base change of the affine trace; the compact-support exchange mate is exactly rho.
The finite Tate pullback and comparison of the degree-zero coefficient unit give
localInverse, with the ordered counit transpose diagonalAffineMate on its other side.
Every normalized t and D gives the same Kummer class and its trace; the root-tensor
comparisons are the prescribed ones. At d=0 this is the identity adjunction; on an
empty target open both sides are the unique maps between zero objects. -/
theorem diagonalDncAffineModel (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    [SmoothOfRelativeDimension d (affineTraceProjection Y d)]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (E : OrientationRefinement.Chart P (affineTraceProjection Y d) aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    let ν := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower Y d)).mapDerivedCategory
    (OrientationCounit.localInverse P d (affineTraceProjection Y d) aY V E).hom =
      (OrientationRefinement.pull P ((affineTraceProjection Y d) ⁻¹ᵁ V.1).ι).map
        (ν.map (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d)) := by
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower Y d)).mapDerivedCategory
  let L := OrientationRefinement.pull P (affineTraceProjection Y d ⁻¹ᵁ V.1).ι
  let c := L.mapIso (ν.mapIso (OrientationCounit.unitChange P (affineTraceProjection Y d)))
  unfold OrientationCounit.localInverse OrientationRefinement.theta
  change (OrientationRefinement.tate P (affineTraceProjection Y d ⁻¹ᵁ V.1).ι
      (affineTraceProjection Y d ≫ aY) d ≪≫
    (OrientationRefinement.rho P (affineTraceProjection Y d) aY d V E.geometry ≪≫
      (OrientationRefinement.alpha P (affineTraceProjection Y d) aY d V E.geometry).symm ≪≫
      OrientationRefinement.delta P (affineTraceProjection Y d) aY d V E.geometry ≪≫
      OrientationRefinement.beta P (affineTraceProjection Y d) aY d V
        E.geometry E.betaEtale).symm ≪≫ c).hom = _
  exact assemble_section_trace _ _ _ _ _ c
    (OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V E.geometry t D) _
    (P.restrictedAffineDiagonalDncTrace Y d aY V E t D)
    (P.restrictedAffineDiagonalTraceBaseChange Y d aY V E.geometry t D)

end WeilConjectures.PurityFiniteSetting
