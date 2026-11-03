/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! Mixed support pasting and the base-change cube.
Source: latest blueprint composition proof, normalized proper/open comparisons.
(blueprint: lem-zl-geometric-gamma-pasting). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The two mixed pasting equations and the base-change cube.
These are the coherence part of the normalized proper/open comparisons.
Source: latest blueprint composition proof, canonicity, associativity and base change.
(blueprint: lem-zl-geometric-gamma-pasting). -/
structure GeometricGammaLaws (F : WeilConjectures.FiniteFieldDatum.{u}) : Prop where
  /-- Vertical mixed pasting, with canonical direct-image compositors at both ends. -/
  gamma_vertical : ∀ {U W Y Z V T : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {i : Y.obj.left ⟶ Z.obj.left} {k : V.obj.left ⟶ T.obj.left}
    {p₁ : U.obj.left ⟶ Y.obj.left} {p₂ : Y.obj.left ⟶ V.obj.left} {r₁ : W.obj.left ⟶ Z.obj.left}
    {r₂ : Z.obj.left ⟶ T.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k)
    (_h₁ : IsAdmissibleSquare j p₁ r₁ i) (_h₂ : IsAdmissibleSquare i p₂ r₂ k)
    (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    properOpenComponent Λ q K =
      (J Λ k).map ((rComp Λ p₁ p₂).inv.app K) ≫
      properOpenComponent Λ q₂ ((R Λ p₁).obj K) ≫
      (R Λ r₂).map (properOpenComponent Λ q₁ K) ≫
      (rComp Λ r₁ r₂).hom.app ((J Λ j).obj K)
  /-- Horizontal mixed pasting, with canonical open compositors at both ends. -/
  gamma_horizontal : ∀ {U W V Y Z T : SepFinType F.k}
    {j₁ : U.obj.left ⟶ W.obj.left} {j₂ : W.obj.left ⟶ V.obj.left} {i₁ : Y.obj.left ⟶ Z.obj.left}
    {i₂ : Z.obj.left ⟶ T.obj.left}
    {p : U.obj.left ⟶ Y.obj.left} {r : W.obj.left ⟶ Z.obj.left} {s : V.obj.left ⟶ T.obj.left}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact j₁] [QuasiCompact j₂] [QuasiCompact i₁] [QuasiCompact i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂))
    (_h₁ : IsAdmissibleSquare j₁ p r i₁) (_h₂ : IsAdmissibleSquare j₂ r s i₂)
    (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    properOpenComponent Λ q K =
      (jComp Λ i₁ i₂).inv.app ((R Λ p).obj K) ≫
      (J Λ i₂).map (properOpenComponent Λ q₁ K) ≫
      properOpenComponent Λ q₂ ((J Λ j₁).obj K) ≫
      (R Λ s).map ((jComp Λ j₁ j₂).hom.app K)
  /-- Base-change cube (c), at bounded constructible inputs and without inverting Ex. -/
  cube : ∀ {U W Y Z U' W' Y' Z' : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {p : U.obj.left ⟶ Y.obj.left} {r : W.obj.left ⟶ Z.obj.left}
    {i : Y.obj.left ⟶ Z.obj.left}
    {j' : U'.obj.left ⟶ W'.obj.left} {p' : U'.obj.left ⟶ Y'.obj.left}
    {r' : W'.obj.left ⟶ Z'.obj.left} {i' : Y'.obj.left ⟶ Z'.obj.left}
    {aU : U'.obj.left ⟶ U.obj.left} {aW : W'.obj.left ⟶ W.obj.left} {aY : Y'.obj.left ⟶ Y.obj.left}
    {b : Z'.obj.left ⟶ Z.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact j'] [QuasiCompact i']
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (_hQ : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    (P Λ b).map (properOpenComponent Λ q K) ≫
      (derivedDirectImageOpenRestriction Λ qr.toCommSq).app ((J Λ j).obj K) ≫
      (R Λ r').map (openExchangeComponent Λ qj.toCommSq K) =
    openExchangeComponent Λ qi.toCommSq ((R Λ p).obj K) ≫
      (J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K) ≫
      properOpenComponent Λ q' ((P Λ aU).obj K)

/-- The normalized Gamma comparisons satisfy mixed pasting and the base-change cube
at bounded constructible geometric inputs.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, canonicity,
associativity and base-change paragraphs; Stacks 0F7C, 0F7D, 0F7F, formal support argument.
(blueprint: lem-zl-geometric-gamma-pasting).

Proof: Factor each proper square through the Cartesian inverse-image open V and
its clopen subopen U. For a Cartesian square the extra support projector is identity;
for a proper square use projection onto the U coordinate in V = U ⊔ C. Compose
normalized inverse open exchange with this projection to obtain the inverse-image
support map A_Q : P_r J_i → J_t P_q → J_t J_s P_s P_q → J_j P_p, using the
prescribed open and pullback compositors in the last arrow. Its proper-adjunction
mate is R_r(J_j counit_p) after R_r(A_Q R_p) after unit_r(J_i R_p).
Under the two proper adjunctions this mate is Gamma: the open transpose
is inverse support restriction, since the open unit and counit cancel and the
clopen projection has coordinates (identity, zero). For a vertical paste both support
maps retain the intersection of the pulled-back lower support and the upper support;
for a horizontal paste they retain the composite top open. Their coordinates agree
on that support and vanish on its complement. Fully faithful open extension and
clopen coordinate detection prove equality, also for mixed Cartesian/proper pastes.
The two mate-pasting formulas then give the stated Gamma equations, with exactly
the conjugate direct-image and open compositors. Finally pull back the support decomposition
through the cube.
Pullback commutes with restriction and zero insertion, so both projections have
coordinates (identity, zero). Open exchange pasting gives the inverse-image cube.
The mate-cube theorem turns this into the displayed equation, with the recorded
pullback-square mates for Ex_p and Ex_r. Only open comparisons are inverted.
Evaluate at the stipulated inputs; no k-linearity of the scheme maps is used. -/
theorem geometricGammaPasting (F : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ F.p) :
    GeometricGammaLaws (Profinite.padicAlgClRingObj ℓ) F := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
