/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Sheaf.RingTheory.FormalGlueingData

/-! # Affine localization coordinates and their restriction squares

Source: Stacks Project, Tags 0BLH and 05EL.
(blueprint: lem-sbc-punctured-completion-affine-coordinate-squares)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Affine localization gives coordinates on chart intersections and completed charts,
with all four maps from the original section modules commuting with restriction.

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).

Proof: by hcharts, each D(g_j) lies in U.
The restriction of q to this affine open is finite, hence its source V_j is affine.
The finite morphism s also makes E affine. Use Gamma(E) as the C-module M' and
Gamma(Y,V_j) as M_j, with its structural A[1/g_j]-action. The action exists since
g_j is invertible on V_j. Take e and d to be the identity section identifications,
with restriction of scalars through the displayed structural A-actions.
Principal-open localization identifies (M_j) localized at g_i with
Gamma(Y,V_i intersect V_j); use this identification as c_ij. The affine fibre
product formula identifies C tensor_A M_j with Gamma(O,p inverse image V_j);
use this identification as b_j. The given overlap isomorphism identifies
M' localized at g_j with that same section ring. Define alpha_j by composing
this latter identification with b_j inverse, and alpha_overlap_ij by the two
principal-open identifications (using the symmetry of the intersection).
These maps are isomorphisms. Since the overlap isomorphism is over Spec C,
alpha_j is C-linear. On (m/g_j^a)/g_k^b both cocycle routes restrict m to the triple chart and
then divide by g_j^a g_k^b. On (m'/g_i^a)/g_j^b both square routes restrict the
E-section to the completed double chart and divide by g_i^a g_j^b. The swap
maps exchange denominators; compare sends (c tensor m)/g_j^b to
c tensor (m/g_j^b). Fraction generation and additive generation by pure tensors
extend these identities to the complete maps. Thus these maps define FormalGlueing.Data.
The four asserted equations are the numerator formulas for these localization
and tensor identifications: completed restriction, chart pullback, and the two
restrictions to an intersection, respectively. No H0 or matching-ring assertion
is used. Empty charts have zero section rings, so the identifications and all
four equations still hold for zero, nilpotent, or redundant generators. When
t = 0 the chart families and their equations are empty; the construction of
M' is unchanged.
(blueprint: lem-sbc-punctured-completion-affine-coordinate-squares) -/
theorem exists_affine_coordinate_squares
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (g : Fin t → A)
    (hcharts : ∀ j, PrimeSpectrum.basicOpen (g j) ≤ U) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let V : Fin t → Y.Opens := fun j ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j)
    let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
    let aE := ((ΓSpecIso (.of A)).inv ≫ (s ≫ completionSpecMap A).appTop).hom
    letI : Algebra A Γ(Y, ⊤) := aY.toAlgebra
    letI : Algebra A Γ(E, ⊤) := aE.toAlgebra
    letI : ∀ j, Algebra A Γ(Y, V j) := fun j ↦
      ((Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op).hom.comp aY).toAlgebra
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    letI : Algebra A C := φ.toAlgebra
    ∃ (X : FormalGlueing.Data.{u, u, u} φ g)
      (e : FormalGlueing.restrict φ X.M' ≃ₗ[A] Γ(E, ⊤))
      (d : ∀ j, FormalGlueing.piece (g j) (X.M j) ≃ₗ[A] Γ(Y, V j))
      (b : ∀ j, FormalGlueing.restrict φ
        (FormalGlueing.extend φ (FormalGlueing.piece (g j) (X.M j))) ≃ Γ(O, p ⁻¹ᵁ V j))
      (c : ∀ i j, FormalGlueing.localize (g i)
        (FormalGlueing.piece (g j) (X.M j)) ≃ Γ(Y, V i ⊓ V j)),
      (∀ j m, b j (X.alpha j (LocalizedModule.mk m 1)) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op
          (D.toCompleted.appTop (e m))) ∧
      (∀ j m, b j (TensorProduct.tmul A (1 : C) m) = p.app (V j) (d j m)) ∧
      (∀ i j m, c i j (X.alpha_overlap i j (LocalizedModule.mk m 1)) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (d i m)) ∧
      (∀ i j m, c i j (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (d j m)) := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
