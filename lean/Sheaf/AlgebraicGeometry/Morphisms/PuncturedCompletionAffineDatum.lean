/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Sheaf.RingTheory.FormalGlueingH0

/-! # Affine section presentation of the local compatibility equations

Source: Stacks Project, Tags 0BLH and 05EL.
(blueprint: lem-sbc-punctured-completion-affine-datum)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The affine datum identifies its ambient coordinates with actual chart sections;
its compatibility equations are precisely local sheaf compatibility and local overlap agreement.

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, H0.

Proof: put V_j = (q followed by the inclusion of U) inverse image of D(g_j).
These opens cover Y: a prime different from the maximal ideal cannot contain all
its generators. Each V_j is affine because q is finite and D(g_j) is affine.
E is affine because s is finite. Set M' to Gamma(E), with the structural completion
module action, and M_j to Gamma(Y,V_j), with its structural A[1/g_j] action.
Affine localization identifies sections on V_j intersect V_k with localizations
of M_j and M_k. The overlapIso and affine base-change tensor-product formula
identify M' localized at g_j with C tensor M_j. Use these maps for alpha and
alpha_overlap. Their equations follow on numerators from restriction functoriality;
localization uniqueness extends the equations to fractions. The overlap isomorphism
is over Spec C, which proves alpha_smul. The underlying coordinate identifications
e and d are A-linear for the stated structural maps. The two families of kernels
in H0 now say exactly that d_j(x_j) restrict equally on intersections and that
their pullbacks agree locally with e(x'). This proves both directions of the iff,
without gluing a global section or constructing an element of the matching ring.
For an empty punctured spectrum the chart section rings are zero, the cover is
empty or consists of empty opens, and the same equations hold. Nilpotent and
redundant generators are allowed; their empty charts contribute zero modules.
(blueprint: lem-sbc-punctured-completion-affine-datum) -/
theorem exists_formalGlueingData_affine_datum
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (g : Fin t → A)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal A) :
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
    ⊤ ≤ iSup V ∧
    ∃ (X : FormalGlueing.Data.{u, u, u} φ g)
      (e : FormalGlueing.restrict φ X.M' ≃ₗ[A] Γ(E, ⊤))
      (d : ∀ j, FormalGlueing.piece (g j) (X.M j) ≃ₗ[A] Γ(Y, V j)),
      ∀ x : FormalGlueing.restrict φ X.M' ×
          ∀ j, FormalGlueing.piece (g j) (X.M j),
        x ∈ FormalGlueing.h0 φ g X ↔
          Y.presheaf.IsCompatible V (fun j ↦ d j (x.2 j)) ∧
          ∀ j, p.app (V j) (d j (x.2 j)) =
            O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op
              (D.toCompleted.appTop (e x.1)) := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
