module
public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Sheaf.RingTheory.FormalGlueingH0
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData
/-- Finite affine chart sections give local matching families for formal glueing data.
Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, H0.
(blueprint: lem-sbc-punctured-completion-formal-glueing-data-prime)

Proof: set V_i to the inverse image under q followed by U's inclusion of D(f_i).
These opens cover Y: a prime other than the maximal ideal cannot contain all f_i,
since their span is that maximal ideal. Finiteness of q makes each V_i affine.
Finiteness of s makes E affine. Take M' to be Gamma(E) with its structural C-action
and M_i to be Gamma(Y,V_i), regarded as an A_{f_i}-module by the structural map.
Sections over double principal opens are localizations of these affine rings.
The overlap identification identifies the localization of M' at f_i with the
scalar extension of M_i to C. These identifications give alpha_i and alpha_ij;
restriction on double and triple opens proves the square and cocycle equations,
and compatibility with C-scalars gives alpha_smul. The prime identification e is
the identity. Define r_i(h) to be the i-th chart coordinate under the section
identification. The second H0 equations say these sections restrict equally to
V_i intersect V_j. The first H0 equations say their pullbacks to the overlap
agree with the restriction of e(h.prime). These are precisely the two displayed
local compatibility conditions. No global section or matching-ring element is
constructed here. If t is zero then U and Y are empty, so the cover and all local
conditions are empty; zero chart rings obey the same restriction equations. -/
theorem exists_formalGlueingData_prime
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hgen : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
    letI : Module C Γ(E, ⊤) := Module.compHom _ g.hom
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    ∃ (X : FormalGlueing.Data.{u, u, u} φ f) (e : X.M' ≃ₗ[C] Γ(E, ⊤))
      (V : Fin t → Y.Opens), ⊤ ≤ iSup V ∧
      ∃ (r : ∀ i, FormalGlueing.h0 φ f X → Γ(Y, V i)),
        (∀ h, Y.presheaf.IsCompatible V (fun i ↦ r i h)) ∧
        ∀ h i, p.app (V i) (r i h) =
          O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V i ≤ ⊤)).op
            (D.toCompleted.appTop (e h.val.1)) := by sorry
end AlgebraicGeometry.Scheme.CompletionGluingData
