module

public import Sheaf.RingTheory.AffineDilatationAlgebra
public import Sheaf.RingTheory.ValuedPointDifferentialDefect
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.SmoothAtGenericPointOverField
import Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# One residue-point dilatation lowers the index-one differential defect

Source: BLR, Neron Models, 3.6 Proposition 3, printed p.79 (PDF p.85), and
3.2 Proposition 1, printed p.63 (PDF p.69).
(blueprint: lem-sfb-index-one-residue-dilatation-defect-drop)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- The affine dilatation at the schematic closure of the residue of `φ`.
Source: BLR 3.6 Proposition 3 and the affine construction of 3.2.
(blueprint: lem-sfb-index-one-residue-dilatation-defect-drop) -/
noncomputable def residueDilatationAlgebra {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [CommRing A] [IsLocalRing A]
    [Algebra R B] [Algebra R A] (π : R) (φ : B →ₐ[R] A) :
    Subalgebra B (Localization.Away (algebraMap R B π)) :=
  affineDilatationAlgebra (algebraMap R B π)
    (RingHom.ker ((IsLocalRing.residue A).comp φ.toRingHom))

/-- Dilatation at one residue point lowers the index-one differential defect.
Source: BLR 3.6 Proposition 3, printed p.79; 3.2 Proposition 1, printed p.63.
(blueprint: lem-sfb-index-one-residue-dilatation-defect-drop)

Proof: (1) A DVR is Noetherian. Finite type makes B Noetherian
(lem-weil-pbc-finite-type-algebra-noetherian), so finitely many ideal generators
suffice to generate B[I/π]. Its ambient localization gives π-injectivity and the
unchanged generic fibre. Evaluation of the generators lies in A; cancellation
gives its unique extension (def-sc-discrete-valuation-ring).
(2) The residue image D is a finite type domain over the residue field. Its
fraction field is separable (def-weil-pbc-separable-field-extension), so shrink
D to make it smooth (lem-weil-pbc-smooth-at-generic-point-over-field) and its
restricted differential module free (lem-pur-noetherian-algebra-module-generic-freeness).
(3) Lift the localization element to B; its evaluation is a unit, so the evaluated
modules and dilatations are unchanged (lem-weil-pbc-kahler-differentials-localization).
Use lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-sc-relative-differential-sheaf,
lem-weil-pbc-tilde-pullback-base-change and lem-weil-pbc-spec-module-tilde-sections
to apply lem-sfb-adapted-smooth-ambient. Obtain C/H and coordinates y,z with
J=(π,z), an etale coordinate map and the differential isomorphism on C/J.
(4) Write h=πc+Σ z_j c_j for h in H. The differential isomorphism forces
c_j in J. Evaluating h and cancelling π forces c in J because C/J embeds in
κ(A). Thus H is contained in J².
(5) Apply lem-sfb-smooth-centre-dilatation-coordinates to form C'=C[J/π].
The dilatated quotient has ideal H' given by π-saturation of HC'. Each h/π²
belongs to H'. Its evaluation in A is zero by cancellation.
(6) Differentiate h=π²(h/π²): the y coefficients divide by π², and the z
coefficients divide by π, since dz=π dz'.
(7) The quotient differential sequence (lem-weil-pbc-jacobi-zariski-differential-maps)
and tensor products (def-weil-pbc-module-tensor-product) present both evaluated
modules as finite free modules modulo the evaluated relation rows.
(8) The localized defining ideals agree, so their relation spans have the same
fraction-field rank q under the invertible coordinate change.
(9) Apply lem-sfb-dvr-relation-minors-length. If q>0, a minimizing q-minor
scales down by π to exponent q+p, where p counts y columns. Thus the new
length is at most the old length minus one. If q=0 both relation modules vanish
and both torsion lengths are zero. The localization comparisons transport this
bound back to the original point. No excellence, completion, or fraction-field
separability is used. -/
theorem indexOne_residueDilatation_defect_drop
    {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalHom (algebraMap R A)]
    (hinj : Function.Injective (algebraMap R A))
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (hindex : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap R A π})
    (hsep : @IsSeparableExtension (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A) _ _
      (IsLocalRing.ResidueField.map (algebraMap R A)).toAlgebra)
    (hfinite : (algebraMap R B).FiniteType)
    (hregular : Function.Injective (fun b : B => algebraMap R B π * b))
    (hsmooth : RingHom.Smooth (IsLocalization.Away.map (Localization.Away π)
      (Localization.Away (algebraMap R B π)) (algebraMap R B) π))
    (φ : B →ₐ[R] A) :
    (algebraMap R (residueDilatationAlgebra π φ)).FiniteType ∧
    Function.Injective
      (fun b : residueDilatationAlgebra π φ => algebraMap R _ π * b) ∧
    IsLocalization.Away (algebraMap R (residueDilatationAlgebra π φ) π)
      (Localization.Away (algebraMap R B π)) ∧
    ∃ φ' : residueDilatationAlgebra π φ →ₐ[R] A,
      (∀ b : B, φ' (algebraMap B (residueDilatationAlgebra π φ) b) = φ b) ∧
      (∀ ψ : residueDilatationAlgebra π φ →ₐ[R] A,
        (∀ b : B, ψ (algebraMap B (residueDilatationAlgebra π φ) b) = φ b) → ψ = φ') ∧
      (∀ b : RingHom.ker ((IsLocalRing.residue A).comp φ.toRingHom),
        algebraMap R A π * φ'
          (affineDilatationGenerator (algebraMap R B π) _ b) = φ b) ∧
      valuedPointDifferentialDefect φ' ≠ ⊤ ∧
      valuedPointDifferentialDefect φ' ≤ max 0 (valuedPointDifferentialDefect φ - 1) := by
  sorry

end Algebra
