module

public import Sheaf.AlgebraicGeometry.CurveVectorFieldsFixingPoints
public import Sheaf.AlgebraicGeometry.RationalSectionDivisor
public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.Curve.UniformizerDifferentialBasis
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials
import Mathlib.RingTheory.Etale.Kaehler

/-! # Tangent sections and zero divisors of curve derivations

Source: Stacks Project, curves.tex, Tags 0E67 and 0C1E; divisors.tex, Tags 02SF and 0BE6
(blueprint: lem-sfb-smooth-derivation-zero-divisor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The global section of the dual differential sheaf represented by a vector field.
Use the existing internal-Hom section equivalence and evaluate the compatible family at top.
Source: Stacks Project, Tag 0E67, first paragraph of the proof
(blueprint: lem-sfb-smooth-derivation-zero-divisor). -/
def smoothCurveTangentSection {X S : Scheme.{u}} (f : X ⟶ S)
    (θ : f.relativeDifferentials ⟶ Scheme.Modules.unit X) :
    Γ(Scheme.Modules.dual f.relativeDifferentials, ⊤) :=
  ((SheafOfModules.homObjSectionsEquiv f.relativeDifferentials
    (Scheme.Modules.unit X)).symm θ).val (op ⊤)

/-- Take the actual generic germ of a global section. The integral structure is supplied by
smoothness and connectedness, rather than imposed as an additional hypothesis.
Source: Stacks Project, divisors.tex, Tag 02SF
(blueprint: lem-sfb-smooth-derivation-zero-divisor). -/
def smoothCurveSectionGenericGerm (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : X.Modules) (s : Γ(L, ⊤)) : Scheme.Modules.rationalSection k X f L :=
  letI := Classical.choose (X.smooth_connected_curve_local_rings k f)
  TopCat.Presheaf.germ L.val.presheaf ⊤ (genericPoint X) trivial s

/-- Normalized order of a local coefficient, computed in the function field. At a closed
point of a smooth connected curve this is the normalized valuation of its DVR stalk.
Source: Stacks Project, divisors.tex, Tag 02SF
(blueprint: lem-sfb-smooth-derivation-zero-divisor). -/
def smoothCurveLocalCoefficientOrder (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (q : closedPoints X) (a : X.presheaf.stalk q.val) : ℤ :=
  letI := Classical.choose (X.smooth_connected_curve_local_rings k f)
  letI : IsNoetherian X := (Classical.choose_spec
    (X.smooth_connected_curve_local_rings k f)).1
  X.ord (algebraMap (X.presheaf.stalk q.val) X.functionField a) q.val

/-- The tangent sheaf of a smooth proper connected curve is invertible.
Source: Stacks Project, Tag 0E67, proof, with Tags 0BS2 and 08S2
(blueprint: lem-sfb-smooth-derivation-zero-divisor).

Proof: `lem-sc-canonical-sheaf` makes the differential sheaf invertible, using the
comparison `lem-sc-smooth-proper-diagonal-conormal-differentials` with the canonical
sheaf. Apply `lem-pc-tensor-dual-invertible` to its dual. -/
@[instance] theorem smooth_curve_tangent_invertible (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f] :
    (Scheme.Modules.dual f.relativeDifferentials).IsInvertible := by
  sorry

/-- The zero divisor is the existing rational-section divisor of the actual generic germ.
Its nonzero-germ argument is supplied by `smooth_derivation_zero_divisor` below.
Source: Stacks Project, divisors.tex, Tag 0BE6
(blueprint: lem-sfb-smooth-derivation-zero-divisor). -/
def smoothCurveTangentZeroDivisor (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (θ : f.relativeDifferentials ⟶ Scheme.Modules.unit X)
    (hη : smoothCurveSectionGenericGerm k X f (Scheme.Modules.dual f.relativeDifferentials)
      (smoothCurveTangentSection f θ) ≠ 0) : X.Divisor :=
  Scheme.Modules.rationalSectionDivisor k X f (Scheme.Modules.dual f.relativeDifferentials)
    ⟨smoothCurveSectionGenericGerm k X f (Scheme.Modules.dual f.relativeDifferentials)
      (smoothCurveTangentSection f θ), hη⟩

/-- The tangent degree and the canonical additive derivation/section dictionary.
`Derivation'` consists of additive, restriction-compatible Leibniz maps killing base sections.
Source: Stacks Project, Tag 0E67, first paragraph of the proof, and Tag 01UR
(blueprint: lem-sfb-smooth-derivation-zero-divisor).

Proof:
1. `lem-sc-canonical-degree` gives degree 2g-2 for the differential sheaf, after the
   diagonal-conormal comparison. The Picard degree homomorphism and tensor-dual identity
   give degree 2-2g for its dual (`def-sc-pic0`, `lem-pc-tensor-dual-invertible`).
2. `lem-sfb-relative-differentials-sheaf-universal-property` identifies morphisms theta with
   sheaf derivations by theta composed with d. Internal Hom identifies theta with global
   sections (`def-pur-sheaf-hom`); a compatible family is determined by its value at top.
3. Composition with d is additive on every open, giving the asserted additive identification.
   This includes the zero derivation. -/
theorem smooth_curve_tangent_dictionary (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f] :
    f.picDegree (@Scheme.Pic.mk X (Scheme.Modules.dual f.relativeDifferentials)
      (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
        (Scheme.Modules.dual f.relativeDifferentials))) =
      2 - 2 * (f.genus : ℤ) ∧
    ∃ e : Γ(Scheme.Modules.dual f.relativeDifferentials, ⊤) ≃
        (Scheme.Modules.unit X).val.Derivation' f.pullbackPresheafToPresheaf,
      (∀ θ : f.relativeDifferentials ⟶ Scheme.Modules.unit X,
        e (smoothCurveTangentSection f θ) =
          f.relativeDifferentialsHomEquiv (Scheme.Modules.unit X) θ) ∧
      (∀ (s t : Γ(Scheme.Modules.dual f.relativeDifferentials, ⊤)) (U : X.Opens),
        (e (s + t)).d (X := op U) = (e s).d (X := op U) + (e t).d (X := op U)) := by
  sorry

/-- Closed points are rational, and preserving their ideals is fibre vanishing.
Fibre vanishing is membership of the germ in the maximal ideal times the stalk module,
i.e. zero in the quotient by that submodule.
Source: Stacks Project, Tags 0E67 and 0C1E; morphisms.tex, Tag 01TB
(blueprint: lem-sfb-smooth-derivation-zero-divisor).

Proof:
1. `lem-weil-pbc-closed-point-residue-field-base` makes the structural residue map bijective.
2. `lem-trf-affine-chart-stalk-differentials` and differential localization identify the
   stalk differentials with the differentials of the local ring, preserving d on fractions.
3. A uniformizer t has dt as basis by `lem-a1-uniformizer-differential-basis`. In the dual
   basis the coefficient is theta(dt) = D(t). Leibniz and m=(t) show preservation of m iff
   this coefficient belongs to m, equivalently the tangent section has zero fibre.
4. Away from q the point ideal is the whole stalk. Subsheaf membership is local, so this
   is exactly `curveVectorFieldsFixingPoints f {q}`, including the zero derivation. -/
theorem smooth_curve_derivation_fixes_iff (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (q : closedPoints X) :
    Function.Bijective (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ q.val trivial ≫ X.residue q.val).hom) ∧
    ∀ θ : f.relativeDifferentials ⟶ Scheme.Modules.unit X,
      θ ∈ curveVectorFieldsFixingPoints f {q.val} ↔
        TopCat.Presheaf.germ (Scheme.Modules.dual f.relativeDifferentials).val.presheaf
          ⊤ q.val trivial (smoothCurveTangentSection f θ) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk q.val) •
            (⊤ : Submodule (X.presheaf.stalk q.val)
              ((Scheme.Modules.dual f.relativeDifferentials).presheaf.stalk q.val)) := by
  sorry

/-- A nonzero derivation has an effective finite zero divisor of degree 2-2g, with its
basis-independent local orders, and each distinct fixed point contributes at least one.
Source: Stacks Project, curves.tex, Tag 0E67; divisors.tex, Tags 02SF, 02SG and 0BE6
(blueprint: lem-sfb-smooth-derivation-zero-divisor).

Proof:
1. Smooth connected curve local rings are integral and the closed stalks are DVRs
   (`lem-sc-smooth-connected-curve-local-rings`). A nonzero tangent section has nonzero
   generic germ: trivialize locally, use injectivity into the function field, then glue.
2. In any local basis write the germ as a times the basis vector. Its generic germ is
   nonzero, so a is nonzero. The DVR valuation is nonnegative; it is positive iff a is in
   the maximal ideal. Multiplication of the basis by a unit leaves its order unchanged.
3. `lem-sc-rational-section-order` gives finite support. The definition
   `def-sc-rational-section-divisor` gives coefficients equal to these orders, hence effectivity.
4. `lem-sc-line-bundle-rational-section` identifies O(Z) with the tangent sheaf by f maps to
   f times s. The degree homomorphism (`def-sc-pic0`) gives degree Z = degree T = 2-2g.
   Rationality of closed points makes this degree the unweighted sum of multiplicities.
5. The fixed-point/fibre calculation gives positive multiplicity exactly at fixed points.
   Positive integer coefficients are at least one, so any finite set of distinct fixed
   points has cardinality bounded by the sum, giving the last assertion. -/
theorem smooth_derivation_zero_divisor (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (θ : f.relativeDifferentials ⟶ Scheme.Modules.unit X) (hθ : θ ≠ 0) :
    ∃ hη : smoothCurveSectionGenericGerm k X f (Scheme.Modules.dual f.relativeDifferentials)
        (smoothCurveTangentSection f θ) ≠ 0,
      (∀ q : closedPoints X, 0 ≤ smoothCurveTangentZeroDivisor k X f θ hη q) ∧
      Set.Finite {q : closedPoints X | smoothCurveTangentZeroDivisor k X f θ hη q ≠ 0} ∧
      Nonempty (Scheme.Modules.dual f.relativeDifferentials ≅
        Scheme.Divisor.moduleOfSmoothConnectedCurve k X f
          (smoothCurveTangentZeroDivisor k X f θ hη)) ∧
      Scheme.Divisor.degree X (smoothCurveTangentZeroDivisor k X f θ hη) =
        (smoothCurveTangentZeroDivisor k X f θ hη).sum (fun _ m ↦ m) ∧
      Scheme.Divisor.degree X (smoothCurveTangentZeroDivisor k X f θ hη) =
        2 - 2 * (f.genus : ℤ) ∧
      (∀ (q : closedPoints X)
        (b : Module.Basis PUnit.{u + 1} (X.presheaf.stalk q.val)
          ((Scheme.Modules.dual f.relativeDifferentials).presheaf.stalk q.val)),
        ∃ a : X.presheaf.stalk q.val, a ≠ 0 ∧
          TopCat.Presheaf.germ (Scheme.Modules.dual f.relativeDifferentials).val.presheaf
            ⊤ q.val trivial (smoothCurveTangentSection f θ) = a • b PUnit.unit ∧
          smoothCurveTangentZeroDivisor k X f θ hη q =
            smoothCurveLocalCoefficientOrder k X f q a) ∧
      (∀ q : closedPoints X, 0 < smoothCurveTangentZeroDivisor k X f θ hη q ↔
        θ ∈ curveVectorFieldsFixingPoints f {q.val}) ∧
      (∀ q : closedPoints X, θ ∈ curveVectorFieldsFixingPoints f {q.val} →
        1 ≤ smoothCurveTangentZeroDivisor k X f θ hη q) ∧
      (∀ E : Finset (closedPoints X),
        (∀ q ∈ E, θ ∈ curveVectorFieldsFixingPoints f {q.val}) →
          (E.card : ℤ) ≤ 2 - 2 * (f.genus : ℤ)) := by
  sorry

end AlgebraicGeometry
