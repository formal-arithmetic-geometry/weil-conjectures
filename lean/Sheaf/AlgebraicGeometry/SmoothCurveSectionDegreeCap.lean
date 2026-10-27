module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.RationalSectionDivisor
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.AlgebraicGeometry.DivisorModuleTensorAdd
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import Sheaf.AlgebraicGeometry.CartierDivisorFinite
import Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-! # Degree and dimension of sections with prescribed vanishing

Source: Stacks Project, Curves, Tag 0CCS, `lemma-grd-inequalities`; Varieties,
Tags 0AYX and 0AYY (blueprint: lem-sfb-smooth-curve-section-degree-cap).

The helpers spell out the tensor/divisor twist, the generic germ of a global section,
and the order condition, using the recorded divisor and rational-section constructions.
The theorem identifies the image of the twisted section space and gives its degree,
finite dimensionality, dimension bound, and vanishing in negative degree.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual module `A^{⊗m}(-qB)`, using the existing divisor module construction.
Source: Stacks Project, Divisors, Tag 0BE9; Varieties, Tags 0AYX and 0AYY
(blueprint: lem-sfb-smooth-curve-section-degree-cap). -/
noncomputable def smoothCurveVanishingTwist
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (A : C.Modules) (B : C.Divisor) (m q : ℕ) : C.Modules :=
  A.tensorPow m ⊗ (-(q • B)).moduleOfSmoothConnectedCurve k C f

/-- The prescribed twisted section space, using the recorded module cohomology functor
and its canonical scalar restriction along the structure morphism of the curve.
Source: Stacks Project, Cohomology, Tag 01DZ; Curves, Tag 0CCS
(blueprint: lem-sfb-smooth-curve-section-degree-cap). -/
noncomputable def smoothCurveVanishingSections
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsConnectedCurve (C ↘ Spec (.of k))]
    [Smooth (C ↘ Spec (.of k))] (A : C.Modules) (B : C.Divisor) (m q : ℕ) :
    ModuleCat.{u} k :=
  ((RingedSpace.moduleCohomology C.toRingedSpace 0 ⋙
    ModuleCat.restrictScalars (globalSectionsRingHom k (X := C))).obj
      (smoothCurveVanishingTwist k C (C ↘ Spec (.of k)) A B m q))

/-- The canonical germ of a global section in the existing rational-section stalk.
Integrality is obtained from the recorded smooth-connected-curve theorem.
Source: Stacks Project, Divisors, Tag 01X5 (2)
(blueprint: lem-sfb-smooth-curve-section-degree-cap). -/
noncomputable def smoothCurveSectionGerm
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) (s : Γ(L, ⊤)) : rationalSection k C f L :=
  letI := Classical.choose (C.smooth_connected_curve_local_rings k f)
  TopCat.Presheaf.germ L.val.presheaf ⊤ (genericPoint C) trivial s

/-- Prescribed vanishing of a global section: its nonzero generic germ has order
at least `q * B P` at every closed point `P`. The zero germ satisfies this condition.
On a smooth connected curve the generic germ is zero exactly for the zero section.
Source: Stacks Project, Divisors, Tags 02SF and 0BE9
(blueprint: lem-sfb-smooth-curve-section-degree-cap). -/
def smoothCurveSectionVanishes
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) [L.IsInvertible] (B : C.Divisor) (q : ℕ) (s : Γ(L, ⊤)) : Prop :=
  ∀ (hs : smoothCurveSectionGerm k C f L s ≠ 0) (P : closedPoints C),
    (q : ℤ) * B P ≤
      rationalSectionOrder k C f L ⟨smoothCurveSectionGerm k C f L s, hs⟩ P

/-- Sections of `A^{⊗m}` with order at least `q B(P)` are precisely the image of
`H⁰(C,A^{⊗m}(-qB))`. This space is finite dimensional, has degree `m deg A - q deg B`,
and has dimension at most `max (m deg A - q deg B + 1) 0`, with the maximum in `ℤ`.
In negative degree the section space is zero. No positivity of `m`, `q`, or `B` is required.

Source: Stacks Project, Curves, Tag 0CCS, `lemma-grd-inequalities`; Varieties,
Tags 0AYX and 0AYY (blueprint: lem-sfb-smooth-curve-section-degree-cap).

Proof:
1. Put L = A^{⊗m} ⊗ O(-qB). By lem-sc-divisor-module-local its stalk at a closed
   point P is t^{q B(P)} times the stalk of A^{⊗m}. The divisor module therefore
   includes into A^{⊗m}, and its sections are exactly the specified order conditions,
   including zero. Identify H⁰ with global sections (def-sc-ringed-space-module-cohomology).
   Tensor invertibility follows from lem-pc-tensor-dual-invertible.
2. The unit has degree zero by def-pc-degree-line-bundle. Tensor-degree additivity
   (lem-trf-curve-degree-tensor-additive) gives deg(A^{⊗m}) = m deg A by induction.
   By lem-pc-degree-agrees-sc the degree of O(qB) is q deg B. Apply
   lem-sc-divisor-module-tensor-add to O(-qB) tensor O(qB) = O(0) to get the
   negative twist degree. Thus deg L = m deg A - q deg B, including all zero cases.
3. Properness over a field makes the curve Noetherian and invertible modules coherent
   (lem-trf-proper-field-invertible-coherent). Proper coherent cohomology
   (lem-pc-coherent-hi) gives finite dimensionality of H⁰(C,L).
4. If s is nonzero, integrality follows from lem-sc-smooth-connected-curve-local-rings.
   By lem-pc-nonzero-section-integral-cartier its zero scheme D is effective Cartier.
   Then L is isomorphic to O(D) by lem-pc-zero-scheme-divisor-iso, and D is finite
   over k by lem-pc-cartier-divisor-finite-over-field, also when D is empty.
5. The restriction of L to D is invertible. By lem-sfb-finite-trivialize-invertible-upstairs
   it is trivial, since the only neighbourhood of the point of Spec k is Spec k.
   By lem-pc-degree-base-change, dim Γ(D,L|D) = dim Γ(D,O_D) = deg L = d, so d ≥ 0.
6. Locally multiplication by s gives 0 → R → Re → (R/(a))e → 0 with a a
   nonzerodivisor, hence globally 0 → O_C → L → i_*(L|D) → 0. Global sections
   are left exact by lem-sc-global-sections-left-exact, and Γ(C,O_C) = k by
   lem-sc-global-functions. Thus 0 → k → H⁰(C,L) → Γ(D,L|D) is exact, without
   asserting surjectivity on the right. A basis of the kernel and lifts of a basis of
   the image give dim H⁰(C,L) ≤ 1+d.
7. If there is no nonzero section its dimension is zero. Otherwise d ≥ 0 and the
   preceding inequality is the required maximum bound. Negative d excludes a nonzero
   section. Substitute the degree formula from step 2.
-/
theorem smoothCurve_section_degree_cap
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsConnectedCurve (C ↘ Spec (.of k))]
    [Smooth (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    (A : C.Modules) [A.IsInvertible] (B : C.Divisor)
    (hB : ∀ P : closedPoints C, 0 ≤ B P) (m q : ℕ) :
    (∃ j : smoothCurveVanishingSections k C A B m q →ₗ[k]
        ((RingedSpace.globalSectionsFunctor C.toRingedSpace ⋙
          ModuleCat.restrictScalars (globalSectionsRingHom k (X := C))).obj
            (A.tensorPow m)),
      Function.Injective j ∧ ∀ s : Γ(A.tensorPow m, ⊤),
        s ∈ Set.range j ↔
          smoothCurveSectionVanishes k C (C ↘ Spec (.of k)) (A.tensorPow m) B q s) ∧
    FiniteDimensional k (smoothCurveVanishingSections k C A B m q) ∧
    (smoothCurveVanishingTwist k C (C ↘ Spec (.of k)) A B m q).degree k =
      (m : ℤ) * A.degree k - (q : ℤ) * Divisor.degree C B ∧
    (Module.finrank k (smoothCurveVanishingSections k C A B m q) : ℤ) ≤
      max ((m : ℤ) * A.degree k - (q : ℤ) * Divisor.degree C B + 1) 0 ∧
    ((m : ℤ) * A.degree k - (q : ℤ) * Divisor.degree C B < 0 →
      Subsingleton (smoothCurveVanishingSections k C A B m q)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
