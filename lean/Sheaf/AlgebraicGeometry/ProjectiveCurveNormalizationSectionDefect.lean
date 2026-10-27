module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.UniformProjectiveFibreVanishing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Quotient.Basic

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CurveNormalizationCoherentSupport
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-! # Bounded section defect under componentwise normalization

Source: Stacks Project, varieties.tex, Tags 0BXR, 0C1R, 0AYT; coherent.tex,
Tag 0B3J; curves.tex, Tag 0BS6. The reduction sequence retains finite embedded nilpotents.
(blueprint: lem-sfb-projective-curve-normalization-section-defect)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveCurveNormalizationSectionDefect

/-- The specified normalization of the reduced component, with its existing construction.
Source: Stacks, Tag 0BXR
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
abbrev component (X : Scheme.{u}) (Z : irreducibleComponents X) : Scheme.{u} :=
  (X.reducedNormalizationComponent Z).normalization

/-- The canonical component map to X, including its possibly nonzero nilradical.
Source: Stacks, Tags 0BXR, 0C1R
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def componentMap (X : Scheme.{u}) (Z : irreducibleComponents X) : component X Z ⟶ X :=
  (X.reducedNormalizationComponent Z).fromNormalization ≫
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι

/-- The ambient hyperplane twist, restricted by the recorded tensor pullback.
Source: Stacks, Tag 01MT
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def twistOn {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (m : ℤ) : X.Modules :=
  (tensorPullback j).obj (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)) m)

/-- The canonical ambient power-to-twist identification, glued from standard chart bases.
Source: Stacks, Tags 01MT, 01CD
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def ambientPower (k : Type u) [Field k] (N : ℕ) :
    ∀ m : ℕ,
      (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)) 1).tensorPow m ≅
        ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)) (m : ℤ)
  | 0 => ProjectiveSpace.unitIsoTwistZero _ _
  | m + 1 => (Iso.refl _ ⊗ᵢ ambientPower k N m) ≪≫
      ProjectiveSpace.twistTensorIso _ _ 1 (m : ℤ) ≪≫
      eqToIso (congrArg (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)))
        (by omega : 1 + (m : ℤ) = ((m + 1 : ℕ) : ℤ)))

/-- The prescribed hyperplane line on a normalized reduced component.
Source: Stacks, Tags 0AYR, 0B5X
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def line {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (Z : irreducibleComponents X) :
    (component X Z).Modules :=
  (tensorPullback (componentMap X Z)).obj (twistOn j 1)

/-- The structural map used for the field action on each component's cohomology.
Source: Stacks, Tags 0BXR, 0AYR
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def componentStructure {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (Z : irreducibleComponents X) :
    component X Z ⟶ Spec (.of k) :=
  componentMap X Z ≫ j ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k))

/-- The recorded cohomological degree of A_i, with precisely its structural field action.
Source: Stacks, Tag 0AYR
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def componentDegree {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (Z : irreducibleComponents X) : ℤ :=
  letI : (component X Z).Over (Spec (.of k)) := ⟨componentStructure j Z⟩
  (line j Z).degree k

/-- H_m is the right-derived Zariski module cohomology H^0(X,O_X(m)).
Source: Stacks, Tag 01DZ
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
abbrev sourceSections {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (m : ℕ) : ModuleCat.{u} k :=
  UniformProjectiveFibreVanishing.cohomology k
    (j ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k))) (twistOn j m) 0

/-- T_i,m is the right-derived Zariski module cohomology H^0(E_i,A_i^m).
Source: Stacks, Tags 01DZ, 0BS6
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
abbrev componentSections {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (Z : irreducibleComponents X)
    (m : ℕ) : ModuleCat.{u} k :=
  UniformProjectiveFibreVanishing.cohomology k (componentStructure j Z)
    ((line j Z).tensorPow m) 0

/-- The canonical tensor identifications from nu_i^* O_X(m) to A_i^m.
Source: Stacks, Tags 01CD, 01MT
(blueprint: lem-sfb-projective-curve-normalization-section-defect). -/
def componentTwistIso {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (Z : irreducibleComponents X)
    (m : ℕ) :
    (tensorPullback (componentMap X Z)).obj (twistOn j m) ≅ (line j Z).tensorPow m :=
  (tensorPullback (componentMap X Z)).mapIso
    ((tensorPullback j).mapIso (ambientPower k N m).symm ≪≫
      boundaryPullbackPowIso j
        (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)) 1) m) ≪≫
    boundaryPullbackPowIso (componentMap X Z) (twistOn j 1) m

/-- Componentwise normalization has bounded section defect for a generically reduced
connected embedded projective curve. A finite product realizes the displayed finite direct
sum. The section equation fixes rho_m uniquely, including all low degrees.

Source: Stacks, varieties.tex, Tags 0BXR, 0C1R, 0AYT; coherent.tex, Tag 0B3J;
curves.tex, Tag 0BS6.
(blueprint: lem-sfb-projective-curve-normalization-section-defect)

Proof:
1. Projectivity makes X proper and Noetherian. Its finitely many reduced components are
integral and proper. A zero-dimensional component would be an open and closed singleton;
connectedness and dimension one exclude it. Normalize these one-dimensional components.
Their normalizations and their disjoint union are finite over X. Over the perfect field k
normal curves are smooth, and integral curves are connected. This is the normalized component
cover of lem-trf-proper-curve-normalized-component-cover and lem-sc-normalization-properties.
2. O_X(1) is ample and invertible. Restriction and finite pullback preserve ampleness, so
lem-trf-proper-integral-curve-ample-degree gives the positive component degrees e_i.
3. Let J be the nilradical. It is coherent and has zero stalk at every component generic
point by the given reduced-local-ring condition. The support of a coherent sheaf is closed;
a closed subset missing all these generic points on a dimension-one scheme has dimension
at most zero. In particular finite embedded nilpotents are allowed.
4. On D=X_red the normalization quotient Q in 0 -> O_D -> p_*O_E -> Q -> 0 is coherent
of finite support (lem-trf-curve-normalization-coherent-support). Tag 0AYT gives constant
h^0(J tensor L^m)=a and h^0(Q tensor L_D^m)=b, and H^1(J tensor L^m)=0. Proper coherent
cohomology makes a and b finite.
5. Tensor the reduction and normalization sequences by the invertible twists. The closed
immersion projection formula and the finite-map projection formula identify their sections
with H_m and the finite sum T_m. On a trivializing open the finite-map projection comparison
is the identity; thus the middle map is exactly the restriction and pullback characterized
below, using the normalized unit and the canonical tensor identifications.
6. Their long exact cohomology sequences give a surjection H_m -> H^0(D,L_D^m), followed
by an injection into T_m with cokernel a subspace of H^0(D,Q tensor L_D^m).
Consequently dim ker rho_m=a and dim coker rho_m<=b.
7. Coherent cohomology finiteness applies to H_m and all T_i,m. Put g_i=h^1(E_i,O_E_i).
Degree tensor additivity and large-degree Riemann--Roch give
h^0(E_i,A_i^m)=m e_i+1-g_i once m>=max(0,2g_i-1), since e_i is a positive integer.
The Euler-characteristic degree is the degree here by lem-sc-riemann-roch.
8. Set R=sum_i |1-g_i| and C=a+b+R. The finite-dimensional rank formula gives
|dim H_m-dim T_m|<=a+b. The component formulas and the triangle inequality give both
remaining errors <=C. Choose a common nonnegative threshold m0 for the finitely many
components. Both constants depend on this embedded X; no uniform bound is asserted. -/
theorem exists_bounded_section_defect
    {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) [IsClosedImmersion j]
    [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (hgeneric : ∀ (Z : irreducibleComponents X) (η : X), IsGenericPoint η Z.1 →
      _root_.IsReduced (X.presheaf.stalk η)) :
    IsFinite X.fromReducedNormalization ∧
      (∃ νred : X.reducedNormalization ⟶ X.nilradical.subscheme,
        νred ≫ X.nilradical.subschemeι = X.fromReducedNormalization) ∧
      ∃ (t : ℕ) (c : Fin t ≃ irreducibleComponents X),
        (∀ i : Fin t, IsConnectedCurve (componentStructure j (c i)) ∧
          Smooth (componentStructure j (c i)) ∧ IsProper (componentStructure j (c i)) ∧
          0 < componentDegree j (c i)) ∧
        ∃ ρ : ∀ m : ℕ, sourceSections j m →ₗ[k]
            (∀ i : Fin t, componentSections j (c i) m),
          (∀ (m : ℕ) (s : sourceSections j m) (i : Fin t),
            (UniformProjectiveFibreVanishing.zeroSections ((line j (c i)).tensorPow m)).hom
                (ρ m s i) =
              (componentTwistIso j (c i) m).hom.app ⊤
                (((tensorPullback (componentMap X (c i))).obj (twistOn j m)).presheaf.map
                  (eqToHom (by simp) :
                    op (componentMap X (c i) ⁻¹ᵁ (⊤ : X.Opens)) ⟶
                      op (⊤ : (component X (c i)).Opens))
                  ((((tensorPullbackSectionAdjunction (componentMap X (c i))).unit.app
                    (twistOn j m)).app ⊤
                    ((UniformProjectiveFibreVanishing.zeroSections (twistOn j m)).hom s))))) ∧
          ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
            Module.Finite k (sourceSections j m) ∧
            (∀ i : Fin t, Module.Finite k (componentSections j (c i) m)) ∧
            Module.finrank k (LinearMap.ker (ρ m)) ≤ C ∧
            Module.finrank k ((∀ i : Fin t, componentSections j (c i) m) ⧸
              LinearMap.range (ρ m)) ≤ C ∧
            (∀ i : Fin t,
              |(Module.finrank k (componentSections j (c i) m) : ℤ) -
                (m : ℤ) * componentDegree j (c i)| ≤ (C : ℤ)) ∧
            (|(Module.finrank k (sourceSections j m) : ℤ) -
              (m : ℤ) * ∑ i : Fin t, componentDegree j (c i)| ≤ (C : ℤ)) := by
  sorry

end AlgebraicGeometry.ProjectiveCurveNormalizationSectionDefect
