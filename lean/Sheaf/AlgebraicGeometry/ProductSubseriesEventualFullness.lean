module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.AlgebraicGeometry.FieldGlobalSections
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion
import Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-! # Eventual fullness of a product linear series

Source: Morrison, GIT Constructions of Moduli Spaces of Stable Curves and Maps,
Section 2.3, printed p.9, pointwise argument for equation (4); Stacks Tags
0E8S, 0B5T, 01XT, 0B5U, 0AYX, 0BS6.
(blueprint: lem-sfb-product-subseries-eventual-fullness)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Ordered products of sections, including the empty product one.
Source: Morrison Section 2.3, p.9, equation (4).
(blueprint: lem-sfb-product-subseries-eventual-fullness) -/
def seriesTensorProduct {C : Scheme.{u}} (L : C.Modules) :
    (n : ℕ) → (Fin n → Γ(L, ⊤)) → Γ(L.tensorPow n, ⊤)
  | 0, _ => unitSectionsEquiv ⊤ 1
  | n + 1, s => tmulSection (s 0) (seriesTensorProduct L n (fun i ↦ s i.succ))

/-- The line underlying the product subseries, with the indicated parenthesization.
Source: Morrison Section 2.3, p.9, equation (4).
(blueprint: lem-sfb-product-subseries-eventual-fullness) -/
abbrev productSeriesLine {C : Scheme.{u}} (L A B : C.Modules) (p l : ℕ) : C.Modules :=
  (L ⊗ A.tensorPow (p - l)) ⊗ B.tensorPow l

/-- The span of the actual products v u_1 ... u_(p-l) t_1 ... t_l.
Source: Morrison Section 2.3, p.9, equation (4).
(blueprint: lem-sfb-product-subseries-eventual-fullness) -/
def productSubseries (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] (L A B : C.Modules)
    (V : Submodule k (ProjectiveSpace.fieldSections k L))
    (U : Submodule k (ProjectiveSpace.fieldSections k A))
    (T : Submodule k (ProjectiveSpace.fieldSections k B)) (p l : ℕ) :
    Submodule k (ProjectiveSpace.fieldSections k (productSeriesLine L A B p l)) :=
  Submodule.span k {s | ∃ (v : V) (a : Fin (p - l) → U) (b : Fin l → T),
    s = tmulSection (tmulSection v.val
      (seriesTensorProduct A (p - l) (fun i ↦ (a i).val)))
      (seriesTensorProduct B l (fun i ↦ (b i).val))}

/-- Evaluation of all elements of a subspace, represented by the free-sheaf arrow.
Its being epi is equivalent to surjectivity of V tensor O_C to L; using all elements
rather than a basis does not change its image.
Source: Stacks Tag 01NE, generating sections.
(blueprint: lem-sfb-product-subseries-eventual-fullness) -/
def subseriesEvaluation (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] (L : C.Modules)
    (V : Submodule k (ProjectiveSpace.fieldSections k L)) :=
  L.freeHomEquiv.symm (fun v : V ↦
    L.unitHomEquiv (homOfGlobalSection L v.val))

/-- A basis of the subspace gives the canonical closed immersion into projective space.
Changing basis merely changes projective coordinates; the target is P(V dual).
Source: Stacks Tag 01NE and Morrison Section 2.3, p.9.
(blueprint: lem-sfb-product-subseries-eventual-fullness) -/
def IsEmbeddingSubseries (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] (L : C.Modules) [L.IsInvertible]
    (V : Submodule k (ProjectiveSpace.fieldSections k L)) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (b : Module.Basis I k V)
    (hs : Epi (L.freeHomEquiv.symm (fun i ↦
      L.unitHomEquiv (homOfGlobalSection L (b i).val)))),
    IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I (C ↘ Spec (.of k)) L
      (fun i ↦ L.unitHomEquiv (homOfGlobalSection L (b i).val)) hs)

/-- The product series generates its line, embeds the curve, and has full symmetric
powers eventually, with the Riemann--Roch dimension. The linear map is specified on
all pure symmetric tensors, which span its source and uniquely determine it.

Source: Morrison Section 2.3, printed p.9, pointwise argument for equation (4).
(blueprint: lem-sfb-product-subseries-eventual-fullness)

Proof:
1. Choose finite bases of V, U, T. At each point one section in each basis has nonzero
   fibre value. Their product is nonzero, including exponent zero via the unit section.
   Apply lem-weil-pbc-invertible-generating-sections-fibre and
   lem-weil-pbc-invertible-pullback-tensor. Products of the bases span S, so S is finite.
   Projectivity implies properness by lem-pc-projective-proper.
2. V separates points and tangent vectors because its morphism is a closed immersion.
   Multiply a separating section v by sections u,t nonzero at the required point.
   At a zero of v the derivative is u^(p-l)t^l dv, nonzero in any characteristic.
   Apply lem-sc-point-tangent-separation-closed-immersion to obtain the embedding by S,
   with pullback of O(1) equal to M and matching coordinate sections.
3. Apply lem-sfb-projective-polarization-section-algebra to this fixed embedding.
   Restriction of high twists is surjective. The coordinate-monomial description in
   lem-pc-projective-space-twist-cohomology, lem-pc-twist-tensor and the pullback-tensor
   comparison identify restriction with multiplication on Sym^n S. This constructs
   the specified linear map, including its values on every pure tensor.
4. Apply lem-weil-pbc-closed-immersion-serre-vanishing with F = O_C. Positive cohomology
   of M^n vanishes for large n, so h^0(M^n) = chi(M^n).
5. By lem-trf-curve-degree-tensor-additive, deg M = d+(p-l)a+lb and deg M^n = n deg M.
   The definition of degree gives chi(M^n) = n deg M + chi(O_C).
   lem-sc-riemann-roch gives chi(O_C) = 1-g. Take the maximum of 1 and the two bounds
   from steps 3 and 4. Surjectivity identifies the image dimension with h^0(M^n).
   This bound is chosen after fixing all data; it makes no uniformity assertion. -/
theorem product_subseries_eventual_fullness (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsConnectedCurve (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [IsHProjective (C ↘ Spec (.of k))]
    (L A B : C.Modules) [L.IsInvertible] [A.IsInvertible] [B.IsInvertible]
    (V : Submodule k (ProjectiveSpace.fieldSections k L))
    (U : Submodule k (ProjectiveSpace.fieldSections k A))
    (T : Submodule k (ProjectiveSpace.fieldSections k B))
    [FiniteDimensional k V] [FiniteDimensional k U] [FiniteDimensional k T]
    (hV : V ≠ ⊥) (hU : U ≠ ⊥) (hT : T ≠ ⊥)
    (hVe : Epi (subseriesEvaluation k L V))
    (hUe : Epi (subseriesEvaluation k A U))
    (hTe : Epi (subseriesEvaluation k B T))
    (hVemb : IsEmbeddingSubseries k L V) (p l : ℕ) (hl : l ≤ p) :
    Epi (subseriesEvaluation k (productSeriesLine L A B p l)
      (productSubseries k L A B V U T p l)) ∧
    IsEmbeddingSubseries k (productSeriesLine L A B p l)
      (productSubseries k L A B V U T p l) ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ μ : SymmetricPower k (ULift.{u} (Fin n)) (productSubseries k L A B V U T p l) →ₗ[k]
        ProjectiveSpace.fieldSections k ((productSeriesLine L A B p l).tensorPow n),
        (∀ s : ULift.{u} (Fin n) → productSubseries k L A B V U T p l,
          μ (SymmetricPower.tprod k s) =
            seriesTensorProduct (productSeriesLine L A B p l) n (fun i ↦ (s ⟨i⟩).val)) ∧
        Function.Surjective μ ∧
        (Module.finrank k (LinearMap.range μ) : ℤ) =
          (n : ℤ) * (L.degree k + ((p - l : ℕ) : ℤ) * A.degree k + (l : ℤ) * B.degree k) +
            1 - (C.arithmeticGenus k : ℤ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
