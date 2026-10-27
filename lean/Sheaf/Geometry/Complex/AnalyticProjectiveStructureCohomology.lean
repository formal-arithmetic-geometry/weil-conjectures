module

public import Sheaf.Geometry.Complex.ProjectiveHolomorphicModule
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.CategoryTheory.RingedAcyclicResolutionDerivedMaps
import Sheaf.Analysis.Complex.HartogsPuncturedAffineExtension
import Sheaf.Paper.HermitianDolbeaultOrthogonalDecomposition
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # Analytic structure-sheaf cohomology of complex projective space

Source: Serre, Géométrie algébrique et géométrie analytique, no. 13, Lemma 4,
printed pp.20--21 (blueprint: lem-sfb-analytic-projective-structure-cohomology).

The coefficient ringed space has the constant complex ring sheaf, rather than the
holomorphic structure sheaf. Thus `moduleCohomology` computes the derived global sections
in sheaves of complex vector spaces, as requested by the node.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace ComplexGeometry

/-- Global holomorphic functions on analytic projective space are unique constants,
and its holomorphic module has zero positive cohomology, including dimension zero.
Source: Serre, GAGA, no. 13, Lemma 4, printed pp.20--21
(blueprint: lem-sfb-analytic-projective-structure-cohomology).

Proof plan, retaining the six DAG steps:
1. The standard projective charts have compact Kähler geometry by
   lem-sfb-analytic-projective-kahler-geometry. On the open site, the constant complex
   ring has enough injective module sheaves by
   lem-sc-ringed-space-module-sheaves-enough-injectives. Apply
   lem-sfb-dolbeault-acyclic-resolution with p=0 and the identity case of
   lem-sfb-ringed-acyclic-resolution-derived-maps: module cohomology is the quotient
   of closed smooth (0,q)-forms by exact ones, in the same coefficient category.
2. For n>0 pull a holomorphic function back to punctured complex (n+1)-space.
   Chart ratios are analytic by lem-sfb-complex-analytic-function-operations.
   Hartogs extension (lem-sfb-hartogs-punctured-affine-extension) gives an entire F.
   The equality F(tz)=F(z), t>0, and continuity at zero give F(z)=F(0).
   Quotient surjectivity gives constancy; evaluation at [1:0:...:0] gives uniqueness.
3. For a holomorphic r-form, 1≤r≤n, expand its punctured-affine pullback coefficients.
   The chart derivative formulas of lem-sfb-complex-analytic-derivative-rules and the
   analytic operations lemma make the coefficients holomorphic. Extend them by Hartogs.
   Homogeneity gives t^r B_I(tz)=B_I(z), so continuity at zero forces them to vanish.
   Pull back by the standard local sections to obtain vanishing of the original form.
4. For 1≤q≤n, lem-sfb-hermitian-dolbeault-orthogonal-decomposition writes a closed
   (0,q)-form as h+dbar u+dbar* v. Pairing the harmonic equation with h gives dbar h=0.
   The closed residual w=dbar* v has squared norm <dbar w,v>=0, hence is zero.
   Zero norm implies zero smooth form because metric volume is positive on open sets.
5. The identity in lem-sfb-kahler-laplacian-identity makes h d-harmonic, hence closed.
   Conjugation produces a closed (q,0)-form. Its dbar component vanishes, so Dolbeault
   exactness makes it holomorphic. Step 3 kills this form and hence h. The comparison
   of step 1 then gives the stated module-cohomology vanishing.
6. For q>n the (0,q)-form space is zero. For n=0 projective space is one point,
   holomorphic functions are complex constants and positive-degree forms are zero;
   the same acyclic-resolution comparison proves every positive cohomology vanishes. -/
theorem analytic_projective_structure_cohomology (n : ℕ)
    (P : ProjectiveHolomorphicModule.{u} n) :
    (∀ f : P.holomorphic.val.obj (op ⊤),
      ∃! c : ℂ, ∀ x : (⊤ : Opens P.coefficients), P.eval ⊤ f x = c) ∧
    (∀ q : ℕ, 0 < q →
      IsZero ((AlgebraicGeometry.RingedSpace.moduleCohomology P.coefficients q).obj
        P.holomorphic)) := by
  sorry

end ComplexGeometry
