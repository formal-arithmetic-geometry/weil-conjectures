/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
import WeilConjectures.AlgebraicGeometry.TateTwistLocallyFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.LineUnboundedDerivedTensor
import WeilConjectures.AlgebraicGeometry.WfTateTwistCompatibility
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
import WeilConjectures.AlgebraicGeometry.AmbRootTowerPullbackCoherence
import WeilConjectures.LinearAlgebra.FrobeniusModuleWeights

/-! # Weight shift under a Tate twist

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
lem-tw-tate-twist-weight-shift.md (blueprint: lem-tw-tate-twist-weight-shift).

The ordinary twist below assembles the existing signed coefficient line and its
root-normalized Weil map. Weights use the ordinary condensed local-return predicates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedWeil

/-- Assemble tensor Weil data through the inverse strong-monoidal tensorator.
Source: latest blueprint, lem-tw-tate-twist-weight-shift, tensor Weil structure
(blueprint: lem-tw-tate-twist-weight-shift). -/
def tensorPair {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P : C ⥤ C) [P.Monoidal] (M N : CategoryTheory.Endofunctor.IsoAlgebra P) :
    CategoryTheory.Endofunctor.IsoAlgebra P :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (M.carrier ⊗ N.carrier)
    ((Functor.Monoidal.μIso P M.carrier N.carrier).symm ≪≫ tensorIso M.str N.str)

/-- The signed Tate line with its root-normalized ordinary Weil structure.
Source: latest blueprint, Tate normalization in sk-def-sf-weil-complexes
(blueprint: lem-tw-tate-twist-weight-shift). -/
def tatePair (l : ℕ) [Fact l.Prime] (c : PurityTransport.Coefficient l)
    {T : Scheme.{u}} (g : T ≅ T) [∀ x : T, Invertible (l : T.residueField x)]
    (n : ℤ) : CategoryTheory.Endofunctor.IsoAlgebra (CondensedRing.upperStar (c.obj l) g.hom) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    (CondensedRing.StrictWeil.tateLine l c T n) (CondensedRing.StrictWeil.tatePull l c g n)

/-- The degree-zero Tate twist with its specified Weil structure. Its carrier is ordinary
sheaf tensor with the existing signed Tate line. Frobenius first uses the inverse tensorator,
then the input Weil map and the root-normalized Tate map; negative lines use the sheaf dual.
Source: latest blueprint, lem-tw-tate-twist-weight-shift, first proof paragraph, and
sk-def-sf-weil-complexes, Tate normalization
(blueprint: lem-tw-tate-twist-weight-shift). -/
@[irreducible] def tateTwist (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : WeilModule D l X₀) (n : ℤ) : WeilModule D l X₀ :=
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  tensorPair
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    M (tatePair l .closure (D.geometricFrobenius X₀) n)

/-- Tate twisting shifts punctual purity and mixed upper weight bounds by minus twice
its integer exponent, for a lisse Weil sheaf.
Source: latest blueprint, lem-tw-tate-twist-weight-shift
(blueprint: lem-tw-tate-twist-weight-shift).

Proof:
1. The Tate line is locally free of rank one for every integer exponent
   (det-def-sp-tate-twist-locally-free), including negative exponents by sheaf duality.
   Tensor with it is an additive exact equivalence by
   lem-pur-sheaf-line-evaluation-inverse-pair. Its derived degree-zero value agrees with
   ordinary tensor by lem-pur-line-unbounded-derived-tensor. The tensor Weil map is
   the prescribed one (lem-wf-tate-twist-compatibility). Kernels and cokernels of Weil
   modules are computed on their carriers. Restriction and Cartesian Tate comparison
   (lem-sfb-localized-site-tensor-restriction, det-prop-sfb-cartesian-coefficients-twists)
   show that this tensor preserves lisseness and constructibility; use the finite
   stratification characterization of sk-lem-coefficient-heart.
2. At a closed point of degree m, restrict to an affine neighbourhood over the base
   finite field. The tensor fibre comparison of lem-fd-condensed-fibre-linear-operations
   identifies the local operator with the tensor of the two local operators. Cartesian
   Tate comparison identifies the point line with the actual coefficient Tate line.
   Compatible primitive roots trivialize its finite stages, limits, scalar extensions,
   powers and duals (def-coefficient-twists-detailed); the coefficient unit evaluates
   to Qbar_l (det-pe-condensed-point-coefficients). Its degree-one operator is q^(-n)
   (def-weil-frobenius-coefficient-twists). The iterate-and-return construction
   (def-weil-local-frobenius-trace) makes the degree-m operator q^(-mn).
   Root pullback coherence (lem-amb-root-tower-pullback-coherence) identifies the
   Cartesian map with the specified point Weil map. A basis of the Tate fibre therefore
   identifies the twisted operator with q^(-mn) times the original one.
3. A nonzero scalar c rescales eigenvalues by alpha to c alpha, directly by the
   eigenvector equation (def-weil-frobenius-module-weights), without semisimplicity.
   Here c=q^(-mn), q_y=q^m, and every field embedding fixes rational scalars. Thus
   |iota(c alpha)|=q^(-mn) q_y^(w/2)=q_y^((w-2n)/2), as required by
   def-weil-punctual-weights. This calculation also applies to constructible pure
   sheaves which are not globally lisse.
4. For mixedness take the finite constructible Weil filtration in
   def-weil-punctual-weights. Exact tensor carries each quotient of weight v to its
   twist, pure of weight v-2n by steps 2--3. These weights are at most w-2n.
   The resulting finite filtration proves mixedness. A filtration of length zero
   remains the zero filtration after tensoring.
-/
theorem tateTwist_weight_shift (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : WeilModule D l X₀)
    (_hLisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (n : ℤ) :
    (Pure D l X₀ M iota w → Pure D l X₀ (tateTwist D l hl X₀ M n) iota (w - 2 * n)) ∧
    (Mixed D l X₀ M iota w → Mixed D l X₀ (tateTwist D l hl X₀ M n) iota (w - 2 * n)) := by
  sorry

end WeilConjectures.CondensedWeil
