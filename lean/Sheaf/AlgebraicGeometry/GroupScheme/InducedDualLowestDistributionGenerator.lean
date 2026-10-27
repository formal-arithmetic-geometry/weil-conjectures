/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Polynomial.Coeff
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # The lowest distribution generator of a dual induced module

Source: Mathieu, Tilting Modules and their Applications (2000), Section 2,
Lemma 2.1 and the start of the proof of Lemma 2.3, printed pp.153--155.
(blueprint: lem-sfb-induced-dual-lowest-distribution-generator)

The module is the actual space of global sections of the associated character
line bundle. Its coaction is fixed by left translation through the specified
pullback coordinate. Distributions are the finite-order part of the existing
convolution dual; no factorials in the coefficient field are inverted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.InducedDualLowest

/-- The union of the duals of F[U]/m^(r+1), embedded in the full convolution dual.
Here m is the kernel of the canonical coordinate counit. Multiplication and the
unit are the existing convolution product and counit on WithConv of the dual.
Source: Mathieu, Section 1, pp.150--152, and Section 2, p.155.
(blueprint: lem-sfb-induced-dual-lowest-distribution-generator). -/
def distributions {F : Type u} [Field F]
    (U : Grp (Over (Spec (.of F)))) [IsAffine U.X.left] :
    Set (WithConv (Module.Dual F (RationalHighestWeight.coordinateAlgebra U))) :=
  {a | ∃ r : ℕ, ∀ f ∈
    RingHom.ker (Bialgebra.counitAlgHom F
      (RationalHighestWeight.coordinateAlgebra U)).toRingHom ^ (r + 1), a.ofConv f = 0}

/-- Contract a rational coaction with a distribution: (1 tensor a)c.
Source: Mathieu, Section 2, p.152, structural-map description of the hyperalgebra action.
(blueprint: lem-sfb-induced-dual-lowest-distribution-generator). -/
def distributionAction {F : Type u} [Field F]
    {U : Grp (Over (Spec (.of F)))} [IsAffine U.X.left]
    {V : Type v} [AddCommGroup V] [Module F V]
    (c : V →ₗ[F] V ⊗[F] RationalHighestWeight.coordinateAlgebra U)
    (a : WithConv (Module.Dual F (RationalHighestWeight.coordinateAlgebra U))) :
    V →ₗ[F] V :=
  (TensorProduct.rid F V).toLinearMap ∘ₗ a.ofConv.lTensor V ∘ₗ c

/-- Evaluate coordinate functions with the canonical affine Hopf scalar structure.
The affine Spec--Gamma isomorphism is over F. The inverse of the existing
Spec.mapMulEquiv returns the actual F-algebra map attached to the point.
Source: Milne, Section 3a and Section 2, p.152.
(blueprint: lem-sfb-induced-dual-lowest-distribution-generator). -/
def coordinateEvaluation {F : Type u} [Field F]
    {S : Grp (Over (Spec (.of F)))} [IsAffine S.X.left]
    {A : Type u} [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ S.X) :
    RationalHighestWeight.coordinateAlgebra S →ₐ[F] A :=
  ((Spec.mapMulEquiv (R := F)
    (S := RationalHighestWeight.coordinateAlgebra S) (T := A)).symm
      ((s.left ≫ S.X.left.isoSpec.hom).asOver (Spec (.of F)))).ofConv

/-- The nth root distribution, obtained by polynomial coefficient extraction along x.
The universal additive point has parameter X, so this is exactly [t^n]x* f.
Source: Mathieu, Section 1, divided powers, pp.150--151; Section 2, p.155.
(blueprint: lem-sfb-induced-dual-lowest-distribution-generator). -/
def rootDistribution {F : Type u} [Field F]
    {U : Grp (Over (Spec (.of F)))} [IsAffine U.X.left]
    (x : Grp.mk (StandardGroupSchemes.additive F) ⟶ U) (n : ℕ) :
    WithConv (Module.Dual F (RationalHighestWeight.coordinateAlgebra U)) :=
  WithConv.toConv ((Polynomial.lcoeff F n) ∘ₗ
    (coordinateEvaluation
      (TorusCharacterTangent.additiveParameterPoint F (Polynomial.X : Polynomial F) ≫
        x.hom.hom)).toLinearMap)

/-- A dominant induced module is nonzero and finite-dimensional. Its actual dual,
with the canonical contragredient coaction, has a nonzero vector of character -eta
which generates under all finite-order distributions and is killed by the simple
root divided powers of orders above the corresponding integral coroot pairing.

The automorphism e is conjugation by n inverse, where n represents the longest
Weyl element. Its root-reversal equation is the characterization supplied by
lem-sfb-rho-regular-weyl-orbit. Thus line is L_(w0 eta) = M_(-w0 eta).

Source: Mathieu, Section 2, Lemma 2.1 and proof of Lemma 2.3, pp.153--155.
(blueprint: lem-sfb-induced-dual-lowest-distribution-generator).

Proof plan (the DAG's eight steps):
1. Set mu = -w0 eta. Opposition permutes the simple roots and coroots by
   lem-sfb-rho-regular-weyl-orbit and lem-sfb-reductive-rank-one-reflections.
   The fundamental-weight expansion from lem-sfb-simply-connected-character-lattice
   and lem-sfb-fundamental-flag-boundary-sections give a product section nonzero at nB.
2. The flag quotient is proper and the associated line sheaf coherent by
   lem-sfb-reductive-borel-pair-structure and lem-sfb-homogeneous-line-bundle-sections.
   Apply lem-pc-coherent-hi in degree zero over F. The regular-function comparison
   supplies the rational left-translation coaction; inverse transpose gives its dual.
3. Take w(v) = f_v(n). It is nonzero by step 1. On every F-algebra,
   (tw)(v) = f_v(tn) = mu(n inverse t n)f_v(n) = (-eta)(t)w(v).
4. By lem-sfb-bruhat-longest-cell-charts, u to unB is a dense affine cell.
   The map v to P_v(u) = f_v(un) is injective, since S is integral, and P_v is
   exactly the matrix coefficient (uw)(v).
5. Every coefficient functional on the polynomial coordinates of U kills a power
   of its augmentation ideal. A vector annihilating all distributions applied to w
   therefore has every coefficient of P_v zero. Injectivity and finite-dimensional
   duality imply that the span of all aw is the whole dual.
6. For alpha_j = -w0 alpha_i, root-subgroup uniqueness identifies n inverse x_i n
   with a scalar reparametrization of the negative root in the rank-one SL2 map
   of lem-sfb-opposite-root-sl2-parametrizations. Use
   lem-sfb-unipotent-root-intersection-products to put its positive root in B.
   The projection to T of its diagonal is alpha_j coroot.
7. The semi-invariance on SL2 has exponent d = <mu,alpha_j coroot> = m_i.
   For g_x = [[x,-1],[1,0]], the identity
   I + z E21 = g_(1/z) diag(z,1/z) (I + z inverse E12)
   gives P(z) = z^d R(1/z) in F[z,z inverse]. Hence deg P is at most m_i.
   Coefficients of order n > m_i vanish, giving exactly the displayed relations.
   No factorial division and no condition m_i < p occurs.
8. For S = 1 the root index is empty, the associated bundle is trivial, and
   sections, dual and distributions are F. The empty product section is 1.
   For eta = 0 the same product is 1 and every simple-root degree bound is zero. -/
theorem induced_dual_lowest_distribution_generator
    {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (S T B U : Grp (Over (Spec (.of F))))
    [IsAffine S.X.left] [IsAffine T.X.left] [IsAffine U.X.left]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (jT : T ⟶ B) (iU : U ⟶ B)
    (hTB : jT ≫ iB = iT)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom)
    (hU : IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ U, f ≫ iU = iN)
    (pT : B ⟶ T) (hpT : jT ≫ pT = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit U.X) pT.hom.hom η[T.X])
    (hBT : IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ jT.hom.hom)))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    [ModObj T.X S.X] [ModObj T.X B.X]
    (hconjS : γ[T.X,S.X] = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (hconjB : γ[T.X,B.X] = (jT.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    [P.IsReduced] (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ TorusCharacterTangent.weightSpace T S χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      TorusCharacterTangent.weightSpace T B α.val.toMul ≠ ⊥)
    (x : b.support → (Grp.mk (StandardGroupSchemes.additive F) ⟶ U))
    (hx : ∀ i : b.support,
      IsClosedSubgroupScheme (x i ≫ iU ≫ iB).hom.hom ∧
      TorusCharacterTangent.IsStable T S (x i ≫ iU ≫ iB) ∧
      (GrpObj.differential (x i ≫ iU ≫ iB).hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T S i.val.val.toMul)
    (n : 𝟙_ (Over (Spec (.of F))) ⟶ S.X) (e : T ≅ T)
    (he : e.hom.hom.hom ≫ iT.hom.hom =
      (toUnit T.X ≫ n⁻¹) * iT.hom.hom * (toUnit T.X ≫ n))
    (hlongest :
      (fun α : Φ ↦ Additive.ofMul (e.hom ≫ α.val.toMul)) '' {α : Φ | b.IsPos α} =
        (fun α : Φ ↦ -α.val) '' {α : Φ | b.IsPos α})
    (eta : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hdominant : ∀ i : b.support, 0 ≤ P.toLinearMap eta (P.coroot i))
    (Q : Over (Spec (.of F))) (π : S.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hπf : Flat π.left) (hπs : Surjective π.left)
    (hπi : (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) ≫ π = fst S.X B.X ≫ π)
    (hπt : IsPullback (fst S.X B.X)
      (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) π π)
    (line : AssociatedCharacterLineBundle.Presentation S B iB Q π
      (pT ≫ e.hom ≫ eta.toMul))
    (eV : AssociatedCharacterLineBundle.sections Q line.L ≃ₗ[F]
      RhoSection.sectionModule S B iB ((pT ≫ e.hom ≫ eta.toMul)⁻¹) 1)
    (heV : ∀ v : AssociatedCharacterLineBundle.sections Q line.L,
      (eV v).val =
        AssociatedCharacterLineBundle.pullbackCoordinate π line.L line.trivialization v) :
    Nontrivial (AssociatedCharacterLineBundle.sections Q line.L) ∧
    FiniteDimensional F (AssociatedCharacterLineBundle.sections Q line.L) ∧
    ∃ (c : AssociatedCharacterLineBundle.sections Q line.L →ₗ[F]
        AssociatedCharacterLineBundle.sections Q line.L ⊗[F]
          RationalHighestWeight.coordinateAlgebra S)
      (d : Module.Dual F (AssociatedCharacterLineBundle.sections Q line.L) →ₗ[F]
        Module.Dual F (AssociatedCharacterLineBundle.sections Q line.L) ⊗[F]
          RationalHighestWeight.coordinateAlgebra S),
      HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra S) _ c ∧
      HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra S) _ c ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (s g : StandardGroupSchemes.affine F A ⟶ S.X)
        (v : AssociatedCharacterLineBundle.sections Q line.L),
        LinearMap.mul' F A
            (TensorProduct.map
              ((RhoSection.evaluate g).toLinearMap ∘ₗ
                (RhoSection.sectionModule S B iB
                  ((pT ≫ e.hom ≫ eta.toMul)⁻¹) 1).subtype ∘ₗ eV.toLinearMap)
              (coordinateEvaluation s).toLinearMap (c v)) =
          RhoSection.evaluate (s⁻¹ * g) (eV v).val) ∧
      HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra S) _ d ∧
      HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra S) _ d ∧
      RationalHighestWeight.IsContragredient c d ∧
      ∃ w : Module.Dual F (AssociatedCharacterLineBundle.sections Q line.L),
        w ≠ 0 ∧
        (RationalHighestWeight.coordinateMap iT).toLinearMap.lTensor _ (d w) =
          w ⊗ₜ[F] RationalHighestWeight.characterElement (-eta).toMul ∧
        Submodule.span F
          {z | ∃ a ∈ distributions U,
            z = distributionAction
              ((RationalHighestWeight.coordinateMap (iU ≫ iB)).toLinearMap.lTensor _ ∘ₗ d)
              a w} = ⊤ ∧
        ∀ (i : b.support) (k : ℕ), (P.toLinearMap eta (P.coroot i) : ℤ) < k →
          distributionAction
            ((RationalHighestWeight.coordinateMap (iU ≫ iB)).toLinearMap.lTensor _ ∘ₗ d)
            (rootDistribution (x i) k) w = 0 := by
  sorry

end AlgebraicGeometry.InducedDualLowest
