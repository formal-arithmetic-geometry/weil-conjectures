module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
public import Sheaf.AlgebraicGeometry.HilbertToPicardMorphism
public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocusDual
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.Paper.BoundaryCechCompatibility
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine

/-! # The differential of the pointed Abel morphism

Source: Milne, Abelian Varieties, III Proposition 2.1 and Theorem 5.1(b), pp.90–91,
101–103, with the local-equation refinement recorded in the DAG proof
(blueprint: lem-sfb-abel-differential-boundary).

The tangent modules below restrict the recorded residue-field tangent spaces to k.
The rational-point comparisons are specified on dual-number morphisms. The Picard
comparison is specified by the units retraction a+epsilon b ↦ a⁻¹b, and the Hilbert
comparison by the graph ideal (f+epsilon g). Thus the assertion compares maps.
`Modules.H` is the existing Ext model of the right-derived cohomology in
`pqf-def-cohomology`; `exists_moduleCohomology_source_comparison` supplies the comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Restriction of the recorded scheme tangent space along the structural residue map.
Source: Stacks 0B2C; Milne III 2.1 (blueprint: lem-sfb-abel-differential-boundary). -/
def abelDifferentialTangent (k : Type u) [Field k]
    (X : Over (Spec (.of k))) (x : X.left) : ModuleCat.{u} k :=
  letI : Module k (schemeTangentSpace k X.left X.hom x) :=
    Module.compHom _
      (StructureSheaf.toStalk k (X.hom x) ≫ X.hom.stalkMap x ≫ X.left.residue x).hom
  ModuleCat.of k (schemeTangentSpace k X.left X.hom x)

/-- The canonical coefficient change from k-dual numbers to residue-field dual numbers.
Source: Stacks 0B2C (blueprint: lem-sfb-abel-differential-boundary). -/
def abelDifferentialCoefficient (k : Type u) [Field k]
    (X : Over (Spec (.of k))) (x : X.left) :
    Spec (.of (DualNumber (X.left.residueField x))) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
    (StructureSheaf.toStalk k (X.hom x) ≫ X.hom.stalkMap x ≫ X.left.residue x).hom))

/-- The ideal of the divisor represented by a rational Hilbert point, transported from
C times Spec k to C. Source: Stacks 0B9I
(blueprint: lem-sfb-abel-differential-boundary). -/
def abelDifferentialDivisor {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (r : ℕ) (H : Over (Spec (.of k)))
    (eH : (hilbertPresheaf f r).RepresentableBy H)
    (d : 𝟙_ (Over (Spec (.of k))) ⟶ H) : C.IdealSheafData :=
  (eH.homEquiv d).val.comap (inv (pullback.fst f (𝟙 _)))

/-- The ideal of the infinitesimal divisor on C[epsilon], using the canonical pullback
square for the dual-number thickening. Source: Milne III 5.1(b), local equations
(blueprint: lem-sfb-abel-differential-boundary). -/
def abelDifferentialDeformation {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (r : ℕ) (H : Over (Spec (.of k)))
    (eH : (hilbertPresheaf f r).RepresentableBy H)
    (v : Scheme.dualNumbersOver (Spec (.of k)) ⟶ H) : C.dualNumbers.IdealSheafData :=
  (eH.homEquiv v).val.comap (Scheme.isPullback_dualNumbersProj f).isoPullback.hom

/-- The canonical inclusion O_C into O_C(D)=I_D dual, obtained by dualizing I_D into O_C.
Source: Milne III 5.1(b); Stacks 0B9I
(blueprint: lem-sfb-abel-differential-boundary). -/
def abelDifferentialInclusion {C : Scheme.{u}} (I : C.IdealSheafData) :
    Scheme.Modules.unit C ⟶ I.toModulesᵛ :=
  Scheme.Modules.dualUnitIso.inv ≫ Scheme.Modules.dualMap I.toModulesι

/-- The actual quotient sequence O_C into O_C(D) onto O_D(D), using the categorical
cokernel. Source: Milne III 5.1(b), local-equation refinement
(blueprint: lem-sfb-abel-differential-boundary). -/
def abelDifferentialSequence {C : Scheme.{u}} (I : C.IdealSheafData) :
    ShortComplex C.Modules :=
  ShortComplex.mk (abelDifferentialInclusion I) (cokernel.π (abelDifferentialInclusion I))
    (cokernel.condition (abelDifferentialInclusion I))

/-- The differential of the pointed Abel map is the boundary, up to one overall sign;
its kernel has dimension h0(O(D))-1.
Source: Milne III Proposition 2.1 and Theorem 5.1(b), pp.90–91, 101–103
(blueprint: lem-sfb-abel-differential-boundary).

Proof:
1. Projective-proper and smooth-connected-curve-local-rings give properness, integrality
   and Noetherianity. prop-pc-xk-integral gives geometric integrality. Hilbert-curves
   identifies degree-r Hilbert points with effective Cartier divisors, and
   divisor-line-bundle-agrees-sc identifies the dual ideal with the valuation module.
2. On a cover with I=(f), finite-embedded-dual-number-graphs identifies tangent
   deformations with Hom(I,O/I). The map h ↦ h(f)/f identifies this sheaf with O(D)/O.
   Changing f by a unit preserves the fraction; multiplication and two-parameter graphs
   give the scalar and addition laws, including the empty divisor.
3. A local lift q=g/f gives the graph equation f+epsilon g. The overlap equations have
   transition ratios 1+epsilon(q_j-q_i). Hilbert-to-pic-morphism on dual-number points
   gives this same invertible ideal dual. Translation cancels the fixed -rP twist.
   Split-thickening-picard-cocycle and the representing group isomorphism identify its
   class with the additive cocycle q_j-q_i, with one sign depending on frame order.
4. Boundary-cech-compatibility identifies this very cocycle with the connecting class.
   This proves equality of maps under the specified comparisons.
5. Closed-immersion-cokernel-cohomology gives the long exact sequence for O into O(D)
   onto O_D(D). Global-functions identifies its initial space with k. Substitution of
   the preceding comparisons gives the two exactness assertions; sign changes preserve
   the kernel.
6. Curve-coherent-finiteness makes H0(O(D)) finite dimensional. Its image has kernel
   the one-dimensional constants, so rank-nullity gives the displayed dimension.

N is the class O(-P); hN fixes it to the actual point ideal. The all-test-scheme
formula ha specifies the constructed Abel morphism, including infinitesimal points.
The rational tangent comparisons rho and rhoJ are fixed by coefficient change; tau
is fixed by translation; beta is fixed by the epsilon-part of the units torsor.
The final local graph formula fixes alpha, rather than allowing an arbitrary linear
identification with the same dimension. -/
theorem abelDifferential_boundary
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))]
    [IsConnectedCurve (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [IsHProjective (C ↘ Spec (.of k))]
    (P : Spec (.of k) ⟶ C) (hP : P ≫ (C ↘ Spec (.of k)) = 𝟙 _)
    (J : Over (Spec (.of k))) [GrpObj J]
    (hJ : @IsJacobian k _ C (C ↘ Spec (.of k)) _ _ _
      (@GeometricallyIntegral.of_isSepClosed k _ C inferInstance _ inferInstance
        (IsConnectedCurve.connectedSpace' (C ↘ Spec (.of k)))) J _)
    (eJ : (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj.RepresentableBy J)
    (heJ : IsPicardZeroMul (C ↘ Spec (.of k)) eJ)
    (N : C.Pic) (hN : Nonempty ((fromSkeleton C.Modules).obj N.val ≅ P.ker.toModules))
    (r : ℕ) (H : Over (Spec (.of k)))
    (eH : (hilbertPresheaf (C ↘ Spec (.of k)) r).RepresentableBy H)
    (a : H ⟶ J)
    (ha : ∀ (T : Over (Spec (.of k))) (z : T ⟶ H),
      ∃ (L : (pullback (C ↘ Spec (.of k)) T.hom).Pic)
        (hL : L * Scheme.Pic.map (pullback.fst (C ↘ Spec (.of k)) T.hom) (N ^ r) ∈
          (picardSubfunctorDegree (C ↘ Spec (.of k)) 0).obj (op T)),
        Nonempty ((fromSkeleton _).obj L.val ≅ (eH.homEquiv z).val.toModulesᵛ) ∧
        eJ.homEquiv (z ≫ a) =
          (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (C ↘ Spec (.of k)) 0).toFunctor).app (op T)
              ⟨L * Scheme.Pic.map (pullback.fst (C ↘ Spec (.of k)) T.hom) (N ^ r), hL⟩)
    (d : 𝟙_ (Over (Spec (.of k))) ⟶ H) :
    ∃ (rho : tangentSpaceAt H d ≃
        abelDifferentialTangent k H (d.left (IsLocalRing.closedPoint k)))
      (rhoJ : tangentSpaceAt J (d ≫ a) ≃
        abelDifferentialTangent k J ((d ≫ a).left (IsLocalRing.closedPoint k)))
      (da : abelDifferentialTangent k H (d.left (IsLocalRing.closedPoint k)) →ₗ[k]
        abelDifferentialTangent k J ((d ≫ a).left (IsLocalRing.closedPoint k)))
      (alpha : abelDifferentialTangent k H (d.left (IsLocalRing.closedPoint k)) ≃ₗ[k]
        (abelDifferentialSequence
          (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).X₃.H 0)
      (tau : abelDifferentialTangent k J ((d ≫ a).left (IsLocalRing.closedPoint k)) ≃ₗ[k]
        tangentSpaceAt J η[J])
      (beta : tangentSpaceAt J η[J] ≃ₗ[k] (Scheme.Modules.unit C).H 1)
      (hs : (abelDifferentialSequence
        (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).ShortExact),
      (∀ v : tangentSpaceAt H d,
        (rho v).val = abelDifferentialCoefficient k H (d.left (IsLocalRing.closedPoint k)) ≫
          inv (Scheme.dualNumbersToSpec (.of k)) ≫ v.val.left) ∧
      (∀ v : tangentSpaceAt J (d ≫ a),
        (rhoJ v).val =
          abelDifferentialCoefficient k J ((d ≫ a).left (IsLocalRing.closedPoint k)) ≫
            inv (Scheme.dualNumbersToSpec (.of k)) ≫ v.val.left) ∧
      (∀ v : tangentSpaceAt H d, da (rho v) = rhoJ ⟨v.val ≫ a,
        (Category.assoc _ _ _).symm.trans (congrArg (fun q ↦ q ≫ a) v.property)⟩) ∧
      (∀ v : tangentSpaceAt J (d ≫ a),
        (tau (rhoJ v)).val = v.val * (CartesianMonoidalCategory.toUnit _ ≫ (d ≫ a))⁻¹) ∧
      (∀ (v : tangentSpaceAt J η[J])
        (L : (pullback (C ↘ Spec (.of k))
          (Scheme.dualNumbersOver (Spec (.of k))).hom).Pic)
        (hL : L ∈ (picardSubfunctorDegree (C ↘ Spec (.of k)) 0).obj
          (op (Scheme.dualNumbersOver (Spec (.of k))))),
        eJ.homEquiv v.val =
          (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (C ↘ Spec (.of k)) 0).toFunctor).app
              (op (Scheme.dualNumbersOver (Spec (.of k)))) ⟨L, hL⟩ →
        beta v = Sheaf.H.map C.dualNumbersUnitsRetract 1
          (Scheme.Pic.toH1UnitsDualNumbers C (Scheme.Pic.map
            (Scheme.isPullback_dualNumbersProj (C ↘ Spec (.of k))).isoPullback.hom L))) ∧
      (∃ sign : ℤ, (sign = 1 ∨ sign = -1) ∧
        ∀ v, beta (tau (da v)) = sign • Scheme.Modules.H.δ hs 0 (alpha v)) ∧
      (∃ c : k →ₗ[k]
          (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d).toModulesᵛ.H 0,
        (∀ t : k, Scheme.Modules.H.zeroLinearEquiv _ (c t) =
          (abelDifferentialInclusion
            (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).app ⊤
              (Scheme.globalSectionsRingHom k t)) ∧
        Function.Injective c ∧
        Function.Exact c (fun z ↦ alpha.symm (Scheme.Modules.H.map
          (abelDifferentialSequence
            (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).g 0 z)) ∧
        Function.Exact (fun z ↦ alpha.symm (Scheme.Modules.H.map
          (abelDifferentialSequence
            (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).g 0 z)) da) ∧
      Module.finrank k (LinearMap.ker da) =
        Module.finrank k
          ((abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d).toModulesᵛ.H 0) - 1 ∧
      (∀ (v : tangentSpaceAt H d) (U : C.Opens)
        (s : (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d).toModules.val.obj (op U))
        (_hsfree : Scheme.Modules.IsFreeGenerator s)
        (t : (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d).toModulesᵛ.val.obj (op U)),
        (abelDifferentialSequence
          (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).g.app U t =
            (abelDifferentialSequence
              (abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d)).X₃.presheaf.map
                (homOfLE le_top).op
                  (Scheme.Modules.H.zeroLinearEquiv _ (alpha (rho v))) →
        (abelDifferentialDeformation (C ↘ Spec (.of k)) r H eH v.val).idealOfOpens U =
          Ideal.span {TrivSqZeroExt.inl
            ((abelDifferentialDivisor (C ↘ Spec (.of k)) r H eH d).toModulesι.app U s) +
              TrivSqZeroExt.inr (t.app (op (Over.mk (𝟙 U))) s)}) := by
  sorry

end AlgebraicGeometry
