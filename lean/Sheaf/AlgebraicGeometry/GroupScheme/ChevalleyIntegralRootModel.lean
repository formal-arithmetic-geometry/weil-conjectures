/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.Algebra.Lie.KostantIntegralPBW
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.Field.ULift
import Sheaf.LinearAlgebra.RootDatumLatticeEmbedding

/-! # An integral Chevalley model preserving a prescribed pinning

Source: Milne, Algebraic Groups (2017), Section 23h, pp.509--511, equation (153)
and the paragraph Reductive groups over Z; Theorem 23.40 and Corollary 23.41.
The integral positive-root chart is the integral counterpart of Theorem 21.68(a).
(blueprint: lem-sfb-chevalley-integral-root-model)

All integral schemes live over Spec of the universe lift of the integers. Base change
is the actual pullback functor on group objects. The additive group law on the integral
affine line is specified on every test scheme by addition of its coordinate sections.
The rational Lie algebra is the existing tangent Lie algebra, with scalar restriction
from the universe lift of the rationals specified explicitly.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.ChevalleyIntegralRootModel

/-- The integral base in the schemes' universe. Source: Milne, Section 23h, p.511
(blueprint: lem-sfb-chevalley-integral-root-model). -/
abbrev integerBase : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

/-- The unique scalar map from the lifted integers. Source: Milne, p.511
(blueprint: lem-sfb-chevalley-integral-root-model). -/
def integerMap (R : Type u) [CommRing R] : Spec (.of R) ⟶ integerBase.{u} :=
  Spec.map (CommRingCat.ofHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom))

/-- Affine coordinate space as an object over its base. Source: Milne, 21.68(a)
and Section 23h (blueprint: lem-sfb-chevalley-integral-root-model). -/
abbrev affineCoordinates (I : Type u) (S : Scheme.{u}) : Over S :=
  (AffineSpace I S).asOver S

/-- The morphism with prescribed coordinate sections. This uses Mathlib's canonical
coordinate construction, not a chosen map. Source: Milne, 21.68(a) and (153)
(blueprint: lem-sfb-chevalley-integral-root-model). -/
def coordinateArrow {S : Scheme.{u}} (I : Type u) (W : Over S)
    (a : I → Γ(W.left, ⊤)) : W ⟶ affineCoordinates I S :=
  Over.homMk (AffineSpace.homOfVector W.hom a) (AffineSpace.homOfVector_over W.hom a)

/-- The integral affine line. Source: Milne, equation (153)
(blueprint: lem-sfb-chevalley-integral-root-model). -/
abbrev integralLine : Over integerBase.{u} :=
  affineCoordinates PUnit.{u + 1} integerBase

/-- Canonical base change of group schemes from the integers. Source: Milne, p.511
(blueprint: lem-sfb-chevalley-integral-root-model). -/
def scalarChange (R : Type u) [CommRing R] :
    Grp (Over integerBase.{u}) ⥤ Grp (Over (Spec (.of R))) :=
  (Over.pullback (integerMap R)).mapGrp

/-- The coordinate projection of an ordered integral root chart. Source: the integral
counterpart of Milne, 21.68(a) (blueprint: lem-sfb-chevalley-integral-root-model). -/
def rootProjection (N : ℕ) (i : Fin N) :
    affineCoordinates (ULift.{u} (Fin N)) integerBase ⟶ integralLine.{u} :=
  coordinateArrow PUnit _ (fun _ ↦ AffineSpace.coord integerBase (ULift.up i))

/-- An integral root model exists with every labelled root immersion, the prescribed
simple-root pinning, an integral positive-root chart, and its normalized Chevalley
basis in the actual rational tangent Lie algebra.

Source: Milne, Algebraic Groups (2017), Section 23h, pp.509--511, equation (153),
Theorem 23.74, and Theorem 23.40 / Corollary 23.41 for the prescribed pinning.
(blueprint: lem-sfb-chevalley-integral-root-model)

Proof plan:
1. Use lem-sfb-simply-connected-character-lattice to identify X with the full weight
   lattice P, and lem-sfb-root-datum-lattice-embedding to remove the central summand.
   Apply lem-sfb-chevalley-admissible-representation to obtain a faithful representation
   and a weight-decomposed admissible lattice with all root divided powers integral.
2. Form the torus Spec Z[P] and the finite exponential root matrices (153). Apply
   lem-sfb-integral-chevalley-weyl-atlas to their rational closure. Polynomial identities
   descend from Q to the torsion-free integer coordinate rings, giving root homomorphisms.
3. By lem-weil-subgroup-finite-free-abelian-group-free choose bases of the weight
   summands. The weights generate P, so the torus is closed in the general linear group.
   The atlas consists of polynomial Laurent-polynomial charts; lifting variables and
   units through square-zero ideals gives smoothness by def-sbc-smooth-morphisms.
4. Over any algebraically closed field, lem-sfb-chevalley-root-exponential-group
   identifies the root-generated group with the base-changed closure: every atlas chart
   factors through that group, so its defining ideal vanishes on an open cover.
5. Choose a positive regular integral cocharacter separating the representation's
   weights. Conjugation grades the ordered positive-root product with positive degrees.
   Apply lem-sfb-chevalley-unipotent-polynomial-coordinates over algebraically closed fields.
6. Each graded target piece is finite free over Z. Its cokernel vanishes over Q and
   modulo every prime, hence is zero. Thus the integral positive-root product is closed
   and its image U has the specified affine chart.
7. Descend multiplication, inverse, identity and positive-root factorizations from Q
   through torsion-free polynomial rings. The torus normalizes this U.
8. In decreasing weight order, impose the upper block triangular equations and require
   g diag(g)^{-1} to lie in U, with diag(g) in T. This is a closed B isomorphic to U × T.
9. The semidirect formulas give B's group operations. Its T and U inclusions are closed;
   their polynomial Laurent-polynomial charts give smooth affine finite type schemes.
   Positive roots are chart coordinate axes; apply the negative construction for the
   negative roots. Hence every root homomorphism is a closed immersion.
10. Use lem-sfb-chevalley-exponential-big-cell, the recorded root parametrizations,
    lem-sfb-regular-cocharacter-borel-description and lem-sfb-borel-root-product-coordinates
    to identify the labelled root groups, Borel and unipotent radical in the special fibre.
11. Apply lem-sfb-root-datum-isogeny-realization with the identity weight lattice and
    root labels. It is an isomorphism; the simple root maps differ by nonzero scalars.
12. Clear denominators from P over Z Delta and take the required roots of those scalars
    in F. By lem-sfb-multiplicative-character-antiduality they come from a torus point.
    Conjugation corrects all simple-root scalars and preserves T, B, U and every root label.
13. Differentiate the identity atlas over Q. Its tangent is the direct sum of the torus
    tangent and the root lines. The linear term of each exponential is its root vector;
    on a weight block the torus tangent is evaluation at that weight. Faithfulness thus
    identifies this tangent with the original rational Lie algebra. For matrix coordinates
    D_A(X)=XA, so the left-invariant commutator is the matrix bracket AB-BA.
14. The simple coroot derivative acts by its integral weight pairing. The resulting basis
    has exactly the opposite-root and root-string constants in lem-sfb-kostant-integral-pbw.
    The integral chart sends zero to the identity. If there are no roots, P=0, the entire
    construction consists of trivial group schemes and the zero tangent Lie algebra. -/
theorem exists_integral_root_model
    (F : Type u) [Field F] [IsAlgClosed F]
    (S T B U : Grp (Over (Spec (.of F))))
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
    (Ua : Φ → Grp (Over (Spec (.of F)))) (ia : ∀ α : Φ, Ua α ⟶ S)
    (hua : ∀ α : Φ, IsClosedSubgroupScheme (ia α).hom.hom ∧
      Smooth (Ua α).X.hom ∧ ConnectedSpace (Ua α).X.left ∧
      TorusCharacterTangent.IsStable T S (ia α) ∧
      (GrpObj.differential (ia α).hom.hom).toLinearMap.range =
        TorusCharacterTangent.weightSpace T S α.val.toMul ∧
      Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ Ua α))
    (x : ∀ α : b.support, Grp.mk (StandardGroupSchemes.additive F) ≅ Ua α) :
    ∃ (GZ TZ BZ UZ : Grp (Over integerBase.{u}))
      (tB : TZ ⟶ BZ) (bG : BZ ⟶ GZ) (uB : UZ ⟶ BZ)
      (_ : GrpObj integralLine.{u}) (y : ∀ α : Φ, Grp.mk integralLine ⟶ GZ),
      (∀ H ∈ ({GZ, TZ, BZ, UZ} : Set (Grp (Over integerBase.{u}))),
        Smooth H.X.hom ∧ IsAffine H.X.left ∧
        LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom) ∧
      IsClosedImmersion tB.hom.hom.left ∧ IsClosedImmersion bG.hom.hom.left ∧
      IsClosedImmersion uB.hom.hom.left ∧
      IsClosedImmersion (tB ≫ bG).hom.hom.left ∧
      (∀ α : Φ, IsClosedImmersion (y α).hom.hom.left) ∧
      (coordinateArrow PUnit (𝟙_ (Over integerBase)) (fun _ ↦ 0) = η[integralLine]) ∧
      (∀ (W : Over integerBase.{u}) (a c : Γ(W.left, ⊤)),
        coordinateArrow PUnit W (fun _ ↦ a + c) =
          coordinateArrow PUnit W (fun _ ↦ a) * coordinateArrow PUnit W (fun _ ↦ c)) ∧
      ∃ (aF : Grp.mk (StandardGroupSchemes.additive F) ≅
          (scalarChange F).obj (Grp.mk integralLine))
        (aQ : Grp.mk (StandardGroupSchemes.additive (ULift.{u} ℚ)) ≅
          (scalarChange (ULift.{u} ℚ)).obj (Grp.mk integralLine))
        (fibreIso : (scalarChange F).obj GZ ≅ S)
        (eT : (scalarChange F).obj TZ ≅ T)
        (eB : (scalarChange F).obj BZ ≅ B)
        (eU : (scalarChange F).obj UZ ≅ U),
        (aF.hom.hom.hom.left ≫ pullback.fst integralLine.hom (integerMap F)).appTop
            (AffineSpace.coord integerBase PUnit.unit) =
          (Scheme.ΓSpecIso (.of (Polynomial F))).inv Polynomial.X ∧
        (aQ.hom.hom.hom.left ≫
            pullback.fst integralLine.hom (integerMap (ULift.{u} ℚ))).appTop
            (AffineSpace.coord integerBase PUnit.unit) =
          (Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℚ)))).inv Polynomial.X ∧
        (scalarChange F).map (tB ≫ bG) ≫ fibreIso.hom = eT.hom ≫ iT ∧
        (scalarChange F).map bG ≫ fibreIso.hom = eB.hom ≫ iB ∧
        (scalarChange F).map (uB ≫ bG) ≫ fibreIso.hom = eU.hom ≫ iU ≫ iB ∧
        (∃ er : ∀ α : Φ, Grp.mk (StandardGroupSchemes.additive F) ≅ Ua α,
          (∀ α : Φ,
            aF.hom ≫ (scalarChange F).map (y α) ≫ fibreIso.hom = (er α).hom ≫ ia α) ∧
          ∀ α : b.support, er α = x α) ∧
        (∀ α : Φ, b.IsPos α → ∃ z : Grp.mk integralLine ⟶ UZ,
          z ≫ uB ≫ bG = y α) ∧
        (∃ (N : ℕ) (β : Fin N ≃ {α : Φ // b.IsPos α})
          (θ : affineCoordinates (ULift.{u} (Fin N)) integerBase ≅ UZ.X),
          θ.hom ≫ uB.hom.hom ≫ bG.hom.hom =
            ((List.finRange N).map
              (fun i ↦ rootProjection N i ≫ (y (β i).val).hom.hom)).prod ∧
          coordinateArrow (ULift.{u} (Fin N)) (𝟙_ (Over integerBase))
            (fun _ ↦ 0) ≫ θ.hom = η[UZ.X]) ∧
        ∃ (_ : LieAlgebra ℚ (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X))
          (_ : FiniteDimensional ℚ (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X))
          (_ : LieAlgebra.HasTrivialRadical ℚ (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X))
          (H : LieSubalgebra ℚ (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X))
          (_ : IsLieAbelian H)
          (Q : RootPairing Φ ℚ (Module.Dual ℚ H) H)
          (_ : Q.IsRootSystem) (_ : Q.IsCrystallographic) (_ : Q.IsReduced)
          (bQ : Q.Base) (e : Φ → GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X),
          (∀ (q : ℚ) (v : GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X),
            q • v = (ULift.up q : ULift.{u} ℚ) • v) ∧
          (∀ K : LieSubalgebra ℚ (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X),
            H ≤ K → IsLieAbelian K → K = H) ∧
          (H : Set (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X)) =
            Set.range (GrpObj.differential
              ((scalarChange (ULift.{u} ℚ)).map (tB ≫ bG)).hom.hom) ∧
          (∀ (f : Module.Dual ℚ H) (h : H), Q.toLinearMap f h = f h) ∧
          bQ.support = b.support ∧
          (∀ α β : Φ, Q.pairing α β = (P.pairing α β : ℚ)) ∧
          (∀ α : Φ, GrpObj.tangentPoint (e α) =
            TorusCharacterTangent.additiveParameterPoint (ULift.{u} ℚ)
                (TrivSqZeroExt.inr 1) ≫ aQ.hom.hom.hom ≫
              ((scalarChange (ULift.{u} ℚ)).map (y α)).hom.hom) ∧
          (∀ α : Φ, e α ∈ LieModule.weightSpace
              (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X) (Q.root α) ∧ e α ≠ 0) ∧
          (∀ α : Φ, ⁅e α, e (Q.reflectionPerm α α)⁆ = (Q.coroot α :
            GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X)) ∧
          (∀ α β κ : Φ, Q.root α + Q.root β = Q.root κ →
            ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
              ⁅e α, e β⁆ = ((ε : ℚ) * (Q.chainBotCoeff α β + 1)) • e κ) ∧
          (∀ α β : Φ, Q.root α + Q.root β ∉ Set.range Q.root →
            Q.root α + Q.root β ≠ 0 → ⁅e α, e β⁆ = 0) ∧
          (∃ C : Module.Basis (bQ.support ⊕ Φ) ℚ
              (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X),
            (∀ α : bQ.support, C (Sum.inl α) = (Q.coroot α :
              GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X)) ∧
            ∀ α : Φ, C (Sum.inr α) = e α) ∧
          (IsEmpty Φ →
            Nonempty (GZ ≅ Grp.trivial (Over integerBase)) ∧
            Nonempty (TZ ≅ Grp.trivial (Over integerBase)) ∧
            Nonempty (BZ ≅ Grp.trivial (Over integerBase)) ∧
            Nonempty (UZ ≅ Grp.trivial (Over integerBase)) ∧
            Subsingleton (GrpObj.Lie ((scalarChange (ULift.{u} ℚ)).obj GZ).X)) := by
  sorry

end AlgebraicGeometry.ChevalleyIntegralRootModel
