/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice

/-! # Integral Euler characters of arbitrary flag line bundles

Source: Milne, Algebraic Groups (2017), Section 18c, Theorem 22.48 and Theorem 22.50,
printed pp.389--390 and 479--480, with the quotient-action signs retained.
(blueprint: lem-sfb-flag-line-euler-alternant)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct DirectSum

namespace AlgebraicGeometry.FlagEuler

/-- The normalized comparison of the two existing module pullback functors.
It intertwines their adjunction units, so does not choose an arbitrary isomorphism.
Source: Stacks 0096, used in Milne 22.50's natural cohomology action.
(blueprint: lem-sfb-flag-line-euler-alternant) -/
def pullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.tensorPullback f ≅ Scheme.Modules.pullback f :=
  (Scheme.Modules.scalarPullbackAdjunction f).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- Left multiplication by a rational point, as an actual scheme morphism.
Source: Milne 18c and 22.48 (blueprint: lem-sfb-flag-line-euler-alternant). -/
def translate {F : Type u} [Field F] (G : Grp (Over (Spec (.of F))))
    (s : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) : G.X ⟶ G.X :=
  (toUnit G.X ≫ s) * 𝟙 G.X

/-- The quotient's actual left translation from the homogeneous bundle presentation.
Source: Milne 18c and 22.48 (blueprint: lem-sfb-flag-line-euler-alternant). -/
def baseTranslate {F : Type u} [Field F]
    {G B : Grp (Over (Spec (.of F)))} {iB : B ⟶ G}
    {Q : Over (Spec (.of F))} {π : G.X ⟶ Q}
    {χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)}
    (L : AssociatedCharacterLineBundle.Presentation G B iB Q π χ)
    (s : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) : Q ⟶ Q :=
  lift (toUnit Q ≫ s) (𝟙 Q) ≫ L.baseAction.smul

/-- The coefficient isomorphism for natural left translation on cohomology.
After the faithfully flat atlas π its coordinate is unchanged under g ↦ s⁻¹g.
This pins the isomorphism on the entire scheme, not only on global sections.
Source: Milne 18c and 22.48 (blueprint: lem-sfb-flag-line-euler-alternant). -/
def IsTranslationCoefficient {F : Type u} [Field F]
    {G B : Grp (Over (Spec (.of F)))} {iB : B ⟶ G}
    {Q : Over (Spec (.of F))} {π : G.X ⟶ Q}
    {χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)}
    (L : AssociatedCharacterLineBundle.Presentation G B iB Q π χ)
    (s : 𝟙_ (Over (Spec (.of F))) ⟶ G.X)
    (h : π ≫ baseTranslate L s⁻¹ = translate G s⁻¹ ≫ π)
    (θ : (Scheme.Modules.tensorPullback (baseTranslate L s⁻¹).left).obj L.L ≅ L.L) :
    Prop :=
  (Scheme.Modules.pullback π.left).mapIso
      ((pullbackComparison (baseTranslate L s⁻¹).left).symm.app L.L ≪≫ θ) ≪≫
      L.trivialization =
    (Scheme.Modules.pullbackComp π.left (baseTranslate L s⁻¹).left).app L.L ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj L.L)
        (congrArg (fun f ↦ f.left) h)) ≪≫
      ((Scheme.Modules.pullbackComp (translate G s⁻¹).left π.left).app L.L).symm ≪≫
      (Scheme.Modules.pullback (translate G s⁻¹).left).mapIso L.trivialization ≪≫
      Scheme.Modules.pullbackObjUnitIso (translate G s⁻¹).left

open Classical in
/-- The scalar-extended action of an actual rational representation in a finite basis.
Source: Milne Section 4a (blueprint: lem-sfb-flag-line-euler-alternant). -/
def pointAction {F : Type u} [Field F]
    {G : Grp (Over (Spec (.of F)))} {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [Fintype I] [DecidableEq I] (e : Module.Basis I F V)
    (r : GeneralLinearGroup.RationalHom G.X I)
    {A : Type u} [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ G.X) : V →ₗ[F] A ⊗[F] V :=
  ∑ j, ∑ k, (TensorProduct.mk F A V
    ((GeneralLinearGroup.homMulEquiv I F A (s ≫ r) : Matrix I I A) j k)).comp
      ((e.coord k).smulRight (e j))

/-- Character weight spaces on the actual vector space. Testing every algebra-valued
point is exactly the coaction equation c(v) = v tensor χ, including nonreduced tests.
Source: Milne 12.12 and 22.36 (blueprint: lem-sfb-flag-line-euler-alternant). -/
def weightSpace {F : Type u} [Field F]
    {G T : Grp (Over (Spec (.of F)))} (iT : T ⟶ G)
    {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [Fintype I] [DecidableEq I] (e : Module.Basis I F V)
    (r : GeneralLinearGroup.RationalHom G.X I)
    (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) : Submodule F V :=
  ⨅ (A : Type u) (_ : CommRing A) (_ : Algebra F A)
    (t : StandardGroupSchemes.affine F A ⟶ T.X),
    (pointAction e r (t ≫ iT.hom.hom) -
      RhoSection.characterValue (t ≫ χ.toMul.hom.hom) • TensorProduct.mk F A V 1).ker

open Classical in
/-- The integral character of one finite rational cohomology space, using integer dimensions.
Source: Milne 22.36 and 22.50 (blueprint: lem-sfb-flag-line-euler-alternant). -/
def character {F : Type u} [Field F]
    {G T : Grp (Over (Spec (.of F)))} (iT : T ⟶ G) [IsCommMonObj T.X]
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [Fintype I] [DecidableEq I] (e : Module.Basis I F V)
    (r : GeneralLinearGroup.RationalHom G.X I) :
    AddMonoidAlgebra ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) :=
  ∑ᶠ χ, AddMonoidAlgebra.single χ (Module.finrank F (weightSpace iT e r χ) : ℤ)

open Classical in
/-- The Weyl alternant in the integral character algebra. The determinant of the
integer lattice automorphism is its determinant after tensoring with ℚ.
Source: Milne 22d, p.480 (blueprint: lem-sfb-flag-line-euler-alternant). -/
def alternant {X Y J : Type u} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (ν : X) : AddMonoidAlgebra ℤ X :=
  ∑ᶠ w : P.weylGroup, AddMonoidAlgebra.single
    ((RootPairing.Equiv.weightEquiv P P w.val) ν)
    (LinearMap.det (RootPairing.Equiv.weightEquiv P P w.val).toLinearMap)

end AlgebraicGeometry.FlagEuler

namespace AlgebraicGeometry

open Classical in
/-- Every homogeneous flag line bundle has finite rational cohomology with finite
weight support, and its integer Euler character satisfies the Weyl alternant identity.
The rational representations below are on the actual derived-functor cohomology.
Their action at every F-point is the pullback by inverse translation followed by the
uniquely normalized coefficient isomorphism. Since G is smooth over an algebraically
closed field, these values determine the rational action, including after scalar extension.

Source: Milne, Section 18c, Theorems 22.48 and 22.50, pp.389--390 and 479--480.
(blueprint: lem-sfb-flag-line-euler-alternant)

Proof plan:
1. Apply lem-sfb-flag-torus-fixed-geometry to the reductive group G. Its fixed points
   are indexed by the normalizer Weyl quotient, with tangent weights -w Phi-positive.
   By lem-sfb-simply-connected-character-lattice roots span the rational character
   space. Lemma lem-sfb-weyl-reflection-realization identifies that quotient with
   the reflection Weyl group; duality gives cotangent weights w alpha, each once.
2. For chi = -lambda composed with p, the associated bundle convention gives
   t[n_w,z] = [n_w,chi(n_w inverse t n_w)z], hence fibre weight -w lambda.
   This calculation holds over every algebra, by the quotient relation in
   lem-sfb-homogeneous-line-bundle-sections.
3. Apply lem-sfb-torus-coherent-fixed-point-formula. It supplies finite-dimensional
   rational cohomology, boundedness and the finite character decomposition, and
   q_lambda = sum_w e^(-w lambda)/product_alpha(1-e^(w alpha)) in the root localization.
4. Lemma lem-sfb-root-datum-weyl-denominator gives
   D = A(-rho) = e^(-rho) product_alpha(1-e^alpha).
   Reindex the Weyl sum to get wD = det(w)D, whence each localized denominator
   is det(w)e^(w rho)D. The root factors and e^(-rho) are units there.
5. Multiply the fixed-point formula by D, obtaining the sum A(-lambda-rho).
   Choose an integer basis of X: its group ring is a Laurent polynomial domain.
   A largest support exponent proves products of nonzero Laurent polynomials nonzero.
   Thus all nonzero root factors are nonzero and localization is injective, so the
   identity holds already over the integers. Rank zero has empty products and W = 1.
-/
theorem flag_line_euler_alternant
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ CategoryTheory.GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpositive : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    [P.IsReduced]
    (ρ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hρ : 2 • ρ = ∑ α ∈ Finset.univ.filter b.IsPos, P.root α)
    (p : B ⟶ T) (hp : j ≫ p = 𝟙 T)
    (hpu : ∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ B),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      Smooth U.X.hom → ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
      l ≫ p = 1)
    (lam : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hχ : χ.hom.hom = (p ≫ lam.toMul).hom.hom⁻¹)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hπf : Flat π.left) (hπs : Surjective π.left)
    (hπi : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπt : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (L : AssociatedCharacterLineBundle.Presentation G B iB Q π χ) :
    (∀ i : ℕ, Module.Finite F (Scheme.Modules.scalarCohomology Q.hom L.L i)) ∧
    (∃ N : ℕ, ∀ i : ℕ, N < i →
      Subsingleton (Scheme.Modules.scalarCohomology Q.hom L.L i)) ∧
    Finite P.weylGroup ∧
    ∃ (I : ℕ → Type u) (_ : ∀ i : ℕ, Fintype (I i)) (_ : ∀ i : ℕ, DecidableEq (I i))
      (e : ∀ i : ℕ, Module.Basis (I i) F (Scheme.Modules.scalarCohomology Q.hom L.L i))
      (r : ∀ i : ℕ, GeneralLinearGroup.RationalHom G.X (I i))
      (_ : ∀ i : ℕ, IsMonHom (r i)),
      (∀ (s : 𝟙_ (Over (Spec (.of F))) ⟶ G.X),
        ∃ (h : π ≫ FlagEuler.baseTranslate L s⁻¹ = FlagEuler.translate G s⁻¹ ≫ π)
          (θ : (Scheme.Modules.tensorPullback (FlagEuler.baseTranslate L s⁻¹).left).obj L.L ≅
            L.L),
          FlagEuler.IsTranslationCoefficient L s h θ ∧
          ∀ (i : ℕ) (v : Scheme.Modules.scalarCohomology Q.hom L.L i),
            ∑ j, ((GeneralLinearGroup.homMulEquiv (I i) F F
                (toUnit (StandardGroupSchemes.affine F F) ≫ s ≫ r i) :
                  Matrix (I i) (I i) F).mulVec ((e i).repr v)) j • e i j =
              Scheme.Modules.scalarCohomologyMap Q.hom θ.hom i
                (Scheme.Modules.scalarCohomologyPullback Q.hom Q.hom
                  (FlagEuler.baseTranslate L s⁻¹).left
                  (FlagEuler.baseTranslate L s⁻¹).w L.L i v)) ∧
      (∀ i : ℕ, DirectSum.IsInternal (FlagEuler.weightSpace iT (e i) (r i)) ∧
        Set.Finite {eta | FlagEuler.weightSpace iT (e i) (r i) eta ≠ ⊥}) ∧
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i • FlagEuler.character iT (e i) (r i)) *
        FlagEuler.alternant P (-ρ) = FlagEuler.alternant P (-lam - ρ) := by
  sorry

end AlgebraicGeometry
