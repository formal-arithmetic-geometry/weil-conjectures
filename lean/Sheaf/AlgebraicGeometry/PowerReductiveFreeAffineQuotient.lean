/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits

/-!+# Affineness of free affine quotients under universal invariant power lifting

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Proposition 9.7.8, printed p. 528; Lemma 9.2.5(3) and Theorem 4.3.1
(blueprint: lem-sfb-power-reductive-free-affine-quotient).

The orbit coequalizer and its sheafification unit are actual constructions. Sheafification
uses the next value universe; its comparison with the given small algebraic space includes
the quotient arrow. The coordinate algebra after base change is the canonical tensor
product Hopf algebra, identified with global functions by the affine fibre-product formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The sectionwise right-orbit presheaf is the coequalizer of projection and action.
Source: Alper, Proposition 9.7.8, principal homogeneous space; Stacks, quotient sheaf
(blueprint: lem-sfb-power-reductive-free-affine-quotient). -/
def affineRightOrbitPresheaf {S : Scheme.{u}} (G X : Over S) (a : X ⊗ G ⟶ X) :
    (Over S)ᵒᵖ ⥤ Type u :=
  coequalizer (yoneda.map (fst X G)) (yoneda.map a)

/-- The fppf sheaf quotient is the sheafification of the right-orbit presheaf.
Source: Alper, Proposition 9.7.8; Stacks, quotient sheaf
(blueprint: lem-sfb-power-reductive-free-affine-quotient). -/
def affineRightQuotient {S : Scheme.{u}} (G X : Over S) (a : X ⊗ G ⟶ X) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (affineRightOrbitPresheaf G X a ⋙ uliftFunctor.{u + 1, u})

/-- The actual orbit projection followed by the sheafification unit.
Source: Alper, Proposition 9.7.8; Stacks, quotient sheaf
(blueprint: lem-sfb-power-reductive-free-affine-quotient). -/
def affineRightQuotientMap {S : Scheme.{u}} (G X : Over S) (a : X ⊗ G ⟶ X) :
    yoneda.obj X ⋙ uliftFunctor.{u + 1, u} ⟶ (affineRightQuotient G X a).obj :=
  Functor.whiskerRight (coequalizer.π (yoneda.map (fst X G)) (yoneda.map a))
      uliftFunctor.{u + 1, u} ≫
    toSheafify (Scheme.fppfTopology.over S)
      (affineRightOrbitPresheaf G X a ⋙ uliftFunctor.{u + 1, u})

/-- Universal invariant power lifting makes the free affine fppf quotient affine,
and its projection affine and finitely presented, without a finite-type assumption on X.
The four displayed linear-map equations are precisely counitality and coassociativity
of the two algebra coactions. Their Hopf algebra is R' tensor_R Gamma(G,O).
Source: Alper, Proposition 9.7.8, with Lemma 9.2.5(3) and Theorem 4.3.1
(blueprint: lem-sfb-power-reductive-free-affine-quotient).

Proof:
1. Choose a representable surjective etale scheme atlas of Y. The local-section
   hypothesis lifts it fppf locally to X. The torsor pullback square gives a unique
   g with x = s g, identifying each pullback of X with U_i times_S G. This uses
   lem-sfb-space-fppf-covering-calculus; the formulas commute with test maps.
2. The identity section makes G surjective. The trivial models are flat, locally
   finitely presented and affine. Form the coproduct of the U_i using
   lem-weil-pbc-scheme-coproduct-family. Apply
   lem-sfb-representable-flat-lfp-fppf-descent and
   lem-sfb-space-four-property-fppf-descent. Thus q is flat, surjective, affine and
   locally finitely presented. By lem-weil-pbc-affine-morphism-permanence it is
   quasi-compact and separated, hence quasi-separated, and therefore finitely presented.
3. X is quasi-compact and surjects onto Y, so
   lem-sfb-algebraic-stack-quasicompact-surjection gives quasi-compactness of Y.
   Pull its absolute diagonal back by q times q. The source X times_S G and target
   X times_Spec(Z) X are affine by lem-weil-pbc-fibre-product-affine-spectra.
   Their map is affine by the spectrum description. Descend affineness of the
   diagonal by lem-sfb-space-four-property-fppf-descent. Hence Y is quasi-separated.
4. For any surjection of quasi-coherent algebras on Y, use
   lem-sfb-affine-torsor-algebra-invariants to identify global sections with the
   invariants of the equivariant algebras on affine X. The hypothesis at R'=R
   lifts a positive power of every section to an invariant, hence to a section on Y.
   This applies to arbitrary algebras, with no finite-generation restriction.
5. Apply lem-sfb-space-power-lifting-affineness to Steps 3 and 4 to obtain an
   affine representing scheme U. Its structure map to Spec R is affine. The
   representing isomorphism transports q to the scheme morphism f; Step 2 gives
   affineness, local finite presentation, quasi-compactness and quasi-separatedness. -/
theorem power_reductive_free_affine_quotient
    (R : CommRingCat.{u}) (G : Scheme.{u}) [G.Over (Spec R)]
    [GrpObj (G.asOver (Spec R))] [IsAffine G]
    [Flat (G ↘ Spec R)] [LocallyOfFinitePresentation (G ↘ Spec R)]
    [QuasiCompact (G ↘ Spec R)] [QuasiSeparated (G ↘ Spec R)]
    (hpower : ∀ (R' : Type u) [CommRing R'] [Algebra R R']
      (E F : Type u) [CommRing E] [CommRing F] [Algebra R' E] [Algebra R' F]
      (ρE : E →ₐ[R'] E ⊗[R'] (R' ⊗[R] Γ(G, ⊤)))
      (ρF : F →ₐ[R'] F ⊗[R'] (R' ⊗[R] Γ(G, ⊤))),
      (TensorProduct.rid R' E).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R') (A := R' ⊗[R] Γ(G, ⊤))).lTensor E ∘ₗ
          ρE.toLinearMap = LinearMap.id →
      (TensorProduct.assoc R' E (R' ⊗[R] Γ(G, ⊤)) (R' ⊗[R] Γ(G, ⊤))).toLinearMap ∘ₗ
          ρE.toLinearMap.rTensor (R' ⊗[R] Γ(G, ⊤)) ∘ₗ ρE.toLinearMap =
        (Coalgebra.comul (R := R') (A := R' ⊗[R] Γ(G, ⊤))).lTensor E ∘ₗ
          ρE.toLinearMap →
      (TensorProduct.rid R' F).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R') (A := R' ⊗[R] Γ(G, ⊤))).lTensor F ∘ₗ
          ρF.toLinearMap = LinearMap.id →
      (TensorProduct.assoc R' F (R' ⊗[R] Γ(G, ⊤)) (R' ⊗[R] Γ(G, ⊤))).toLinearMap ∘ₗ
          ρF.toLinearMap.rTensor (R' ⊗[R] Γ(G, ⊤)) ∘ₗ ρF.toLinearMap =
        (Coalgebra.comul (R := R') (A := R' ⊗[R] Γ(G, ⊤))).lTensor F ∘ₗ
          ρF.toLinearMap →
      ∀ f : E →ₐ[R'] F, Function.Surjective f →
        f.toLinearMap.rTensor (R' ⊗[R] Γ(G, ⊤)) ∘ₗ ρE.toLinearMap =
          ρF.toLinearMap ∘ₗ f.toLinearMap →
        ∀ b : F, ρF b = b ⊗ₜ[R'] (1 : R' ⊗[R] Γ(G, ⊤)) →
          ∃ (N : ℕ) (e : E), 1 ≤ N ∧
            ρE e = e ⊗ₜ[R'] (1 : R' ⊗[R] Γ(G, ⊤)) ∧ f e = b ^ N)
    (X : Over (Spec R)) [IsAffine X.left]
    (a : X ⊗ G.asOver (Spec R) ⟶ X)
    (hunit : ∀ (T : Over (Spec R)) (x : T ⟶ X), lift x 1 ≫ a = x)
    (hmul : ∀ (T : Over (Spec R)) (x : T ⟶ X)
      (g h : T ⟶ G.asOver (Spec R)),
      lift (lift x g ≫ a) h ≫ a = lift x (g * h) ≫ a)
    (hfree : ∀ (T : Over (Spec R)) (x : T ⟶ X) (g : T ⟶ G.asOver (Spec R)),
      lift x g ≫ a = x → g = 1)
    (Y : AlgebraicSpace (Spec R))
    (q : yoneda.obj X ⟶ Y.obj.obj)
    (equot : (affineRightQuotient (G.asOver (Spec R)) X a).obj ≅
      Y.obj.obj ⋙ uliftFunctor.{u + 1, u})
    (hq : Functor.whiskerRight q uliftFunctor.{u + 1, u} =
      affineRightQuotientMap (G.asOver (Spec R)) X a ≫ equot.hom)
    (hsections : ∀ (T : Over (Spec R)) (y : Y.obj.obj.obj (op T)),
      ∃ K : Sieve T, K ∈ (Scheme.fppfTopology.over (Spec R)) T ∧
        ∀ (V : Over (Spec R)) (b : V ⟶ T), K b →
          ∃ x : V ⟶ X, q.app (op V) x = Y.obj.obj.map b.op y)
    (htorsor : IsPullback (yoneda.map (fst X (G.asOver (Spec R))))
      (yoneda.map a) q q) :
    ∃ (U : Over (Spec R)) (_ : IsAffine U.left) (e : yoneda.obj U ≅ Y.obj.obj)
      (f : X ⟶ U), yoneda.map f ≫ e.hom = q ∧
        IsAffineHom f.left ∧ LocallyOfFinitePresentation f.left ∧
        QuasiCompact f.left ∧ QuasiSeparated f.left := by
  sorry

end AlgebraicGeometry
