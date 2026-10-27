/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Invariant projective closures and their homogeneous equations

Source: Milne, Algebraic Groups (2017), Corollary 1.18, Sections 4 and 7f,
and the supporting closure argument for Lemma 13.46; Stacks Tags 01J3, 0356 and 03GL.
(blueprint: lem-sfb-projective-invariant-boundary-ideals).

Coordinates identify a nonzero finite-dimensional vector space with k^(n+1).
The lifted indices are used only for the existing general linear group scheme.
The induced action is specified by a graded substitution over the universal point,
with both projections fixing the affine base-change comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open MvPolynomial
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.ProjectiveInvariantBoundary

/-- Polynomial Proj over its coefficient ring, with the standard degree-zero structure map.
This is the existing polynomial projective space with finite, unlifted coordinate indices.
Source: Stacks Tag 01ND (blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def space (R : Type u) [CommRing R] (n : ℕ) : Over (Spec (.of R)) :=
  Over.mk (Proj.toSpecZero (homogeneousSubmodule (Fin (n + 1)) R) ≫
    Spec.map (CommRingCat.ofHom
      (homogeneousSubmoduleZeroEquiv (Fin (n + 1)) R).toRingHom))

/-- The actual matrix substitution on homogeneous coordinates, fixing the specified constants.
Source: Milne Section 7f, p.145
(blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def substitution {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (n : ℕ)
    (M : Matrix (ULift.{u} (Fin (n + 1))) (ULift.{u} (Fin (n + 1))) A) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1)) A :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ)
    (fun i ↦ ∑ j : Fin (n + 1), C (M (ULift.up i) (ULift.up j)) * X j)

variable {k : Type u} [Field k]
variable (G : Scheme.{u}) [G.Over (Spec (.of k))]
variable [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]

/-- Scheme-theoretic specification of the projective action induced by rho on lines.
The pullback uses rho itself; inverse substitution will give the left action on polynomials.
The comparison e is canonical because both of its projection composites are prescribed.
Source: Milne Sections 7e--7f, pp.143--145; affine base change for polynomial Proj.
(blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def IsInduced (n : ℕ)
    (ρ : GeneralLinearGroup.RationalHom (G.asOver (Spec (.of k)))
      (ULift.{u} (Fin (n + 1)))) [IsMonHom ρ]
    (a : ModObj (G.asOver (Spec (.of k))) (space k n)) : Prop :=
  ∃ φ ψ : homogeneousSubmodule (Fin (n + 1)) k →+*ᵍ
      homogeneousSubmodule (Fin (n + 1)) Γ(G, ⊤),
    φ.toRingHom = substitution (algebraMap k Γ(G, ⊤)) n
      (ρ.points Γ(G, ⊤) (RationalRepresentation.genericPoint (k := k) G)) ∧
    ψ.toRingHom = MvPolynomial.map (algebraMap k Γ(G, ⊤)) ∧
    ∃ (hφ : HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) Γ(G, ⊤)) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) k)).map φ)
      (hψ : HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) Γ(G, ⊤)) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) k)).map ψ),
      ∃ e : (space Γ(G, ⊤) n).left ≅
          ((G.asOver (Spec (.of k))) ⊗ space k n).left,
        e.hom ≫ (fst (G.asOver (Spec (.of k))) (space k n)).left =
          (space Γ(G, ⊤) n).hom ≫ G.isoSpec.inv ∧
        e.hom ≫ (snd (G.asOver (Spec (.of k))) (space k n)).left = Proj.map ψ hψ ∧
        e.hom ≫ a.smul.left = Proj.map φ hφ

/-- The existing reduced induced closed subscheme, retaining its structural map.
Source: Stacks Tags 01J3--01J4
(blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def reducedClosed (n : ℕ) (T : TopologicalSpace.Closeds (space k n).left) :
    Over (Spec (.of k)) :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ (space k n).hom)

/-- The canonical closed immersion of the reduced induced closed subscheme.
Source: Stacks Tags 01J3--01J4
(blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def inclusion (n : ℕ) (T : TopologicalSpace.Closeds (space k n).left) :
    reducedClosed n T ⟶ space k n :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal T).subschemeι

/-- The topological closure, used with the existing reduced-induced construction.
Source: Stacks Tag 01J3
(blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def closureSet (n : ℕ) {W : Over (Spec (.of k))} (j : W ⟶ space k n) :
    TopologicalSpace.Closeds (space k n).left :=
  TopologicalSpace.Closeds.closure (Set.range j.left)

/-- Embed the scalar extension of the degree-d piece into the polynomial algebra over A.
This is base change of the submodule inclusion followed by the canonical tensor equivalence.
Source: Milne Section 7f, p.145; Stacks Tag 03GL
(blueprint: lem-sfb-projective-invariant-boundary-ideals). -/
def polynomialTensor (n d : ℕ) (A : Type u) [CommRing A] [Algebra k A] :
    A ⊗[k] homogeneousSubmodule (Fin (n + 1)) k d →ₗ[A] MvPolynomial (Fin (n + 1)) A :=
  (MvPolynomial.algebraTensorAlgEquiv k A).toLinearMap ∘ₗ
    (homogeneousSubmodule (Fin (n + 1)) k d).subtype.baseChange A

/-- The reduced projective closure and boundary are invariant, and their degree pieces
are rational subrepresentations for the contragredient polynomial action over every algebra.
Source: Milne, Corollary 1.18, Sections 4 and 7f, and the input to Lemma 13.46;
Stacks Tags 01J3, 0356 and 03GL.
(blueprint: lem-sfb-projective-invariant-boundary-ideals).

Proof:
1. Factor W through an open U where it is closed. The closure meets U in W's support.
Reduced-induced uniqueness identifies W with Z intersect U and makes its complement B closed.
2. For each g in G(k), its projective automorphism preserves W, its closure Z, and B.
Uniqueness of reduced closed structures upgrades this to preservation of closed subschemes.
3. Smoothness makes G reduced. The affine charts of G times Z and G times B are reduced
finite-type algebras by lem-wf-affine-product-reduced. Nullstellensatz vanishing gives
k-point density, including for disconnected G.
4. The ambient action maps those products into Z and B on dense k-points. Reduced-source
closed factorization gives their scheme actions; monicity gives identities and equivariance.
5. Degree-d monomials form a finite basis. Substitution by rho(g) inverse preserves degree,
respects products in G, and commutes with every algebra map. The representation/comodule
dictionary therefore gives its natural rational representation, including degree zero.
6. The chartwise criterion is exactly the degree piece in the homogeneous-ideal lemma 03GL.
On the reduced charts Nullstellensatz equates section vanishing with vanishing on k-points.
The formula f(rho(g) inverse v) therefore preserves these subspaces for every g in G(k).
7. The smooth-group rational-point subspace test upgrades this to every algebra A, including
nonreduced A. Restricting the natural automorphisms gives a rational representation on I;
the finite-dimensional dictionary identifies it with a group-scheme representation.
8. Empty W or B gives the full polynomial pieces; a nonempty C has I(C)_0=0.
Dimension one, every characteristic, and disconnected G require no separate hypotheses. -/
theorem projective_invariant_boundary_ideals [IsAlgClosed k]
    [Smooth (G ↘ Spec (.of k))] [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))] (n : ℕ)
    (ρ : GeneralLinearGroup.RationalHom (G.asOver (Spec (.of k)))
      (ULift.{u} (Fin (n + 1)))) [IsMonHom ρ]
    (a : ModObj (G.asOver (Spec (.of k))) (space k n)) (ha : IsInduced G n ρ a)
    (W : Over (Spec (.of k))) [IsReduced W.left]
    (j : W ⟶ space k n) [IsImmersion j.left]
    (aW : ModObj (G.asOver (Spec (.of k))) W)
    (hj : aW.smul ≫ j = (𝟙 (G.asOver (Spec (.of k))) ⊗ₘ j) ≫ a.smul) :
    ∃ B : TopologicalSpace.Closeds (space k n).left,
      (B : Set (space k n).left) = closure (Set.range j.left) \ Set.range j.left ∧
      ∃ (aZ : ModObj (G.asOver (Spec (.of k))) (reducedClosed n (closureSet n j)))
        (aB : ModObj (G.asOver (Spec (.of k))) (reducedClosed n B))
        (jW : W ⟶ reducedClosed n (closureSet n j))
        (jB : reducedClosed n B ⟶ reducedClosed n (closureSet n j)),
        IsOpenImmersion jW.left ∧ IsClosedImmersion jB.left ∧
        jW ≫ inclusion n (closureSet n j) = j ∧ jB ≫ inclusion n (closureSet n j) = inclusion n B ∧
        Set.range jW.left = (Set.range jB.left)ᶜ ∧
        aZ.smul ≫ inclusion n (closureSet n j) =
          (𝟙 (G.asOver (Spec (.of k))) ⊗ₘ inclusion n (closureSet n j)) ≫ a.smul ∧
        aB.smul ≫ inclusion n B =
          (𝟙 (G.asOver (Spec (.of k))) ⊗ₘ inclusion n B) ≫ a.smul ∧
        aW.smul ≫ jW = (𝟙 (G.asOver (Spec (.of k))) ⊗ₘ jW) ≫ aZ.smul ∧
        aB.smul ≫ jB = (𝟙 (G.asOver (Spec (.of k))) ⊗ₘ jB) ≫ aZ.smul ∧
        ∀ d : ℕ, ∃ r : RationalRepresentation.NaturalRepresentation (k := k) G
            (homogeneousSubmodule (Fin (n + 1)) k d),
          (∀ (A : Type u) [CommRing A] [Algebra k A]
            (g : points (G.asOver (Spec (.of k))) A)
            (t : A ⊗[k] homogeneousSubmodule (Fin (n + 1)) k d),
            polynomialTensor n d A (r.action A g t) =
              MvPolynomial.aeval
                (fun i : Fin (n + 1) ↦ ∑ l : Fin (n + 1),
                  C (((ρ.points A g)⁻¹ : Matrix.GeneralLinearGroup
                    (ULift.{u} (Fin (n + 1))) A) (ULift.up i) (ULift.up l)) * X l)
                (polynomialTensor n d A t)) ∧
          ∀ T ∈ ({closureSet n j, B} : Set (TopologicalSpace.Closeds (space k n).left)),
            ∃ I : Submodule k (homogeneousSubmodule (Fin (n + 1)) k d),
              (∀ F : homogeneousSubmodule (Fin (n + 1)) k d,
                F ∈ I ↔ ∀ i : Fin (n + 1),
                  (inclusion n T).left.app
                    (Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i))
                    (projectiveClosedSubschemeChartFraction k n d F i) = 0) ∧
              FiniteDimensional k I ∧
              (∀ (A : Type u) [CommRing A] [Algebra k A]
                (g : points (G.asOver (Spec (.of k))) A),
                (I.baseChange A).map (r.action A g).toLinearMap = I.baseChange A) ∧
              ∃ s : RationalRepresentation.NaturalRepresentation (k := k) G I,
                (∀ (A : Type u) [CommRing A] [Algebra k A]
                  (g : points (G.asOver (Spec (.of k))) A),
                  I.subtype.baseChange A ∘ₗ (s.action A g).toLinearMap =
                    (r.action A g).toLinearMap ∘ₗ I.subtype.baseChange A) ∧
                ∃ (b : Module.Basis (ULift.{u} (Fin (Module.finrank k I))) k I)
                  (τ : GeneralLinearGroup.RationalHom (G.asOver (Spec (.of k)))
                    (ULift.{u} (Fin (Module.finrank k I)))),
                  IsMonHom τ ∧
                  ∀ (A : Type u) [CommRing A] [Algebra k A]
                    (g : points (G.asOver (Spec (.of k))) A) (t : A ⊗[k] I),
                    s.action A g t =
                      (Matrix.GeneralLinearGroup.toLin' (b.baseChange A)
                        (GeneralLinearGroup.homMulEquiv
                          (ULift.{u} (Fin (Module.finrank k I))) k A (g ≫ τ))).toLinearEquiv t := by
  sorry

end AlgebraicGeometry.ProjectiveInvariantBoundary
