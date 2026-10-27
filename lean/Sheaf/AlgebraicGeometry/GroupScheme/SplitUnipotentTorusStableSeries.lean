/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries
public import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # A torus-stable additive series in a split unipotent group

Source: Milne, Algebraic Groups (2017), Summary 16.29(d), p.334, and Proposition
16.54, p.344; supporting equivariant filtration, following Conrad--Lichtenstein,
Linear Algebraic Groups I, Appendix D.3, proof of Theorem D.3.2, pp.86--87.
(blueprint: lem-sfb-split-unipotent-torus-stable-series)

The additive quotient is presented by its actual quotient homomorphism to G_a.
Thus its representing quotient is G_a itself and its quotient identification is
identity. The kernel identification is retained by `IsFppfQuotient`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A split torus acting by group automorphisms on a split unipotent group admits
an invariant normal series with one-dimensional additive character quotients.

Source: Milne, Summary 16.29(d), p.334, and Proposition 16.54, p.344; supporting
filtration from Conrad--Lichtenstein, Appendix D.3, pp.86--87.
(blueprint: lem-sfb-split-unipotent-torus-stable-series)

Proof plan (the four steps of the DAG node):
1. Strongly induct on the finite integer dim U. The dimension formula supplies
   finiteness; affineness supplies separatedness. For U=1 take length zero.
   Otherwise lem-sfb-split-unipotent-central-vector-subgroup gives an E-stable
   central nonzero vector subgroup C. Apply lem-sfb-torus-vector-group-linearization
   to write its action as a linear Laurent coaction on a nonzero vector space W.
2. Expand the coaction into Laurent monomials. Coassociativity says each coefficient
   is a weight vector and the counit says their sum is the original vector. Choose
   a nonzero coefficient and its one-dimensional weight line. Its image N in C is
   closed, central, E-stable and isomorphic to G_a. Completing the vector to a basis
   proves closedness; affine-space smoothness gives smoothness. This holds after
   every field extension. The parameter on N has the chosen integer weight.
3. Apply lem-sfb-affine-normal-quotient-geometry to U/N. The quotient is affine,
   smooth and geometrically connected. By lem-sfb-split-unipotent-quotient-split
   it is split unipotent. The action descends by fppf-local lifting. The formula
   of lem-sfb-homogeneous-quotient-krull-dimension gives strictly smaller dimension,
   since N is an affine line. Apply the induction hypothesis to this quotient.
4. Pull the quotient series back to U and append 1. The normal-quotient geometry
   lemma gives normality, smoothness, connectedness and the successive quotient
   identifications. After every field extension the same reasoning gives geometric
   connectedness. Equivariance gives stability and transports the character formula.
   The last nontrivial term is N with the parameter from step 2. Each map to G_a
   represents its fppf quotient, so its scheme-theoretic kernel is the next term.
   This also covers a trivial quotient and a rank-zero acting torus.
-/
theorem splitUnipotent_exists_torusStableSeries
    {k : Type u} [Field k] (U : Grp (Over (Spec (.of k))))
    (_halg : SolvableGroupStructure.IsAlgebraic U)
    (_hunip : SolvableGroupStructure.IsUnipotent U)
    (_hgeom : GeometricallyConnected U.X.hom)
    (_hsplit : ∃ n : ℕ, SplitUnipotentLength U n)
    (s : ℕ)
    (act : (MultiplicativeType.splitTorus k s).X ⊗ U.X ⟶ U.X)
    (_hone : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ U.X),
      lift (1 : (Spec (.of R)).asOver (Spec (.of k)) ⟶
        (MultiplicativeType.splitTorus k s).X) x ≫ act = x)
    (_hassoc : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (e f : (Spec (.of R)).asOver (Spec (.of k)) ⟶
        (MultiplicativeType.splitTorus k s).X)
      (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ U.X),
      lift (e * f) x ≫ act = lift e (lift f x ≫ act) ≫ act)
    (_hhom : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (e : (Spec (.of R)).asOver (Spec (.of k)) ⟶
        (MultiplicativeType.splitTorus k s).X)
      (x y : (Spec (.of R)).asOver (Spec (.of k)) ⟶ U.X),
      lift e (x * y) ≫ act = (lift e x ≫ act) * (lift e y ≫ act)) :
    ∃ (m : ℕ) (V : Fin (m + 1) → Grp (Over (Spec (.of k))))
      (a : ∀ i : Fin (m + 1), V i ⟶ U)
      (j : ∀ i : Fin m, V i.succ ⟶ V i.castSucc),
      IsIso (a 0) ∧ Nonempty (V (Fin.last m) ≅ Grp.trivial _) ∧
      (∀ i : Fin (m + 1),
        IsClosedSubgroupScheme (a i).hom.hom ∧
        IsNormalSubgroupScheme (a i).hom.hom ∧
        Smooth (V i).X.hom ∧ GeometricallyConnected (V i).X.hom) ∧
      (∀ i : Fin m,
        j i ≫ a i.castSucc = a i.succ ∧
        IsClosedSubgroupScheme (j i).hom.hom ∧
        IsNormalSubgroupScheme (j i).hom.hom ∧
        ∃ (actᵢ : (MultiplicativeType.splitTorus k s).X ⊗ (V i.castSucc).X ⟶
            (V i.castSucc).X)
          (q : V i.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k))
          (n : Fin s → ℤ),
          (MultiplicativeType.splitTorus k s).X ◁ (a i.castSucc).hom.hom ≫ act =
            actᵢ ≫ (a i.castSucc).hom.hom ∧
          SolvableGroupStructure.IsFppfQuotient (j i).hom.hom q ∧
          (∀ (R : Type u) [CommRing R] [Algebra k R]
            (e : (Spec (.of R)).asOver (Spec (.of k)) ⟶
              (MultiplicativeType.splitTorus k s).X)
            (x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ (V i.castSucc).X),
            (lift e x ≫ actᵢ ≫ q.hom.hom).left.appTop
                ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) =
              ((List.ofFn (fun l : Fin s ↦
                (e ≫ SplitTorusFrames.coordinate k s l) ^ n l)).prod.left.appTop
                ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) *
              (x ≫ q.hom.hom).left.appTop
                ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X))) := by
  sorry

end AlgebraicGeometry
