/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.AlgebraicGeometry.SmoothPurityBaseChange.FiniteSmoothOrientationBaseChange
public import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Finite orientation on a supplied Cartesian square

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, proof (1)
(blueprint: lem-route-finite-orientation-cartesian-transport).

The square retains its supplied apex and Cartesian witness. The properties needed to
form the exceptional arrows at that apex are supplied by base-change permanence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

/-- Transport the canonical inverse-orientation equation to any supplied Cartesian square.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, proof (1)
(blueprint: lem-route-finite-orientation-cartesian-transport).

Proof:
1. Put P = X ×_Y Y'. The universal property (def-pc-fibre-product) gives the unique
   isomorphism e : X' ≅ P commuting with both projections. Transport Noetherianity
   and the inverse of ell^n from X' to P. The finite-type affine charts of Y' are
   Noetherian by lem-wf-affine-noetherian-components, so Y' is Noetherian too.
2. Smooth relative dimension, quasi-compactness, separatedness and compactifiability
   persist on P by lem-sbc-smooth-relative-dimension-permanence,
   lem-pc-quasi-compact-base-change, lem-pod-separated-finite-type-base-change and
   lemma-nagata-compactification-base-change. The isomorphism e × e identifies the
   diagonals, their ideals, conormal and graded algebras and extended Rees algebras,
   fixing the deformation parameter. It therefore transports every clause of the
   supplied Geometry g' to a Geometry witness G_P for P; no orientation is chosen.
3. By lem-pur-dualizing-cartesian-apex-isomorphism the supplied dualizing exchange is
   m_omega ; e^*(b_0) ; B_e, where m is the canonical inverse-image compositor,
   b_0 the canonical-square exchange, and B_e the counit-preserving apex comparison.
4. By lem-pur-finite-orientation-normalization-isomorphism, alpha' transports to a
   normalized alpha_P with G_P, and e^*(alpha_P.inv) ; B_e = c_e ; alpha'.inv.
5. Apply lem-route-finite-orientation-base-change to the literal fibre product,
   with g, alpha, G_P and alpha_P. It gives p^*(alpha.inv) ; b_0 = c_p ; alpha_P.inv.
6. Naturality of m and functoriality identify the left side with
   m_L ; e^*(p^*(alpha.inv) ; b_0) ; B_e. Steps 5 and 4 make this
   m_L ; e^*(c_p) ; c_e ; alpha'.inv. Finally
   lem-pur-vector-integration-base-coefficient-composition identifies the first three
   factors with c_u', using the fixed roots and ordered pure-tensor normalization.
   The exceptional map throughout is the one of the supplied witness sq. -/
theorem finite_orientation_cartesian_transport
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (X Y X' Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left] [IsNoetherian X'.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left) (d : ℕ)
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [SmoothOfRelativeDimension d f.left]
    (n : ℕ) (_hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f.left f.left) (pullback.diagonal f.left))
    (g' : @Etale.FiniteRingSectionDeformation.Geometry
      (pullback f'.left f'.left) X'.left d
      (pullback.fst f'.left f'.left) (pullback.diagonal f'.left)
      (@IsSeparated.isClosedImmersion_diagonal _ _ f'.left
        (MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(X'.left, ⊤)))
    (alpha : Etale.dualizingComplex A f.left ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
    (alpha' : @Etale.dualizingComplex A _ _ X'.left Y'.left f'.left
        (HasCompactification.of_isPullback sq) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X'.left d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d g hX alpha)
    (_ha' : @Etale.FiniteSmoothPurity.OrientationNormalized A _ _ (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA X'.left Y'.left _ f'.left
      (HasCompactification.of_isPullback sq)
      (MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance)
      (MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance)
      d g' hX' alpha') :
    (Etale.ordinaryFinitePullback A u'.left).map alpha.inv ≫
        @Etale.dualizingComplexBaseChangeMap A _ _
          X.left Y.left X'.left Y'.left f.left v.left f'.left u'.left _
          (HasCompactification.of_isPullback sq)
          (MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance) sq =
      (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
        (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) hA)
        u'.left hX d).hom ≫ alpha'.inv := by
  sorry

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
