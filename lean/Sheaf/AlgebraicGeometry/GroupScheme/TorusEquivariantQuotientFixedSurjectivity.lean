/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.GroupScheme.UniversalActionFixedPoints
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Torus fixed subgroups of equivariant quotients

Source: Conrad, Reductive group schemes, Corollary 3.3.5, proof, printed p.101,
using Borel, Linear Algebraic Groups, 11.14, Corollary 2.
(blueprint: lem-sfb-torus-equivariant-quotient-fixed-surjectivity).

Fixed subgroups are specified on every test scheme after every further base change.
The kernel clause uses all test schemes, including nonreduced ones, and the existing
fppf quotient predicate retains the canonical kernel inclusion and quotient map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- An equivariant faithfully flat homomorphism of smooth connected affine groups
induces a faithfully flat finitely presented map on torus fixed subgroups, with
kernel the universally fixed part of the original scheme-theoretic kernel and with
the indicated fppf quotient presentation. No condition is imposed on the kernel.

Source: Conrad, Reductive group schemes, Corollary 3.3.5, proof, printed p.101,
and Milne, Algebraic Groups (2017), Chapters 5, 10, 12, 13 and 17.
(blueprint: lem-sfb-torus-equivariant-quotient-fixed-surjectivity).

Proof plan:
1. Apply lem-sfb-reduced-normal-kernel-factorization to write q=b a, where a is
   the smooth quotient by the reduced kernel and b is finite faithfully flat
   radicial. By lem-sfb-relative-torus-automorphism-fixed-group the fixed groups
   of H, the intermediate group P, and J are smooth, connected and affine.
2. The tangent map of a is surjective by
   lem-sfb-homogeneous-cotangent-associated-bundle. The weight decompositions of
   lem-sfb-split-torus-representation-weight-decomposition show surjectivity on
   invariant tangent vectors: the zero-weight part of a lift lifts a fixed vector.
3. Evaluating universal fixedness on dual numbers identifies Lie(G^R) with
   Lie(G)^R naturally, so the tangent map of a^R is surjective.
4. Factor a^R through its closed image by
   lem-sfb-algebraic-group-homomorphism-factorization. Smoothness descends by
   lem-sbc-smooth-flat-surjective-source-descent. The surjective tangent map and
   lem-sfb-smooth-subgroup-full-tangent identify the image with connected P^R.
5. A k-point of J^R has a unique preimage under radicial b. Equivariance makes
   that preimage R(k)-fixed. Apply lem-wf-affine-nullstellensatz-vanishing on the
   reduced Laurent torus to identify its orbit morphism with the constant one;
   the preimage is universally fixed, even when b is inseparable.
6. Factor b^R through its closed image. Its image contains every k-point of J^R.
   This target is reduced by sbc-lem-smooth-geometrically-reduced, so the same
   Nullstellensatz makes the image ideal zero. Both a^R and b^R are faithfully
   flat and finitely presented. Compose using lem-pc-flat-compose and
   lem-weil-pbc-finite-presentation-base-change-composition.
7. On every test scheme the kernel consists exactly of universally fixed h
   with q(h)=1. This identifies the scheme-theoretic kernels by Yoneda without
   replacing the original kernel by its reduction.
8. The quotient clause of lem-sfb-algebraic-group-homomorphism-factorization
   now identifies J^R with the fppf sheafification of the kernel coset presheaf.
-/
theorem torus_equivariant_quotient_fixed_surjectivity
    {k : Type u} [Field k] [IsAlgClosed k]
    (H J R : Grp (Over (Spec (.of k))))
    [IsAffine H.X.left] [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [IsAffine J.X.left] [Smooth J.X.hom] [ConnectedSpace J.X.left]
    [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    (r : ℕ) (hR : Nonempty (R ≅ MultiplicativeType.splitTorus k r))
    [ModObj R.X H.X] [ModObj R.X J.X]
    (hH : ∀ (U : Over (Spec (.of k))) (t : U ⟶ R.X) (x y : U ⟶ H.X),
      t • (x * y) = (t • x) * (t • y))
    (hJ : ∀ (U : Over (Spec (.of k))) (t : U ⟶ R.X) (x y : U ⟶ J.X),
      t • (x * y) = (t • x) * (t • y))
    (q : H ⟶ J) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [IsModHom R.X q.hom.hom] :
    ∃ (HF JF : Grp (Over (Spec (.of k)))) (iH : HF ⟶ H) (iJ : JF ⟶ J)
      (qF : HF ⟶ JF),
      IsClosedImmersion iH.hom.hom.left ∧ IsClosedImmersion iJ.hom.hom.left ∧
      (∀ (U : Over (Spec (.of k))) (x : U ⟶ H.X),
        (∃ z : U ⟶ HF.X, z ≫ iH.hom.hom = x) ↔
          x ∈ universalActionFixedPoints R H.X U) ∧
      (∀ (U : Over (Spec (.of k))) (x : U ⟶ J.X),
        (∃ z : U ⟶ JF.X, z ≫ iJ.hom.hom = x) ↔
          x ∈ universalActionFixedPoints R J.X U) ∧
      qF ≫ iJ = iH ≫ q ∧
      Flat qF.hom.hom.left ∧ Surjective qF.hom.hom.left ∧
      LocallyOfFinitePresentation qF.hom.hom.left ∧
      QuasiCompact qF.hom.hom.left ∧ QuasiSeparated qF.hom.hom.left ∧
      (∀ (U : Over (Spec (.of k))) (x : U ⟶ H.X),
        (∃ z : U ⟶ GrpObj.ker qF.hom.hom,
          z ≫ GrpObj.kerι qF.hom.hom ≫ iH.hom.hom = x) ↔
        x ≫ q.hom.hom = 1 ∧
          x ∈ universalActionFixedPoints R H.X U) ∧
      IsFppfGroupQuotient (Grp.ofHom (GrpObj.kerι qF.hom.hom)) qF := by
  sorry

end AlgebraicGeometry
