/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.AbelianVariety.HomogeneousCoherentAcyclicity
import Sheaf.AlgebraicGeometry.ProperStability
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Sheaf.AlgebraicGeometry.PicardKunnethQcoh

/-! # Translation differences of an ample invertible module

Source: Milne, Abelian Varieties, Chapter I, Proposition 8.14, p.39,
with Proposition 8.4(b), pp.35–36, and the definition of lambda on p.34.
(blueprint: lem-sfb-ample-translation-difference-surjectivity)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Every homogeneous invertible module is a translation difference of a specified ample
invertible module on an abelian variety over an algebraically closed field. The translation
is right translation x ↦ x + a, the pullback is tensor inverse image, and the inverse of M
is its sheaf dual Hom(M,O_A). All dimensions and characteristics are included.

Source: Milne, Abelian Varieties, I Proposition 8.14, p.39, with the homogeneous
criterion of Proposition 8.4(b), pp.35–36, and lambda_M on p.34.
(blueprint: lem-sfb-ample-translation-difference-surjectivity)

Proof (the node's cohomological argument, not an identification with algebraic equivalence):
1. By def-sc-abelian-variety, lem-sc-abelian-variety-characterization and
lem-sc-av-commutative, A is nonempty, smooth, proper and geometrically integral with
commutative group law. Its smooth dimension is constant, say g, by def-sbc-smooth-morphisms.
Choose r > 0 with B = M^r very ample (def-sc-ample); its projective embedding makes B
absolutely ample by lem-weil-pbc-projective-ample-invertible. The top exterior power omega
of the differentials is invertible by lem-sc-smooth-omega-finite-locally-free, including
g = 0. Both O_A and omega tensor L are coherent by lem-trf-proper-field-invertible-coherent.
2. By lem-weil-pbc-coherent-twist-global-generation, choose q > 0 so that N = B^q and
omega tensor N tensor L are globally generated. Evaluation at the identity shows their
spaces of global sections are nonzero. Write n = rq, so N = M^n.
3. Apply lem-sfb-projective-line-module-serre-duality to omega tensor N tensor L in
degree g. It identifies H^g(A,N inverse tensor L inverse) with the nonzero dual of
H^0(A,omega tensor N tensor L).
4. Pull thm-sc-theorem-of-cube for N back along x ↦ (x,a,b). The constant factors are
trivial and lem-pc-module-pullback-identity-composition and
lem-weil-pbc-module-pullback-tensor give the square identity. Hence
D_b = t_b^*N tensor N inverse is homogeneous and D_(a+b) is D_a tensor D_b.
On A times A set F = m^*N tensor p1^*(N inverse tensor L inverse). Its p2-fibre over b
is D_b tensor L inverse. If all these fibres are nontrivial, their cohomology vanishes
by lem-sfb-homogeneous-coherent-acyclicity.
5. The projection p2 is proper (lem-kun-proper-stability), smooth
(lem-sbc-smooth-relative-dimension-permanence), flat and locally finitely presented
(lem-pc-smooth-flat), hence finitely presented. F is relatively flat and finitely
presented in local line frames. Apply lem-pc-universal-finite-free-complex locally on A.
At every closed point its residue complex is exact by step 4 and
lem-weil-pbc-closed-point-residue-field-base.
6. At a closed point invert a nonzero maximal minor of the final differential. Split
off a two-term identity complex and repeat. Exactness of the residue complex makes the
last surviving free term zero. Thus the complex is locally contractible there.
The resulting opens cover A by lem-sc-lft-over-field-jacobson-space, so every higher
direct image of F under p2 vanishes.
7. The finite abutment filtrations of lem-sfb-ringed-site-leray-spectral-sequence give
H^i(A times A,F) = 0 in every degree. The shear u(x,b) = (x,x+b), inverse (x,y) ↦ (x,y-x),
identifies F with the pullback of E = p1^*(N inverse tensor L inverse) tensor p2^*N.
Tensor pullback composition and lem-weil-pbc-module-cohomology-fmap-functorial identify
their cohomology, so E also has zero cohomology.
8. Properness makes A quasi-compact and separated; its diagonal is affine by
lem-weil-pbc-closed-immersion-integral-separated-uc. Apply lem-sc-picard-kunneth-qcoh.
The (g,0) summand of H^g(A times A,E) is nonzero by steps 2 and 3, since a tensor of
nonzero vectors over a field is nonzero. This contradiction gives some b with
L isomorphic to t_b^*N tensor N inverse. The same argument covers g = 0.
9. Tensor pullback identifies this difference for N = M^n with the nth tensor power
of the difference for M. The square identity of step 4, now applied to M, identifies
that power with t_(nb)^*M tensor M inverse by induction. Take a = nb. This uses no
extraction of roots and no division by n, so imposes no characteristic restriction. -/
theorem IsAbelianVariety.exists_iso_translation_tensor_dual_of_homogeneous
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (M : A.left.Modules) (hM : IsAmple A.hom M)
    (L : A.left.Modules) [Scheme.Modules.IsInvertible L]
    (homogeneous : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ A,
      Nonempty ((Scheme.Modules.tensorPullback (GrpObj.mulRight A b).left).obj L ≅ L)) :
    ∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ A,
      Nonempty (L ≅
        (Scheme.Modules.tensorPullback (GrpObj.mulRight A a).left).obj M ⊗
          Scheme.Modules.dual M) := by
  sorry

end AlgebraicGeometry
