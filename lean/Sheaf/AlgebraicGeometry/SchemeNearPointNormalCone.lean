/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.NormalConeFibreConstructions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.QuasiFinite.Basic
import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.DimensionAtPointComponents
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # The normal cone at a near point, allowing nonreduced schemes

Source: Cossart--Jannsen--Saito, March 12, 2009 preprint, section 2,
Theorems 2.2(2), 2.3 and 2.14, pp.28--29,36; BMT sections 6.1 and 6.3
(blueprint: lem-per-scheme-near-point-normal-cone).

The constructions of the reduced statement are reused; its theorem is not invoked.
The Rees-monomial normalization specifies the canonical exceptional-fibre map.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry.HilbertSamuel

/-- Extended and raw near-point equalities agree for arbitrary residue extensions.
Source: CJS Theorem 2.10(2), pp.32--33, and Remark 1.41, p.27
(blueprint: lem-per-scheme-near-point-normal-cone).

Proof (node Step 4): use the residue-field map of the blowup and transport along `hy`.
Finite type makes both transcendence degrees finite. The tower formula
`lem-kun-transcendence-degree-tower` gives t_y = t_x + delta. Iterating inclusive
summation rewrites H_y = H_x as Lambda^t_x (Lambda^delta h_y) = Lambda^t_x h_x.
Inclusive summation is injective: recover f(0) at zero and f(n) by the difference of
the values at n and n-1 for n positive. Cancel its t_x iterates in one direction;
apply them in the other. No rationality or closedness of either point is used. -/
theorem near_function_iff_raw {X C P : Scheme.{u}}
    (p : P ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ P) (c : C ⟶ X)
    [Smooth p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    [IsClosedImmersion c] [Smooth (c ≫ i ≫ p)]
    (z : C) (y : c.ker.blowup) (hy : c.ker.blowupMap y = c z) :
    function (c.ker.blowupMap ≫ i ≫ p) y = function (i ≫ p) (c z) ↔
      (summation^[Cardinal.toNat
        (@Algebra.trdeg (X.residueField (c z)) (c.ker.blowup.residueField y) _ _
          ((X.residueFieldCongr hy).inv ≫ c.ker.blowupMap.residueFieldMap y).hom.toAlgebra)])
        (localFunction c.ker.blowup y) = localFunction X (c z) := by
  sorry

/-- Normal flatness and the polynomial directrix at a near point, with nilpotents allowed.
Source: CJS section 2, Theorems 2.2(2), 2.3(1)--(2), 2.14, pp.28--29,36;
BMT sections 6.1 and 6.3 (blueprint: lem-per-scheme-near-point-normal-cone).

Proof, following the node's ten steps:
1. Work in an affine neighbourhood where the ambient embedding is closed. Finite type
   gives Noetherianity (`lem-weil-pbc-finite-type-over-noetherian`). The conormal stalk
   formulas identify A with the centre's local ring (`lem-pur-conormal-graded-algebra`).
   Smoothness gives regularity (`lem-weil-pbc-smooth-scheme-over-field-regular`) and a
   domain (`lem-sc-regular-local-domain`). There are finitely many centre components
   (`lem-weil-pbc-noetherian-finitely-many-components`), corresponding to minimal primes
   (`lem-weil-pbc-spec-irreducible-components-minimal-primes`). Remove the others and
   shrink inside the neighbourhood where the extended function is constant.
2. The dimension formulas `lem-weil-pbc-dimension-at-point-local-ring-trdeg`,
   `lem-weil-pbc-dimension-at-point-components` and
   `lem-sc-closed-irreducible-dimension-trdeg` give t_eta = t_x + dim A. Constancy and
   injectivity of inclusive summation yield h_R = Lambda^(dim A) h_(R_I).
3. Apply `lem-per-bennett-normal-flat-local-criterion`, which allows nilpotents, to obtain
   A-flatness of G. This is flatness of the actual ring, not of its reduction.
4. The tower formula `lem-kun-transcendence-degree-tower` and cancellation of summation
   give the raw near equality, as stated in `near_function_iff_raw` above.
5. The blowup glue datum and local model (`def-nagata-global-blowup-glue-data`,
   `def-nagata-global-blowup-local-model`) identify local charts with Proj of the Rees
   algebra (`def-nagata-affine-blowup`, `def-nagata-rees-algebra`). Localize at x and
   base change Proj to k (`lemma-nagata-relative-proj-base-change-arbitrary`). In degree
   n the fibre and k tensor_A G_n are both I^n/m I^n since I^(n+1) is contained in m I^n.
   Multiplication agrees on representatives, giving the monomial-specified pullback.
6. If a minimal prime contains I, primeness forces it to equal I. Localization at I
   (`def-weil-pbc-localization-at-prime`) has only one prime; its maximal ideal consists
   of nilpotents (`lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`). Finite
   generation gives I^N R_I = 0 for some N. Each a in I^N is killed by some s outside I.
   Flatness over the domain A gives torsion-freeness
   (`lem-trf-flat-module-torsionfree-domain`), hence its degree-N class is zero.
   Thus I^N = I^(N+1). Nakayama (`lem-weil-pbc-nakayama-local-generators`) gives I^N = 0.
   All positive-degree Rees elements are then nilpotent, so Proj is empty, contradicting y.
7. Finite generators of I present S as a standard graded quotient P = k[Z]/K
   (`def-pc-standard-graded-algebra`). The local theorem
   `lem-per-scheme-near-point-additive-action` gives a proper homogeneous subgroup ideal
   L contained in the point's inverse-image prime, with g(Z+W) in K(Z)+L(W) for g in K.
   Evaluation at Z=0 shows K is contained in L.
8. In characteristic zero L is generated by L_1. Otherwise a least-degree nonzero
   homogeneous f after quotienting by L_1 has degree r at least two. The (1,r-1)
   component of comultiplication makes all partial derivatives vanish; Euler's identity
   contradicts r f nonzero. Choose coordinates L=(U), with at least one remaining T
   because the point's prime does not contain the irrelevant ideal.
9. The translation inclusion makes all divided T derivatives preserve K. The finite
   Taylor formula shows evaluation at T=0 preserves K, so each T coefficient belongs
   to J=K intersect k[U]. Hence K=J[T], with factorials invertible in characteristic zero.
10. Take B=k[U]/J with its standard grading. Then S=B[T], and L in the point's prime is
    exactly containment of B_+. The surjective graded Proj map
    (`prop-nagata-relative-proj-functoriality`) identifies this closed locus with Proj k[T].
    Prime containment works for all scheme points, including nonclosed points. -/
theorem near_normal_cone_nonreduced {X C P : Scheme.{u}}
    (p : P ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ P) (c : C ⟶ X)
    [Smooth p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    [IsClosedImmersion c] [Smooth (c ≫ i ≫ p)]
    (hconstant : IsLocallyConstant (fun z : C ↦ function (i ≫ p) (c z)))
    (z : C) (y : c.ker.blowup) (hy : c.ker.blowupMap y = c z)
    (hnear : function (c.ker.blowupMap ≫ i ≫ p) y = function (i ≫ p) (c z)) :
    Module.Flat (X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z)
      (Ideal.associatedGraded (centerStalkIdeal c z)) ∧
    ∃ (_ : GradedAlgebra (normalFibreGrade c z))
      (φ : reesGrading (centerStalkIdeal c z) →+*ᵍ normalFibreGrade c z)
      (hirr : HomogeneousIdeal.irrelevant (normalFibreGrade c z) ≤
        (HomogeneousIdeal.irrelevant (reesGrading (centerStalkIdeal c z))).map φ),
      (∀ (n : ℕ) (a : (centerStalkIdeal c z ^ n : Ideal (X.presheaf.stalk (c z)))),
        φ (reesMonomial (centerStalkIdeal c z) a.val a.property) =
          (1 : X.residueField (c z)) ⊗ₜ[X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z]
            DirectSum.of (Ideal.associatedGradedPiece (centerStalkIdeal c z)) n
              (Submodule.Quotient.mk a)) ∧
      ∃ (U : X.affineOpens) (hx : c z ∈ U.1)
        (hI : (c.ker.ideal U).map (X.presheaf.germ U.1 (c z) hx).hom = centerStalkIdeal c z),
        IsPullback
          (Proj.map φ hirr ≫
            AffineBlowup.hom (X.presheaf.germ U.1 (c z) hx).hom hI ≫ c.ker.blowupι U)
          (Proj.toSpecOfAlgebra (normalFibreGrade c z)) c.ker.blowupMap
          (X.fromSpecResidueField (c z)) ∧
        ∃ (t : Proj (normalFibreGrade c z)) (B : Type u) (_ : CommRing B)
          (_ : Algebra (X.residueField (c z)) B)
          (𝓑 : ℕ → Submodule (X.residueField (c z)) B)
          (_ : GradedAlgebra 𝓑) (_ : GradedAlgebra.IsStandard 𝓑)
          (r : ℕ) (e : normalFibre c z ≃ₐ[X.residueField (c z)] MvPolynomial (Fin r) B),
          1 ≤ r ∧
          (∀ (n : ℕ) (s : normalFibre c z),
            s ∈ normalFibreGrade c z n ↔ e s ∈ normalPolynomialGrade 𝓑 r n) ∧
          (Proj.map φ hirr ≫
            AffineBlowup.hom (X.presheaf.germ U.1 (c z) hx).hom hI ≫ c.ker.blowupι U) t = y ∧
          ∀ (n : ℕ), 0 < n → ∀ b ∈ 𝓑 n,
            e.symm (MvPolynomial.C b) ∈ t.asHomogeneousIdeal.toIdeal := by
  sorry


end AlgebraicGeometry.HilbertSamuel
