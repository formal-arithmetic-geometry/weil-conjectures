/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.RingTheory.Depth
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.RingTheory.Support
import Sheaf.Algebra.Homology.NormalizedDualizingDepthDetection

/-! # Concentration of normalized duality over a Cohen–Macaulay local ring

Source: Stacks Project, dualizing.tex, Tag 0AWS (lemma-apply-CM), with full support
as in Tag 0AWE (lemma-depth-dualizing-module).
(blueprint: lem-sfb-normalized-cm-local-dualizing-concentration).

The four dualizing conditions are stated inline using the existing ordinary-module
RHom. The canonical scalar-action map is the enriched identity `MonoidalClosed.id`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- A normalized algebraic dualizing complex over a Cohen–Macaulay local ring of
finite dimension `d` is its degree `-d` cohomology shifted by `d`. This module is
nonzero, finite, nonzero at every prime, and has depth `d`.

Source: Stacks Project, dualizing.tex, Tag 0AWS, equivalence (1)--(3) and its final
assertion; full support is the Cohen–Macaulay case of Tag 0AWE(1).
(blueprint: lem-sfb-normalized-cm-local-dualizing-concentration).

Proof (the accepted DAG split):
1. Choose the bounded injective representative J. By
[lem-weil-pbc-bounded-below-injectives-kinjective], it is K-injective, and
[def-pur-derived-internal-hom] and [def-pur-hom-complex] compute RHom(A[0],K)
by Hom(A[0],J), identified with J by evaluation at 1. The support of A is all
of Spec(A), since its annihilator is zero and
[lem-weil-pbc-finite-module-support-annihilator] applies. Thus its support
dimension is d. Apply [lem-sfb-normalized-dualizing-depth-detection] to A:
its degree bounds give vanishing below -d and above 0; its depth clause, using
depth(A) = d, gives nonvanishing in degree -d and vanishing in degrees -t for
0 <= t < d. Hence every cohomology degree other than -d vanishes.
2. Put r = -d and W = H^r(J). It is nonzero by Step 1 and finite by hypothesis.
Form the good truncation T: its terms are J^j below r, ker(d_J^r) in degree r,
and zero above r. The inclusion T -> J is a quasi-isomorphism by Step 1.
The quotient T -> W[d], given in degree r by cycles modulo boundaries, is
also a quasi-isomorphism. Invert these maps in the derived category
[def-weil-abstract-derived-category] to obtain K isomorphic to W[d].
3. If a annihilates W, it kills every term of Hom(W[d],J), since
(af)(w) = f(aw) = 0. By Step 2 and the K-injectivity of J this computes
RHom(K,K). The scalar-action isomorphism identifies its degree-zero cohomology
A-linearly with A, so a = a * 1 = 0. Thus Ann(W) = 0, and the finite-module
support-annihilator criterion gives nonzero localization at every prime.
4. Let C = Hom(W[0],J), computing RHom(W[0],K). Degree n of Hom(W[d],J) is
Hom(W,J^(n-d)); multiplication by (-1)^(dn) identifies this complex with C[-d],
including the shift signs in the differentials. By Step 2 and homothety,
C[-d] is isomorphic to A[0], so C is isomorphic to A[d]. Since A is nonzero,
C has nonzero cohomology exactly in degree -d. Apply the depth clause of
[lem-sfb-normalized-dualizing-depth-detection] to the nonzero finite module W:
the least t >= 0 with H^(-t)(C) nonzero is d, proving depth(W) = d.
-/
theorem normalizedCMDualizing_concentration
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (hdepth : IsLocalRing.depth (R := A) A = (d : ℕ∞))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hKinjective : ∃ J : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (J.X i)) ∧
      (∀ i : ℤ, Injective (J.X i)) ∧ Nonempty (Q.obj J ≅ K))
    (hKfinite : ∀ i : ℤ, Module.Finite A
      ((homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hKscalar : IsIso (MonoidalClosed.id K))
    (hKnormalized : Nonempty
      ((ordinaryModuleDerivedInternalHom A).obj
        (op ((singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))), K) ≅
        (singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A)))) :
    Nonempty (K ≅
      ((singleFunctor (ModuleCat.{u} A) 0).obj
        ((homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K))⟦(d : ℤ)⟧) ∧
    Nontrivial ((homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) ∧
    ∃ hWfinite : Module.Finite A
        ((homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K),
      (∀ p : PrimeSpectrum A, Nontrivial (LocalizedModule p.asIdeal.primeCompl
        ((homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K))) ∧
      @IsLocalRing.depth A _ _
        ((homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) _ _ hWfinite =
          (d : ℕ∞) := by
  sorry

end DerivedCategory
