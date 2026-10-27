/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedModuleScalarActionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.CategoryTheory.DerivedCategory.PerfectComplexDerivedBiduality
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction

/-! # Polynomial relative duality over arbitrary commutative bases

Source: Stacks Project, dualizing.tex, Tag 0BZW, proof of (1)(a)--(c) and (2)(a),
with the arbitrary-base extension supplied by more-algebra.tex, Tags 067J, 068X,
0658, 07VI and 0E1T (blueprint: lem-sfb-arbitrary-polynomial-dual-properties).

The dual is the shifted derived coinduction object with its precomposition action.
The scalar map is the existing transpose of the identity; no Noetherian hypothesis
or nonzero-ring hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- The polynomial relative dual C_{P→A}(P[0])[n], with the coinduced A-action
(a h)(a') = h(a'a). The construction uses the existing total right derived coinduction,
computed on K-injective representatives, followed by the cohomological shift n.
Source: Stacks 0A70, 0A71 and 0BZW, polynomial model in the proof of (1)
(blueprint: lem-sfb-arbitrary-polynomial-dual-properties). -/
def polynomialRelativeDual {R A : Type u} [CommRing R] [CommRing A]
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    [HasDerivedCategory.{u} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)] :
    DerivedCategory (ModuleCat.{u} A) :=
  ((derivedCoinduction p).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
      (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))))⟦(n : ℤ)⟧

/-- The polynomial dual of a flat finitely presented algebra is relatively perfect,
its polynomial restriction is perfect, and its actual scalar-action map is invertible.
Here relative perfection is expanded as pseudo-coherence over A and one finite Tor
interval over R, uniform in every R-module. The derived tensor in torAmplitudeIn is
computed by the existing K-flat derived monoidal structure.
Source: Stacks 0BZW, proof of (1)(a)--(c) and (2)(a), extended to arbitrary bases by
more-algebra.tex, Tags 067J, 068X, 0658, 07VI and 0E1T
(blueprint: lem-sfb-arbitrary-polynomial-dual-properties).

Proof (the node's six steps):
1. lem-sfb-flat-fp-polynomial-pseudocoherent makes A[0] pseudo-coherent over this P.
   lem-trf-base-flat-polynomial-tor-bound gives Tor_j^P(A,N)=0 for j>n. A nonpositive
   projective resolution is termwise flat and K-flat by lem-pc-module-bounded-flat-kflat.
   lem-pc-source-kflat-module-tensor-model and def-weil-pbc-tor-modules identify its
   tensor cohomology with Tor, giving amplitude [-n,0], including positive vanishing.
2. lem-pc-ring-pseudo-coherent-finite-tor-perfect supplies a bounded finite-projective
   P-model of A[0]. This proves the first conjunct with def-pc-perfect-ring-complex.
3. Perfect duality (lem-trf-perfect-complex-derived-biduality), in the monoidal derived
   category of lem-sf-ringed-derived-closed-symmetric-monoidal, makes RHom_P(A,P) perfect.
   lem-trf-derived-coinduction-adjunction identifies the restriction of the coinduced
   dual with this object. Shift its bounded finite-projective model by n: UC is perfect.
   lem-pc-pseudo-coherent-bounded-finite-free-model also makes UC pseudo-coherent.
4. P is R-free on monomials, hence R-flat and finitely presented. Apply the reverse
   implication of lem-sfb-flat-fp-quotient-pseudocoherent (Tag 0E1T) to UC, obtaining
   pseudo-coherence of C over A. This uses no Noetherian cohomology criterion.
5. A bounded finite-projective P-model of UC has R-flat terms, since each is a retract
   of a free P-module and P is R-free. It is K-flat over R by
   lem-pc-module-bounded-flat-kflat. lem-pc-source-kflat-module-tensor-model computes
   tensor with each R-module by this bounded model. Its finite support gives a single
   interval [a,b], a≤b, for all test modules. For the zero complex take a=b=0.
6. lem-trf-algebraic-shriek-derived-hom-adjunction identifies the actual scalar map,
   after restriction to P and cancellation of the two shifts, with the canonical
   P-bidual evaluation of A[0]. Its normalization is (a h)(1)=h(a), so it identifies
   the prescribed map itself. Perfect biduality from step 2 makes that map invertible;
   conservative restriction (lem-trf-derived-coinduction-adjunction) reflects this.
   The construction and each argument include n=0 and A=0. -/
theorem polynomialRelativeDual_properties
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    (n : ℕ) (p : MvPolynomial (Fin n) R →ₐ[R] A)
    [HasDerivedCategory.{u} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (hp : Function.Surjective p) :
    DerivedCategory.IsPerfectRingComplex
        ((restrictScalars p.toRingHom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ∧
      DerivedCategory.IsPseudoCoherent (polynomialRelativeDual n p.toRingHom) ∧
      (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b
        ((restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (polynomialRelativeDual n p.toRingHom))) ∧
      DerivedCategory.IsPerfectRingComplex
        ((restrictScalars p.toRingHom).mapDerivedCategory.obj
          (polynomialRelativeDual n p.toRingHom)) ∧
      IsIso (derivedModuleScalarActionMap
        (polynomialRelativeDual n p.toRingHom)) := by
  sorry

end ModuleCat
