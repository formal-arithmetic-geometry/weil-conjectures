/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # The scalar extension of resolutions under Tor independence

Source: Stacks Project, More on Algebra, Section 06Y5 and Tag 06Y6;
Tag 08IB, the Tor-independent affine calculation.
(blueprint: lem-pc-tor-independent-kflat-resolution-tensor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ModuleCat

/-- A K-flat resolution over R of the restriction of an A-K-flat complex
still computes ordinary extension to B if A and B are Tor independent over R.
Source: Stacks Project, Tags 06Y5, 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-kflat-resolution-tensor).

Proof: Resolve B[0] over R by a bounded-above projective complex F with
augmentation f. The complex A tensor_R F has cohomology E = A tensor_R B in
degree zero and Tor_i^R(A,B) in degree -i; it has zero positive cohomology.
Balancedness follows by resolving both A and B and comparing the two
filtrations of the double tensor complex, with finite diagonals in each degree.
Thus Tor vanishing makes A tensor_R f a quasi-isomorphism of A-complexes.
Its cone is acyclic. Tensoring this cone with Q over A preserves acyclicity by
hK. The signed tensor-cone identification and mixed tensor associativity show
that Q tensor_R F -> Q tensor_R B is a quasi-isomorphism after restriction to R.
The same augmentation for P is a quasi-isomorphism by its R-K-flatness.
Tensoring s with F is a quasi-isomorphism because F is bounded above with
projective, hence flat, terms and therefore R-K-flat. The commuting tensor
square, with three sides now quasi-isomorphisms, makes s tensor_R B a
quasi-isomorphism. Tensor symmetry identifies this with restriction of the
termwise scalar extension of s to B. Exact restriction reflects homology
isomorphisms, giving the asserted B-linear quasi-isomorphism. No boundedness
of Q or P is used. The argument also applies to zero complexes and rings. -/
theorem scalarExtension_quasiIso_of_torIndependent_kFlat
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (s : P ⟶ (((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hs : QuasiIso s) :
    QuasiIso (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map s) := by
  sorry

end ModuleCat
