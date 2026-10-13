/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Tor independence and tensor augmentation

Source: Stacks Project, Tags 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-tensor-augmentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace ModuleCat

/-- Tensoring a K-flat resolution of B with an A-K-flat complex preserves its augmentation.
Source: Stacks Project, Tags 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-tensor-augmentation).

Proof: First use a bounded-above projective resolution G of B in nonpositive degrees.
Balanced Tor, computed by resolving A and B and comparing the two finite-diagonal
filtrations, identifies the negative cohomology of A tensor G with Tor_i(A,B).
Positive cohomology vanishes and degree-zero cohomology is A tensor B. Thus Tor
independence makes the augmentation A tensor G to A tensor B a quasi-isomorphism.
Its cone is acyclic over A. Tensor this cone with Q, which preserves acyclicity by
hK. The signed tensor-cone identification and mixed associativity identify the
result with the cone of Q tensor G to Q tensor B, after restriction to R.
For an arbitrary R-K-flat resolution F, take a K-flat resolution H of the
homotopy pullback of F and G over B[0]. The two projection maps are
quasi-isomorphisms between K-flat complexes. Tensoring these maps with the
restriction of Q preserves quasi-isomorphisms, by K-flat resolution invariance
in the first variable. The augmentation triangles commute, so two-out-of-three
transports the result from G to F. Tensor symmetry gives the stated ordering.
No boundedness of Q or F is required. Zero rings and complexes are covered:
the same Tor and cone calculations give zero homology. -/
theorem tensorAugmentation_quasiIso_of_torIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      ((restrictScalars (algebraMap R B)).obj (of B B)))
    (hf : QuasiIso f) :
    QuasiIso ((((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q)
      ◁ f) := by sorry

end ModuleCat
