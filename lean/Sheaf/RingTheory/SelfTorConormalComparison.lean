/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KoszulComplex
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The normalized exterior-to-self-Tor map

Source: Stacks Project, Tags 09PQ and 062I.
(blueprint: new-r4-self-tor-conormal-comparison). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The exterior conormal, regarded as a module over the ambient ring.
Source: Stacks Project, Tag 062I.
(blueprint: new-r4-self-tor-conormal-comparison). -/
noncomputable abbrev conormalExteriorModule (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent))

/-- Koszul normalization of the comparison. For every tuple of ideal elements, lift
its Koszul augmentation to any projective resolution of the quotient. A degree-n wedge,
after tensoring with the quotient, is a cycle. Its image in resolution homology is
the value of the comparison on the wedge of the corresponding conormal classes.
This fixes the comparison, since these wedges generate the exterior power.
Source: Stacks Project, Tags 09PQ and 062I.
(blueprint: new-r4-self-tor-conormal-comparison). -/
def IsSelfTorConormalComparison (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) : Prop :=
  ∀ (r : ℕ) (g : Fin r → I) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex),
    a.f 0 ≫ P.π.f 0 =
      ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) →
    let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
    let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    ∀ (v : Fin n → (Fin r →₀ A)) (z : (T.obj K).cycles n),
      (T.obj K).iCycles n z =
        (exteriorPower.ιMulti A n v) ⊗ₜ[A] (1 : A ⧸ I) →
      (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom
          (c (exteriorPower.ιMulti (A ⧸ I) n
            (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))) =
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
          (T.map a)) ((T.obj K).homologyπ n z)

/-- There is a unique comparison with Koszul normalization, without regularity assumptions.

Source: Stacks Project, Tag 09PQ, the resolution-independent strictly commutative Tor
algebra, and the boundary identification Tor_1(A/I,A/I) = I/I² used with Tag 062I.
(blueprint: new-r4-self-tor-conormal-comparison).

Proof: Resolve A/I by a Tate free strictly commutative dg algebra. A lift of an ideal
element to degree one gives a cycle after tensoring with A/I. Changing the lift changes
its homology class by a boundary; the quotient exact sequence identifies this class
with the ideal element modulo I². Multiply n such classes. Strict commutativity makes
this product alternating, including in characteristic two, and it is A/I-multilinear.
The exterior universal property therefore gives the displayed A-linear map. Comparison
of resolutions identifies the product with the top Koszul wedge for every tuple g:
the map from the Koszul dg algebra to the Tate resolution sends each generator to its
chosen degree-one lift. Every chain lift a has the same effect on homology, because
the source is a bounded complex of projective modules and two lifts of its augmentation
to a projective resolution are chain homotopic. Thus the map has the displayed
normalization for every P and a. Conversely these lifts exist, and every pure wedge of
conormal classes has lifts in I. The normalization determines every pure wedge, so
exterior generation gives uniqueness. For n=0 it is the quotient unit; zero quotients
and the zero ideal satisfy the same construction. -/
theorem existsUnique_selfTor_conormal_comparison (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), IsSelfTorConormalComparison A I n c := by sorry

/-- The actual normalized exterior-to-self-Tor comparison. The theorem used to select it
fixes its value on all pure wedges, and determines it uniquely.
Source: Stacks Project, Tag 09PQ.
(blueprint: new-r4-self-tor-conormal-comparison). -/
noncomputable def selfTorConormalComparison (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)) :=
  (existsUnique_selfTor_conormal_comparison A I n).exists.choose

/-- The canonical comparison has its defining normalization.
Source: Stacks Project, Tag 09PQ.
(blueprint: new-r4-self-tor-conormal-comparison). -/
theorem selfTorConormalComparison_spec (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    IsSelfTorConormalComparison A I n (selfTorConormalComparison A I n) :=
  (existsUnique_selfTor_conormal_comparison A I n).exists.choose_spec

end AlgebraicGeometry
