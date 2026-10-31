/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import WeilConjectures.AlgebraicGeometry.AffineFormallySmooth
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Unramified.Basic

/-!
# Formally étale maps and associated graded rings

Source: Stacks Project, Algebra, Lemma 0H1D and Lemma 00UR
(blueprint: lem-sfb-augmented-etale-associated-graded).

The helpers construct the canonical maps for every ideal-preserving ring homomorphism.
The main statement identifies these maps as isomorphisms under formal étaleness and
surjectivity modulo the target ideal. The source ideal is the inverse image of the
target ideal, which is exactly the kernel of the composite to its quotient.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Ideal

/-- The map on ideal-power quotients sends `[a]` to `[f a]`.
Source: Stacks Project, Algebra, Lemma 0H1D, canonical quotient maps
(blueprint: lem-sfb-augmented-etale-associated-graded). -/
def powerQuotientMap {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (f : A →+* C) (I : Ideal A) (J : Ideal C) (h : I ≤ J.comap f) (n : ℕ) :
    A ⧸ I ^ n →+* C ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f
    ((pow_le_pow_left' h n).trans (Ideal.le_comap_pow f n))

/-- The semilinear map on `I^n/I^(n+1)` sends the class of `a` to the class of `f a`.
Source: Stacks Project, Algebra, Lemma 0H1D, homogeneous-piece maps
(blueprint: lem-sfb-augmented-etale-associated-graded). -/
def associatedGradedPieceMap {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (f : A →+* C) (I : Ideal A) (J : Ideal C) (h : I ≤ J.comap f) (n : ℕ) :
    associatedGradedPiece I n →ₛₗ[f] associatedGradedPiece J n :=
  Submodule.mapQ
    (Submodule.comap (I ^ n).subtype (I ^ (n + 1)))
    (Submodule.comap (J ^ n).subtype (J ^ (n + 1)))
    (f.toSemilinearMap.restrict
      (fun _ hx ↦ ((pow_le_pow_left' h n).trans (Ideal.le_comap_pow f n)) hx))
    (fun _ hx ↦
      ((pow_le_pow_left' h (n + 1)).trans (Ideal.le_comap_pow f (n + 1))) hx)

/-- The canonical graded additive map is the direct sum of the maps on homogeneous pieces.
Its multiplication and scalar compatibility are asserted in the main theorem.
Source: Stacks Project, Algebra, Lemma 0H1D
(blueprint: lem-sfb-augmented-etale-associated-graded). -/
def associatedGradedMap {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (f : A →+* C) (I : Ideal A) (J : Ideal C) (h : I ≤ J.comap f) :
    associatedGraded I →+ associatedGraded J :=
  DirectSum.map (fun n ↦ (associatedGradedPieceMap f I J h n).toAddMonoidHom)

/-- Formal étaleness identifies all positive infinitesimal neighbourhoods and the
associated graded algebras by their canonical maps. Here `J.comap f` is the kernel
of `A → C/J`. The equality with `associatedGradedMap` pins the ring equivalence
to the actual map on representatives, in every degree including degree zero.
The final equality expresses linearity over `A/I = C/J` using the level-one
quotient identification, without choosing a new algebra structure.

Source: Stacks Project, Algebra, Lemma 0H1D
(blueprint: lem-sfb-augmented-etale-associated-graded).

Proof: (1) The quotient map at level one is bijective by surjectivity and the
definition of the kernel. (2) For `n ≥ 1`, `I^n/I^(n+1)` is square zero since
`2*n ≥ n+1`. Formal étaleness lifts `C → A/I^n` uniquely to `C → A/I^(n+1)`.
(3) Its image of `J` lies in `I/I^(n+1)`, so it kills `J^(n+1)` and factors
through `C/J^(n+1)`. The composite on `A/I^(n+1)` is the identity because the
lift is an `A`-algebra map. The other composite equals the identity by unique
lifting through `J^n/J^(n+1)`. (4) The quotient isomorphisms at consecutive
levels give bijectivity of each homogeneous-piece map; degree zero is level
one. (5) Their direct sum is bijective. The homogeneous product and scalar
formulas of lem-weil-pbc-associated-graded-ring-structure show that it preserves
products, one, and the quotient scalars. No Noetherianity, finite generation,
or equality `J = I*C` is used. -/
theorem formallyEtale_powerQuotient_associatedGraded
    {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (f : A →+* C) (J : Ideal C)
    (hform : @Algebra.FormallyEtale A C _ _ f.toAlgebra)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    (∀ n : ℕ, 1 ≤ n →
      Function.Bijective (powerQuotientMap f (J.comap f) J le_rfl n)) ∧
    ∃ e : associatedGraded (J.comap f) ≃+* associatedGraded J,
      e.toAddMonoidHom = associatedGradedMap f (J.comap f) J le_rfl ∧
      ∀ (a : A) (x : associatedGraded (J.comap f)),
        e ((Ideal.Quotient.mk (J.comap f) a) • x) =
          (Ideal.Quotient.mk J (f a)) • e x := by
  sorry

/-- Quotient maps are natural in every compatible square of ideal-preserving maps.
The target datum need not be formally étale for this compatibility.
Source: Stacks Project, Algebra, Lemma 0H1D, canonical maps
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: both composites send `[a]` to `[g (f a)] = [f' (aMap a)]`; the quotient
projections are surjective, so agreement on these representatives proves equality. -/
theorem powerQuotientMap_naturality
    {A : Type u} {C : Type v} {A' : Type w} {C' : Type t}
    [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (f : A →+* C) (f' : A' →+* C') (aMap : A →+* A') (g : C →+* C')
    (I : Ideal A) (J : Ideal C) (I' : Ideal A') (J' : Ideal C')
    (hf : I ≤ J.comap f) (hf' : I' ≤ J'.comap f')
    (ha : I ≤ I'.comap aMap) (hg : J ≤ J'.comap g)
    (hcomm : g.comp f = f'.comp aMap) (n : ℕ) :
    (powerQuotientMap g J J' hg n).comp (powerQuotientMap f I J hf n) =
      (powerQuotientMap f' I' J' hf' n).comp (powerQuotientMap aMap I I' ha n) := by
  sorry

/-- Associated graded maps are natural in compatible squares of ideal-preserving maps.
Source: Stacks Project, Algebra, Lemma 0H1D, canonical homogeneous maps
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: on the degree `n` class represented by `a ∈ I^n`, both routes give the
degree `n` class of `g (f a) = f' (aMap a)` modulo `(J')^(n+1)`. Quotient
induction and the universal property of the direct sum give equality. -/
theorem associatedGradedMap_naturality
    {A : Type u} {C : Type v} {A' : Type w} {C' : Type t}
    [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (f : A →+* C) (f' : A' →+* C') (aMap : A →+* A') (g : C →+* C')
    (I : Ideal A) (J : Ideal C) (I' : Ideal A') (J' : Ideal C')
    (hf : I ≤ J.comap f) (hf' : I' ≤ J'.comap f')
    (ha : I ≤ I'.comap aMap) (hg : J ≤ J'.comap g)
    (hcomm : g.comp f = f'.comp aMap) :
    (associatedGradedMap g J J' hg).comp (associatedGradedMap f I J hf) =
      (associatedGradedMap f' I' J' hf').comp (associatedGradedMap aMap I I' ha) := by
  sorry

/-- Quotient maps commute with composition.
Source: Stacks Project, Algebra, Lemma 0H1D, maps on representatives
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: both maps send `[a]` to `[g (f a)]`. -/
theorem powerQuotientMap_comp
    {A : Type u} {C : Type v} {D : Type w} [CommRing A] [CommRing C] [CommRing D]
    (f : A →+* C) (g : C →+* D) (I : Ideal A) (J : Ideal C) (K : Ideal D)
    (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) (n : ℕ) :
    powerQuotientMap (g.comp f) I K (hf.trans (Ideal.comap_mono hg)) n =
      (powerQuotientMap g J K hg n).comp (powerQuotientMap f I J hf n) := by
  sorry

/-- Associated graded maps commute with composition.
Source: Stacks Project, Algebra, Lemma 0H1D, maps on homogeneous representatives
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: both maps send each homogeneous class `[a]` to `[g (f a)]` in the same
degree. Quotient induction and direct sum extensionality finish. -/
theorem associatedGradedMap_comp
    {A : Type u} {C : Type v} {D : Type w} [CommRing A] [CommRing C] [CommRing D]
    (f : A →+* C) (g : C →+* D) (I : Ideal A) (J : Ideal C) (K : Ideal D)
    (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    associatedGradedMap (g.comp f) I K (hf.trans (Ideal.comap_mono hg)) =
      (associatedGradedMap g J K hg).comp (associatedGradedMap f I J hf) := by
  sorry

/-- The identity induces the identity on ideal-power quotients.
Source: Stacks Project, Algebra, Lemma 0H1D, maps on representatives
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: the identity fixes every representative `[a]`. -/
theorem powerQuotientMap_id {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    powerQuotientMap (RingHom.id A) I I le_rfl n = RingHom.id (A ⧸ I ^ n) := by
  sorry

/-- The identity induces the identity on the associated graded ring.
Source: Stacks Project, Algebra, Lemma 0H1D, homogeneous representatives
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: the identity fixes every homogeneous representative, hence every finite sum. -/
theorem associatedGradedMap_id {A : Type u} [CommRing A] (I : Ideal A) :
    associatedGradedMap (RingHom.id A) I I le_rfl = AddMonoidHom.id (associatedGraded I) := by
  sorry

end Ideal

namespace AlgebraicGeometry

/-- The hypothesis of the infinitesimal-neighbourhood theorem holds for étale
morphisms of affine spectra.
Source: Stacks Project, Algebra, Lemma 00UR
(blueprint: lem-sfb-augmented-etale-associated-graded).
Proof: etale_ring_map_iff_etale_affine identifies the scheme hypothesis with
an étale ring map. Such a map is formally étale. Equivalently, the node's
Step 1 uses flat_unramified_formally_etale for existence of square-zero lifts,
affine-formally-smooth-iff-ring-lifting to translate it to rings, and
formally-unramified-ring-iff-kahler-zero for uniqueness. -/
theorem formallyEtale_of_etale_spec {A C : Type u} [CommRing A] [CommRing C]
    (f : A →+* C) (hf : Etale (Spec.map (CommRingCat.ofHom f))) :
    @Algebra.FormallyEtale A C _ _ f.toAlgebra := by
  sorry

end AlgebraicGeometry
