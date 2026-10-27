/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.SpaceGradedCohomologyFinite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic
import WeilConjectures.Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Global algebras and components of proper algebraic spaces

Source: Stacks Project, Spaces over Fields, Tag 0DMY, clauses (1)--(3), and
More on Morphisms of Spaces, Tag 0E1E
(blueprint: lem-sfb-space-proper-global-algebra-components).

The global algebra is represented by its limit cone on the small etale chart rings,
normalized by the structure map from k. The factors have the same limit-cone
specification. The product equivalence is required to be restriction on every chart.
Connected components are Mathlib's quotient; its fibres are exactly the maximal
nonempty connected subsets. No nonemptiness assumption is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The global algebra of a proper space is the finite product of the local Artinian
section algebras of its clopen connected components. If the space is reduced, the
factors are finite field extensions. Over an algebraically closed field, the inverse
product of the scalar maps is the canonical componentwise-constant isomorphism.
The limit cone `hA` specifies A = Gamma(X_et,O_X); `hscalar` specifies its k-algebra
structure. Both are presentations of the named global algebra, not finiteness assumptions.

Source: Stacks Project, Spaces over Fields, Tag 0DMY(1)--(3), proof of (2), and
More on Morphisms of Spaces, Tag 0E1E
(blueprint: lem-sfb-space-proper-global-algebra-components).

Proof:
1. Specialize lem-sfb-space-graded-cohomology-finite to the degree-zero algebra k
   and structure module O_X, quasi-coherent by def-trf-space-quasi-coherent-module.
   Degree zero cohomology is sections (def-weil-pbc-sites-and-cohomology), giving
   finite dimension. Apply lem-weil-pbc-finite-dim-algebra-artinian. The empty space
   has zero section ring and empty component set, so this case is included.
2. Apply lem-sfb-artinian-ring-finite-local-product to A. Pull the coordinate
   idempotents back to A. By lem-sfb-space-global-idempotent-clopen they give a
   finite disjoint clopen cover: nonzero idempotents give nonempty opens, their
   pairwise products are zero, and their sum is one.
3. Restriction and sheaf gluing on the disjoint chartwise open cover are inverse
   k-algebra maps. Extension by zero identifies each factor with the corresponding
   idempotent summand, hence it is nonzero local Artinian and finite-dimensional.
4. A disconnected piece would supply a nontrivial idempotent in its local factor,
   contradicting lem-weil-pbc-local-ring-idempotent-zero-one. A connected subset
   cannot meet two members of the clopen partition. Thus these pieces are exactly
   the connected components; reindex the restriction equivalence by them.
5. For reduced X a nilpotent section vanishes on every affine etale chart, hence
   vanishes. Each factor is reduced. The reduced Artinian residue decomposition
   lem-sfb-reduced-artinian-residue-product, with its singleton maximal spectrum,
   makes each local factor a field, finite over k by step 3.
6. If k is algebraically closed, lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one
   and the local idempotent lemma make every factor's scalar map bijective. Their
   product followed by inverse restriction is the componentwise-constant map.
7. Transport the coordinate basis of k^C along this equivalence to obtain
   finrank k A = Nat.card C. For the empty set it is the empty basis of zero. -/
theorem proper_global_algebra_components
    (k : Type u) [Field k] (X : AlgebraicSpace (Spec (.of k)))
    (p : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of k))))) (hp : MapIsProper p)
    (A : CommAlgCat.{u} k)
    (π : (Functor.const X.EtaleSiteᵒᵖ).obj (CommRingCat.of A) ⟶
      X.etaleForget.op ⋙ Scheme.Γ)
    (hA : IsLimit (Cone.mk (CommRingCat.of A) π))
    (hscalar : ∀ (a : k) (T : X.EtaleSite),
      (π.app (op T)).hom (algebraMap k A a) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          Scheme.Γ.map T.obj.left.hom.op).hom a) :
    Finite (ConnectedComponents (Point X.obj.obj)) ∧
    (∀ c : ConnectedComponents (Point X.obj.obj),
      IsClopen (ConnectedComponents.mk ⁻¹' {c})) ∧
    Module.Finite k A ∧
    (IsEmpty (Point X.obj.obj) → Subsingleton A) ∧
    ∃ (U : ConnectedComponents (Point X.obj.obj) → OpenSubspace X)
      (Z : ConnectedComponents (Point X.obj.obj) → AlgebraicSpace (Spec (.of k)))
      (i : ∀ c, Z c ⟶ X) (hi : ∀ c, IsEtale (i c).hom.hom)
      (B : ConnectedComponents (Point X.obj.obj) → CommAlgCat.{u} k)
      (ρ : ∀ c, (Functor.const (Z c).EtaleSiteᵒᵖ).obj (CommRingCat.of (B c)) ⟶
        (Z c).etaleForget.op ⋙ Scheme.Γ),
      (∀ c, Nonempty (IsLimit (Cone.mk (CommRingCat.of (B c)) (ρ c)))) ∧
      (∀ c, ∃ j : (Z c).obj.obj ≅ (U c).val.toFunctor,
        j.hom ≫ (U c).val.ι = (i c).hom.hom ∧
        pointImage (U c).val.ι = ConnectedComponents.mk ⁻¹' {c}) ∧
      (∀ c, Nontrivial (B c) ∧ IsLocalRing (B c) ∧ IsArtinianRing (B c) ∧
        Module.Finite k (B c)) ∧
      ∃ e : A ≃ₐ[k] (∀ c, B c),
        (∀ (a : A) (c : ConnectedComponents (Point X.obj.obj)) (T : (Z c).EtaleSite),
          ((ρ c).app (op T)).hom (e a c) =
            (π.app (op ((etaleMap (i c) (hi c)).obj T))).hom a) ∧
        ((∀ T : X.EtaleSite, AlgebraicGeometry.IsReduced (X.etaleForget.obj T)) →
          (∀ c, IsField (B c)) ∧
          (IsAlgClosed k →
            (∃ constants : (ConnectedComponents (Point X.obj.obj) → k) ≃ₐ[k] A,
              ∀ (a : ConnectedComponents (Point X.obj.obj) → k)
                (c : ConnectedComponents (Point X.obj.obj)),
                e (constants a) c = algebraMap k (B c) (a c)) ∧
            Module.finrank k A = Nat.card (ConnectedComponents (Point X.obj.obj)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
