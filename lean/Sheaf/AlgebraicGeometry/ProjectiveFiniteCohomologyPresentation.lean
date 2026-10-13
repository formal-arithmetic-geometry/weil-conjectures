/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A projective presentation with finite cohomology source

Source: Stacks Project, Tag 01YS, proof of Lemma 30.14.1 (1) and (3),
Tag 01Y6, Lemma 30.9.9, and Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-u3-projective-finite-cohomology-presentation)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The closed pushforward of a coherent module has an epimorphism from a module with
finite cohomology over the affine base, with coherent kernel.

Source: Stacks Project, Tag 01YS, proof of Lemma 30.14.1 (1) and (3),
Tag 01Y6, Lemma 30.9.9, and Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-u3-projective-finite-cohomology-presentation)

Proof: put A = Gamma(T,O). The canonical affine isomorphism T -> Spec A
induces an isomorphism of projective spaces compatible with their projections.
The projective space is locally Noetherian, as its projection is locally of
finite type over the Noetherian affine base. Closed pushforward j_*F is
quasi-coherent and finitely presented: on an affine chart a finite module over
a quotient ring is finite over the Noetherian chart ring and hence finitely
presented. Put G = j_*F and transport G to projective space over A.
Choose finitely many generators on each standard affine chart. Clearing denominators
extends each generator, after
multiplication by a power of its coordinate section, to a homomorphism from a
negative twist. The sum E of these finitely many twists maps epimorphically to G,
since its images generate on each chart. The kernel is quasi-coherent, and is
finitely presented because the standard charts are Noetherian. For each twist,
the standard-cover monomial calculation identifies degree-q cohomology with a
finite free A-module (or zero); when there is one coordinate, each twist is
free of rank one on Spec A and has no positive cohomology. Finite sums commute with
cohomology, so H^q(E)
is finite. Transport the epimorphism and its kernel back along the projective
isomorphism; the induced cohomology comparison is A-linear by naturality for
multiplication by base sections. Thus the restricted action is exactly the one
along the displayed projection. For an empty coordinate type the projective
space is empty: G, E, and the kernel are zero, and all cohomology is zero.
This argument does not use finiteness of any cohomology of G or of the kernel. -/
theorem exists_projective_finite_cohomology_presentation
    {Y T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    ∃ (E : (ℙ(N; T)).Modules) (φ : E ⟶ (pushforward j).obj F) (_ : Epi φ),
      (kernel φ).IsQuasicoherent ∧ (kernel φ).IsFinitePresentation ∧
      (letI : Module Γ(T, ⊤) (E.H q) :=
        Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
       Module.Finite Γ(T, ⊤) (E.H q)) := by sorry

end AlgebraicGeometry.Scheme.Modules
