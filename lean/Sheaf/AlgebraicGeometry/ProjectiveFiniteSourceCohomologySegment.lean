/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Exact.Basic
import Sheaf.Paper.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-! # A finite-source cohomology segment for a projective embedding

Source: Stacks Project, Tags 01YS (Lemma 30.14.1 (3)) and 01Y6 (Lemma 30.9.9).
(blueprint: lem-pc-p2-projective-finite-source-cohomology-segment)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The descending-induction segment, without assuming finiteness of its last term.

Source: Stacks Project, Tags 01YS (Lemma 30.14.1 (3)) and 01Y6 (Lemma 30.9.9).
(blueprint: lem-pc-p2-projective-finite-source-cohomology-segment)

Proof: identify the affine base T with Spec Gamma(T,O), and transport the specified
closed embedding to projective space over that ring. Push F forward along the embedding;
closed pushforward is quasi-coherent and finitely presented on the Noetherian projective
space and preserves cohomology. Choose an epimorphism E -> j_* F from a finite sum of
negative twists by clearing denominators of finitely many generators on the standard
charts. Its kernel K is quasi-coherent and finitely presented. The long exact sequence
contains H^q(E) -> H^q(j_* F) -> H^(q+1)(K). Set V = H^q(E), which is finite: cohomology
commutes with finite sums, and the standard-cover monomial calculation gives finite free
cohomology for each twist over the base ring. Transport the middle term to H^q(F).
All maps, including the closed-pushforward comparison and the affine-base identification,
commute with multiplication by base sections, so this is an exact segment of modules
with precisely the displayed restriction-of-scalars actions. No finiteness of H^(q+1)(K)
is asserted. If the coordinate type is empty, projective space and Y are empty; take
K and V zero, and the segment is exact. -/
theorem exists_projective_finite_source_cohomology_segment
    {Y T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    letI : Module Γ(T, ⊤) (F.H q) :=
      Module.compHom _ (j ≫ (ℙ(N; T) ↘ T)).appTop.hom
    ∃ (K : (ℙ(N; T)).Modules) (_ : K.IsQuasicoherent) (_ : K.IsFinitePresentation),
      letI : Module Γ(T, ⊤) (K.H (q + 1)) :=
        Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
      ∃ (V : ModuleCat.{u} Γ(T, ⊤)) (_ : Module.Finite Γ(T, ⊤) V)
        (a : V →ₗ[Γ(T, ⊤)] F.H q) (b : F.H q →ₗ[Γ(T, ⊤)] K.H (q + 1)),
        Function.Exact a b := by sorry

end AlgebraicGeometry.Scheme.Modules
