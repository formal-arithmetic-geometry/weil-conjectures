module

public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Flat.EquationalCriterion
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded-above finite-presentation flat quasi-coherent complex on an affine
scheme has pseudo-coherent global sections.
Source: Stacks Project, Tag 064U, implication (3) to (1), and the affine
quasi-coherent equivalence used in Tag 08EB.
(blueprint: lem-pc-affine-finite-presentation-flat-pseudo-coherent).

Proof: Identify S with Spec A for A = Γ(S, ⊤). The affine quasi-coherent
equivalence identifies each section module of D with a finitely presented flat
A-module, hence a finite projective module. Evaluation preserves zero objects,
so the section complex P is zero above b. For its top term choose a finite
projective complement C^b such that P^b ⊕ C^b is finite free. Descending in n,
choose a finite projective complement C^(n-1) so that
P^(n-1) ⊕ C^n ⊕ C^(n-1) is finite free. This yields a bounded-above complex F:
its differential agrees with that of P on the P summands, is the identity on
C^n between degrees n-1 and n, and zero on the remaining complement. Thus F
is the direct sum of P and contractible identity pairs. Projection F → P is a
homotopy equivalence, hence a quasi-isomorphism and gives Q(F) ≅ Q(P). All
terms of F are finite free, and F is zero above b. These data witness the
ring definition of pseudo-coherence. The complements may continue indefinitely
below; no lower bound on F is asserted or required. The zero ring and the zero
complex also satisfy this construction. -/
theorem affine_finitePresentation_flat_pseudoCoherent (S : Scheme.{u})
    (hS : IsAffine S) (D : CochainComplex S.Modules ℤ) (b : ℕ)
    (hDle : D.IsStrictlyLE b)
    (hDflat : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S))
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hDfp : ∀ n : ℤ, (D.X n).IsFinitePresentation) :
      (letI : CommRing (S.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(S, ⊤));
        letI := HasDerivedCategory.standard (ModuleCat.{u} (S.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
