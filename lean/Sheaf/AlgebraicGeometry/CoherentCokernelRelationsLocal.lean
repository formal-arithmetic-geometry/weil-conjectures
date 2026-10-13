module

public import Sheaf.AlgebraicGeometry.Coherent

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Finite-free replacement for cokernel relations on a neighbourhood of each point.
Source: Stacks Project, Modules, Lemma 01BY, cokernel paragraph.
(blueprint: lem-weil-pbc-coherent-cokernel-relations-local)

Proof: Fix x in U. The cokernel projection G → cokernel f is an epimorphism
of module sheaves, so each of the n sections defining g lifts near x. Intersect
these finitely many neighbourhoods. The image of f is an epimorphic image of
F and is therefore of finite type; shrink again to choose finitely many sections
generating that image. Write V for the resulting neighbourhood inside U.
Combine the image generators and the chosen lifts into a map ψ from a finite
free module of rank m to G.over V. Projection onto the summands corresponding
to the n lifts sends kernel ψ to the restricted relation kernel of g. This map
is epi: a relation of the lifted sections has image in the image of f, so locally
it is a linear combination of the chosen image generators, and subtracting that
combination gives a section of kernel ψ lifting the relation. Equivalently, apply
the snake lemma to the split finite-free sequence and the image-G-cokernel
sequence. Restriction preserves kernels, since kernels are computed sectionwise,
so the target is the overMap restriction of kernel g. No quasi-compactness or
nonemptiness assumption is needed; n = 0 and an empty U cause no difficulty.

Historical explanation: the old fixed-U conclusion was false. On P¹_k take
U = X, F = I_p ≅ O(-1), G = O, f the ideal inclusion of a rational point, and
n = 1 with g the quotient onto k(p). Every ψ : O^m → O is a row of constants,
whose kernel is O^m or O^(m-1). Every morphism from this kernel to O(-1) is zero
because H⁰(P¹_k, O(-1)) = 0, and hence cannot be epi onto the nonzero kernel g.
The neighbourhood quantifiers below restore the shrinking in the cited proof. -/
theorem coherent_cokernel_relations_local (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G)
    (hF : F.IsFiniteType) (hG : IsCoherent X G)
    (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      (cokernel f).over U) :
    ∀ x : X, x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ (m : ℕ)
          (ψ : SheafOfModules.free (R := (moduleRings X).over V)
            (ULift.{u} (Fin m)) ⟶ G.over V),
          ∃ e : kernel ψ ⟶
            (SheafOfModules.overMap (moduleRings X) (homOfLE hVU)).obj (kernel g),
            Epi e := by
  sorry

end AlgebraicGeometry.RingedSpace
