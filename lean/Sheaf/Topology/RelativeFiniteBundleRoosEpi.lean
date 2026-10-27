module

public import Sheaf.Topology.RelativeFiniteBundleModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-! # Local solutions of the finite-bundle Roos equations

Source: Ruimy--Tubach--Wolf, Lemma 1.2.7, relative compactness argument,
and Stacks Tags 08ZU, 005C, 005D, 03CN
(blueprint: lem-sfb-relative-finite-bundle-roos-epi).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

/-- The Roos differential for finite continuous abelian bundles is an epimorphism.
Source: steps 5--7 of lem-sfb-relative-finite-bundle-roos, expanding
Ruimy--Tubach--Wolf, Lemma 1.2.7; Stacks Tags 08ZU, 005C, 005D, 03CN
(blueprint: lem-sfb-relative-finite-bundle-roos-epi).

Proof: pull the bundles to a test object Q over P. Their total spaces are finite
unions of products of clopen subsets of Q with finite discrete groups, so are
profinite. Naturality of the section presentations identifies each transition
with a continuous additive map over P by Yoneda, since the bundle total spaces
represent their section presheaves. For a section y of the product over Q, take
the closed subspace of Q times the product of these total spaces defined by the
equal-base conditions and x_n-t_n(x_(n+1))=y_n(q). It is profinite, since all the
conditions are closed and the ambient product is compact Hausdorff with a clopen
basis. Over each q, any finite set of equations lies in a finite initial block.
Set the next coordinate to zero, solve backwards by x_n=y_n(q)+t_n(x_(n+1)), and
set the remaining coordinates to zero. The closed finite intersection property
in the product of the finite fibres then gives a solution of all equations.
Thus the solution space surjects onto Q. Its coordinate sections give a preimage
of y after this single covering. Local surjectivity makes the underlying
abelian sheaf map epic, and faithful exact forgetting of the scalar action
reflects epimorphisms. For empty Q the projection is vacuously surjective; zero
fibres and arbitrary, possibly nonsurjective, transitions cause no change. -/
theorem relativeFiniteBundle_roos_epi
    (P : Profinite.{u}) (T : Type v) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T]
    (M : ℕᵒᵖ ⥤ SheafOfModules.{max u v + 1} (relativeContinuousRing P T))
    (E : ℕ → FiniteAbelianBundle P)
    (hE : ∀ n : ℕ, Nonempty ((E n).SectionPresentation (M.obj (op n)))) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)) := by sorry

end Profinite
