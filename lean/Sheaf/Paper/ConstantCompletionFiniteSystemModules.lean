module
public import Sheaf.Paper.ConstantCompletionBasic
public import Sheaf.Paper.SectionwiseAdicAlgebraLimit
/-! Module structures for the finite constant completion tower.
Source: Stacks Project, Tag 093M (blueprint: new-e2-constant-completion-finite-system-modules).
The quotient coefficient sections carry their canonical module structures over the
corresponding quotient rings. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
def finiteSystemUnder (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)) :=
  Under.lift (finiteSystem J A I) (quotientCone J A I).π

/--
Source: Stacks Project, Tag 093M (blueprint: new-e2-constant-completion-finite-system-modules).
Proof: evaluate the finite constant coefficient sheaf at `U`; its canonical
`A ⧸ I^(n+1)`-algebra structure induces the required module structure, uniformly
in `n` and `U`.
-/
theorem finiteSystem_module_instances (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    Nonempty (∀ (n : ℕ) (U : Cᵒᵖ),
      Module (A ⧸ I ^ (n + 1)) (adicTerm J A (finiteSystemUnder J A I) n U)) := by
  refine ⟨fun n U ↦ ?_⟩
  exact (((toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of (A ⧸ I ^ (n + 1))))).app U).hom).toModule
end CategoryTheory.ConstantCompletion
