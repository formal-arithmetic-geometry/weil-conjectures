module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For a sheaf of rings on a Grothendieck site and an object `U`, localized
restriction admits a left adjoint preserving finite limits and finite colimits.

Proof: for a localized module sheaf `N`, define a presheaf `P(N)` with sections
at `V` the direct sum of `N(V, f)` over arrows `f : V ⟶ U`. The ring `R(V)` acts
on each summand. A restriction along `a : W ⟶ V` sends the `f` summand by the
restriction of `N` into the `a ≫ f` summand. The identities and composition laws
follow on direct-sum generators from those of `N`. A morphism of localized
sheaves acts on each summand; these maps define an additive functor `P`.
Let `G(N)` be module sheafification of `P(N)`.

A morphism `N ⟶ M.over U` gives a presheaf morphism `P(N) ⟶ M.val` by summing
its components. Conversely, compose such a presheaf morphism with each summand
inclusion to recover the components of a morphism `N ⟶ M.over U`. Naturality
along arrows in `C/U` follows from the restriction formula. The constructions
are inverse on generators and natural in both sheaves. The universal property
of module sheafification therefore gives `G ⊣ restriction`.

A monomorphism of module sheaves is injective on sections: its kernel is the
sectionwise kernel. Direct sums of injections are injective, so `P` sends a
monomorphism to a sectionwise injection. Exact module sheafification sends
this to a monomorphism. Sheafification is additive, so `G` is additive. As a
left adjoint it preserves colimits, hence is right exact. An additive right
exact functor between abelian categories that preserves monomorphisms is exact:
apply it to the two short exact sequences factoring an exact sequence through
its image. Thus `G` preserves kernels and finite biproducts, hence finite
limits; the adjunction already gives preservation of finite colimits.
This argument also covers empty indexing sets, whose direct sums are zero.
No assumption of commutativity of the rings or of pullbacks in `C` is needed.

Source: Stacks Project, Tags 03DI and 03DJ (Modules on Sites, Lemmas 18.19.2
and 18.19.3); Tag 08FI uses this exact left adjoint.
(blueprint: new-localized-restriction-extension-exists)
-/
theorem localized_restriction_extension_exists
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms) :
    ∃ (G : SheafOfModules.{max u v} (R.over U) ⥤ SheafOfModules.{max u v} R),
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      Nonempty (G ⊣ SheafOfModules.overFunctor.{max u v} R U) := by
  sorry

end CategoryTheory
