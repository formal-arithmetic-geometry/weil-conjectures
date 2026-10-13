module

public import Mathlib.Topology.Sheaves.Abelian

/-! Monomorphism preservation for extension by zero along an open embedding. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace

/-- The sheaf pullback along the open-subspace functor preserves monomorphisms.
Source: Stacks Project, Tags 03DI and 03DJ.

Proof: let U be the open image of f. For an open V of Y, the pointwise left Kan
extension along hf.functor.op is the colimit over opens W of X with V contained in f(W).
If V is not contained in U, this category is empty, so the colimit is the zero group.
If V is contained in U, the object W = f⁻¹(V) is terminal in this indexing category:
every other W contains f⁻¹(V), and arrows in the opposite category are reversed inclusions.
Thus the colimit is F(f⁻¹(V)), naturally in the abelian presheaf F. Consequently the
left Kan extension of a sectionwise monomorphism is a sectionwise monomorphism, including
the empty-index case where its component is the identity of the zero group.
The inclusion of sheaves into presheaves preserves monomorphisms, and abelian
sheafification preserves finite limits, hence monomorphisms. Their composite with this
left Kan extension therefore preserves monomorphisms. Finally transport along
Functor.sheafPullbackConstruction.sheafPullbackIso, which identifies this composite
with the chosen left adjoint in the statement.
(blueprint: new-open-embedding-sheaf-pullback-preserves-monomorphisms) -/
theorem Topology.isOpenEmbedding_sheafPullback_preservesMonomorphisms
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    (let G := hf.functor
     haveI := hf.functor_isContinuous
     G.sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology X)
       (Opens.grothendieckTopology Y)).PreservesMonomorphisms := by
  sorry

