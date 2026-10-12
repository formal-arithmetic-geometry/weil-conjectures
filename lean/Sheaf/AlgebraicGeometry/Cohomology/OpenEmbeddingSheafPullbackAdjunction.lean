module
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! Auxiliary extension-by-zero adjunction for open embeddings. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

/-- For an open embedding, extension by zero is mono-preserving and left adjoint to sheaf pullback.
Source: Stacks Project, Tags 03DI and 03DJ.

The extension by zero is constructed by sheafifying the left Kan extension along the open
embedding. Sectionwise, the construction is a direct sum over maps into the image; direct sums
preserve monomorphisms, and sheafification in abelian groups preserves them. The resulting
functor is left adjoint to pullback by the open embedding.
(blueprint: new-open-embedding-sheaf-pullback-adjunction) -/
theorem Topology.isOpenEmbedding_sheafPullback_adjunction
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    ∃ L : X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u},
      Nonempty L.PreservesMonomorphisms ∧
        Nonempty (L ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  sorry
