module
public import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 2000] CategoryTheory.sheafIsAbelian
namespace CategoryTheory.Sheaf.Torsor
/-- Generators biject with the fibre over one.
Source: Stacks 03AJ. Proof: use the short exact sequence and canonical lifting torsor;
local simple transitivity gives injectivity and surjectivity.
(blueprint: lem-sc-extension-presentation-generator-fibre) -/
theorem extension_presentation_generator_bijOn (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T) (U : S.Etaleᵒᵖ) :
    Set.BijOn (E.generator U) Set.univ
      {x | E.projection.hom.app U x = (toSheafify S.smallEtaleTopology
        ((Functor.const S.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{max u w + 1} ℤ)))).app U ⟨1⟩} := by
  sorry
end CategoryTheory.Sheaf.Torsor
