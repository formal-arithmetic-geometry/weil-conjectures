module
public import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
import Mathlib.CategoryTheory.Sites.Abelian
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 2000] CategoryTheory.sheafIsAbelian CategoryTheory.Abelian.hasPushouts
namespace CategoryTheory.Sheaf.Torsor
/-- The extension presentation sequence is short exact.
Source: Stacks 03AJ. Proof: construct the augmentation as a cokernel and verify
exactness using the universal property and local torsor sections.
(blueprint: lem-sc-extension-presentation-short-exact) -/
theorem extension_presentation_shortExact (S : AlgebraicGeometry.Scheme.{u})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}} {T : Torsor G}
    (E : ExtensionPresentation.{u, w} S T) :
    (ShortComplex.mk E.inclusion E.projection E.inclusion_projection).ShortExact := by
  sorry
end CategoryTheory.Sheaf.Torsor
