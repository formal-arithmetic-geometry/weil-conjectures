module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Spaces
import Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtension

/-!
# Extensions and torsors on the Zariski site

Source: literature/stacks-project/cohomology.tex, Lemma 02FQ (cohomology-lemma-torsors-h1)
(blueprint: lem-sc-zariski-ext-torsor)

## Main statements

* `zariskiExtTorsor`: isomorphism classes of torsors are canonically in bijection
  with equivalence classes of extensions of the constant integer sheaf.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Sheaf

/--
For a scheme `X` and an abelian sheaf `G` on its small Zariski site, the isomorphism
classes of `G`-torsors are canonically in bijection with equivalence classes of short
exact sequences `0 → G → E → ℤ_X → 0`.  The map from an extension to a torsor is the
fibre over `1`, and the inverse maps a torsor to the coproduct of its contracted powers.
(blueprint: lem-sc-zariski-ext-torsor)
-/
theorem zariskiExtTorsor {X : Scheme.{u}}
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]
    (G : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{w}) :
    Nonempty (_root_.Quotient (CategoryTheory.Sheaf.Torsor.setoid (G := G)) ≃
      Abelian.Ext ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) G 1) := by
  sorry

end CategoryTheory.Sheaf
