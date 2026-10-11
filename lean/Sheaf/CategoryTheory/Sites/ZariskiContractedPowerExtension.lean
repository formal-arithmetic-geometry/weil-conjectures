module

public import Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtensionPresentation

/-!
# Extension theorem

Source: the worker's contracted-power construction developing blueprint `lem-sc-torsor-h1`;
Stacks Project, Lemma 02FQ constructs the corresponding extension by pushout.
(blueprint: lem-sc-zariski-contracted-power-extension)
-/

@[expose] public section

universe uT

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Torsor

/-- Contracted powers of a Zariski torsor form an extension by the constant integer sheaf.
Source: the worker's contracted-power construction in this node, developing blueprint
`lem-sc-torsor-h1`; Stacks Lemma 02FQ constructs the corresponding extension by pushout.
Proof: (1) Form the sheaf coproduct of all integer powers. On representatives in degrees
`m,n`, define addition by `powers.product m n`; its coherence gives units, associativity,
commutativity, and inverse pairing in degrees `n,-n` (lem-sc-zariski-contracted-power-torsor,
lem-sc-torsor-h1). (2) Project the degree-`n` summand to the constant section `n`.
The torsors are locally nonempty, so this map is locally surjective. Its kernel is the
zero-degree summand `G`, yielding short exactness (def-sc-gm-torsor,
def-sc-topological-abelian-cohomology). (3) The fibre over `1` is the degree-one summand,
identified with `T` by `powers.one`; the degree-zero unit constraint makes this
identification equivariant (lem-sc-zariski-contracted-power-torsor).
(blueprint: lem-sc-zariski-contracted-power-extension) -/
theorem nonempty_contractedPowerExtension (X : AlgebraicGeometry.Scheme.{uT})
    (G : Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{uT + 1}) (T : Torsor G) :
    Nonempty (ContractedPowerExtension X T) := by
  sorry

end CategoryTheory.Sheaf.Torsor

