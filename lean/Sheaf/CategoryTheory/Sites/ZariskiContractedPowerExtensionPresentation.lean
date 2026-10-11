module

public import Sheaf.CategoryTheory.Sites.ZariskiContractedPowerTorsor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Extension from contracted powers of a Zariski torsor

Source: the worker's contracted-power construction developing blueprint `lem-sc-torsor-h1`;
the extension corresponds to Stacks Lemma 02FQ, constructed there by pushout.
(blueprint: def-sc-zariski-contracted-power-extension-presentation)
-/

@[expose] public section

universe uE

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace CategoryTheory.Sheaf.Torsor

/-- An abelian-sheaf presentation of the sheaf coproduct of all integer contracted powers.
The natural summand maps identify each power with the fibre of the exponent map over its
constant integer. Since the target is the constant integer sheaf, sections are locally in
these fibres, which specify the sheaf coproduct. Addition on summands is induced by the
coherent contracted-product maps `powers.product m n`, and degree zero is the inclusion of
`G`. Degree one, transported along `powers.one`, identifies the fibre over `1` with `T`;
its equivariance follows from `summand_add`, `summand_zero`, and the unit constraints.
Source: the worker's contracted-power construction in node
`lem-sc-zariski-contracted-power-extension`, developing blueprint `lem-sc-torsor-h1`.
Stacks Project, Lemma 02FQ constructs the corresponding extension by a pushout instead.
(blueprint: def-sc-zariski-contracted-power-extension-presentation) -/
structure ContractedPowerExtension (X : AlgebraicGeometry.Scheme.{uE})
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE + 1}} (T : Torsor G) where
  powers : CoherentContractedPowers X T
  middle : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE + 1}
  inclusion : G ⟶ middle
  projection : middle ⟶
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE + 1}).obj
      (AddCommGrpCat.of (ULift.{uE + 1} ℤ))
  inclusion_projection : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection inclusion_projection).ShortExact
  summand (n : ℤ) (U : (Opens X)ᵒᵖ) :
    (powers.power n).sheaf.obj.obj U → middle.obj.obj U
  summand_natural (n : ℤ) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
      (t : (powers.power n).sheaf.obj.obj U) :
    middle.obj.map f (summand n U t) =
      summand n V ((powers.power n).sheaf.obj.map f t)
  summand_projection (n : ℤ) (U : (Opens X)ᵒᵖ)
      (t : (powers.power n).sheaf.obj.obj U) :
    projection.hom.app U (summand n U t) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{uE + 1} ℤ)))).app U ⟨n⟩
  summand_bijective (n : ℤ) (U : (Opens X)ᵒᵖ) :
    Set.BijOn (summand n U) Set.univ
      {x | projection.hom.app U x =
        (toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{uE + 1} ℤ)))).app U ⟨n⟩}
  summand_add (m n : ℤ) (U : (Opens X)ᵒᵖ)
      (x : (powers.power m).sheaf.obj.obj U) (y : (powers.power n).sheaf.obj.obj U) :
    summand m U x + summand n U y =
      summand (m + n) U ((powers.product m n).quotient U x y)
  summand_zero (U : (Opens X)ᵒᵖ) (g : G.obj.obj U) :
    summand 0 U
      (cast (congrArg (fun P : Torsor G => P.sheaf.obj.obj U) powers.zero.symm) g) =
      inclusion.hom.app U g


end CategoryTheory.Sheaf.Torsor
