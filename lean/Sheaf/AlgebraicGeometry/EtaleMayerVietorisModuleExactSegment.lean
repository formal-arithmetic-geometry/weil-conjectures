module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import Mathlib.Algebra.Exact.Basic

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- An exact Mayer--Vietoris segment for the underlying abelian groups of
module-sheaf pullbacks. There are no vanishing hypotheses.
Source: Stacks Project, Tag 0A50; module inverse image, Tags 03D3 and 03D7.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-module-exact-segment)

Proof: Let F be the underlying abelian sheaf of i^*J on Z. Pull U and V back
as opens of Z. Their union is Z since inverse image preserves unions and top;
their intersection is the inverse image of U ∩ V. The base changes of the
three open immersions are open immersions isomorphic to these inverse-image
opens. For each T = U, V, U ∩ V, the equality of the two composites in the
pullback square and the inverse-image composition isomorphisms identify
pr_1^*(T.ι^*J) with pr_2^*(i^*J). Forgetting modules commutes with inverse
image, so this identifies the underlying abelian sheaf with F restricted to
the corresponding inverse-image open, transported across its scheme
isomorphism. The induced additive cohomology isomorphisms identify all four
displayed groups with the groups of the two-open Mayer--Vietoris sequence of
F on Z. Tag 0A50 constructs this sequence by applying sections to an injective
resolution: in every degree the sheaf condition gives exactness on the left
and in the middle, and injectivity gives surjectivity onto intersection
sections. The resulting short exact sequence of complexes gives an exact
cohomology segment in degrees r and r + 1. Equivalently use etale_mayerVietoris
and nonempty_sheafH_extDerivedIso to express this segment in Sheaf.H. Transport
its connecting and restriction homomorphisms through the four additive
isomorphisms. Isomorphisms preserve images and kernels, hence the transported
maps δ and ρ are exact. This construction also works for r = 0 and for empty
or repeated cover members. -/
theorem Etale.exists_module_mayer_vietoris_exact_segment
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) (r : ℕ) :
    ∃ δ : (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst (U ⊓ V).ι i)^*[ModuleCat.{u + 1} Λ].obj
          (((U ⊓ V).ι)^*[ModuleCat.{u + 1} Λ].obj J))) r) →+ (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) (r + 1)),
      ∃ ρ : (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) (r + 1)) →+ ((Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst U.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((U.ι)^*[ModuleCat.{u + 1} Λ].obj J))) (r + 1)) × (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst V.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((V.ι)^*[ModuleCat.{u + 1} Λ].obj J))) (r + 1))),
        Function.Exact δ ρ := by
  sorry

end AlgebraicGeometry
