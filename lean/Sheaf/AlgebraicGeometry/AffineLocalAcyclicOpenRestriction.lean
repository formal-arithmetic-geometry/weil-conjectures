module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Affine-local acyclicity under open restriction

Source: Stacks Project, Tag 0A51, the Mayer--Vietoris induction, and Tag 03D3.
(blueprint: lem-weil-pbc-affine-local-acyclic-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Affine-local acyclicity is inherited by restriction to an open subscheme.
Source: Stacks Project, Tag 0A51, induction step; inverse-image composition and
base-change associativity, Stacks Project, Tag 03D3.
(blueprint: lem-weil-pbc-affine-local-acyclic-open-restriction)

Proof: Let O be an affine open of W. Its image W.ι(O) is an affine open of X,
because O and its image are isomorphic as schemes. Apply hlocal to that image.
The iterated fibre product O ×_W (W ×_X Z) is canonically isomorphic to
W.ι(O) ×_X Z, by the open-image isomorphism and associativity of fibre products.
Under this isomorphism the sheaves in the two groups agree: both are the inverse
image of J along the same composite to X. The composition isomorphisms of module
inverse image and their compatibility with forgetting coefficients give an
isomorphism of abelian sheaves. Cohomology preserves sheaf isomorphisms, and
pullback along a scheme isomorphism induces an isomorphism on cohomology.
Transport the subsingleton instance supplied by hlocal across these isomorphisms.
The argument also applies to empty opens, to W = top, and to any morphism i. -/
theorem Etale.affine_local_acyclic_open_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hlocal : ∀ (W : X.Opens), IsAffineOpen W → ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst W.ι i)^*[ModuleCat.{u + 1} Λ].obj
            ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J))) q))
    (W : X.Opens) :
    ∀ (O : W.toScheme.Opens), IsAffineOpen O → ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst O.ι (pullback.fst W.ι i))^*[ModuleCat.{u + 1} Λ].obj
            ((O.ι)^*[ModuleCat.{u + 1} Λ].obj
              ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J)))) q) := by sorry

end AlgebraicGeometry
