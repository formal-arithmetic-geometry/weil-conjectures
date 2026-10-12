module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction

/-!
# Exactness of extension by zero on the small Zariski site

Source: Stacks Project, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

`U_Zar` is the localized site `(Opens.grothendieckTopology X).over U` (the opens `W ⊆ U`,
with the coverings of `X_Zar`), and extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)` is
`sheafToPresheaf ⋙ (Over.forget U).op.lan ⋙ presheafToSheaf`
(`Functor.sheafPullbackConstruction.sheafPullback`): the left Kan extension of `F` along
the inclusion is the presheaf `j_{p!} F` (`F(V)` for `V ⊆ U`, the empty colimit `0`
otherwise), followed by sheafification on `X_Zar`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)`, the sheafification of `j_{p!}`, is
additive.

Source: Stacks Project, Modules on Sites, Lemma 03DJ, additivity clause
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

Proof: `j_!` is a left adjoint of restriction (Mathlib's
`sheafPullbackConstruction.sheafAdjunctionContinuous`); a left adjoint between
preadditive categories preserves finite biproducts, hence is additive. -/
@[instance]
theorem zariski_extensionByZero_additive (X : Scheme.{u}) (U : X.Opens) :
    (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U) AddCommGrpCat.{u}
        ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)).Additive := by
  sorry

/-- Extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)` (additive by
`zariski_extensionByZero_additive`) carries every short exact sequence to a short exact
sequence, and in particular carries monomorphisms to monomorphisms.

Source: Stacks Project, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

Proof: `j_!` is a left adjoint of restriction, hence right exact, so it preserves
cokernels. A monomorphism of `Ab(U_Zar)` is sectionwise injective, so `j_{p!}` of it is
sectionwise injective, and sheafification preserves finite limits, so `j_!` of it is a
monomorphism. A short exact sequence is a mono followed by its cokernel; both are
preserved, which gives short exactness of the image. -/
theorem zariski_extensionByZero_exact (X : Scheme.{u}) (U : X.Opens) :
    (∀ S : ShortComplex (Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}),
      S.ShortExact →
        (S.map (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
          AddCommGrpCat.{u} ((Opens.grothendieckTopology X).over U)
          (Opens.grothendieckTopology X))).ShortExact) ∧
    (∀ {A B : Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}} (f : A ⟶ B),
      Mono f →
        Mono ((Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
          AddCommGrpCat.{u} ((Opens.grothendieckTopology X).over U)
          (Opens.grothendieckTopology X)).map f)) := by
  sorry

end AlgebraicGeometry
