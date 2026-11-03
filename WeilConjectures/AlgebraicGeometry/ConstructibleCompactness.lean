/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedTriangulated
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Compactness with rational coefficients

Source: blueprint latest, sec-six-functors-basics/sk-thm-constructible-compactness,
statement and proof; Stacks Project, Tag 09QH (blueprint: sk-thm-constructible-compactness).

The ambient category is the ordinary unbounded derived category of internal modules over
`condensedRingObj Λ X`. Constructibility throughout means finite constant scalar models,
as in `IsConstantModelConstructible`, rather than arbitrary local finite presentations.
The assertion bundle records compactness inside the localizing closure of this Dbc and
the stronger ambient comparison for all families with ind-constructible cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits DirectSum
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Classical in
/-- The canonical additive map sends the `i`-th summand `f : C ⟶ K i` to
`f ≫ c.inj i`. When `c` is a coproduct, this is exactly the displayed comparison.
Source: blueprint latest, sk-thm-constructible-compactness, displayed formula
(blueprint: sk-thm-constructible-compactness). -/
def constructibleCompactnessComparison
    {A : Type v} [Category.{w} A] [Preadditive A]
    (C : A) {I : Type u} (K : I → A) (c : Cofan K) :
    (⨁ i : I, (C ⟶ K i)) →+ (C ⟶ c.pt) :=
  DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (c.inj i))

/-- Both compactness assertions of the node, with Cons, Dbc, IndCons and Dic expanded
using the recorded finite constant local-model convention. The existential `hc` supplies
the coproduct structure on the full localizing subcategory; it is part of the conclusion,
not an assumption. The second clause uses an arbitrary ambient coproduct cocone, so it
specifies the natural comparison independently of choices of sums. Ambient sums exist by
`localizingClosure_exists`. No common cohomological bound on the family is imposed.
Source: blueprint latest, sk-thm-constructible-compactness, both assertions
(blueprint: sk-thm-constructible-compactness). -/
def HasConstructibleCompactness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∃ hc : HasCoproducts.{u + 1}
      (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
    ∀ C : (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
      constantModelBoundedConstructible Λ X C.obj →
        @CategoryTheory.IsCompactObject _ _ _ hc C) ∧
  (∀ C : DerivedCategory (pulledBackModuleObjects Λ X),
    constantModelBoundedConstructible Λ X C →
    ∀ (I : Type (u + 1)) (K : I → DerivedCategory (pulledBackModuleObjects Λ X)),
      (∀ (i : I) (n : ℤ),
        ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
          ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∀ c : Cofan K, IsColimit c →
        Function.Bijective (constructibleCompactnessComparison C K c))

end AlgebraicGeometry.ProEtale
