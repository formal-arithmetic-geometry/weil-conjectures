/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Pi
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Products of geometric-point skyscraper module sheaves

Source: Stacks Project, Tags 00Y7, 00Y8, 04EQ, 05V8, 01DU, 013K, 05TH and 05TI
(blueprint: lem-per-etale-point-product-acyclic).

We use ordinary small-etale sheaves valued in `ModuleCat`, the encoding specified by
`def-weil-pbc-derived-categories`. These are modules over the constant ring sheaf.
The constructions below use only existing stalk, skyscraper and product functors.

## Main definitions and statements

* `etalePointStalkFamily`: the family of geometric module stalks.
* `etalePointProduct`: the product of the point skyscraper functors.
* `etalePointProductCoordinate`: its canonical section coordinates.
* `etaleModuleEvaluation`: evaluation on an etale object.
* `etalePointProduct_acyclic`: the product formula, germ adjunction, exactness,
  preservation of injectives, degreewise resolutions and evaluation acyclicity.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The family of geometric module stalks, each the pointed-neighbourhood colimit
of `pointedEtaleStalk`. Source: Stacks, Tag 04EQ
(blueprint: lem-per-etale-point-product-acyclic). -/
noncomputable def etalePointStalkFamily (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    {P : Type (u + 1)} {Ω : P → Type u} [∀ p, Field (Ω p)] [∀ p, IsAlgClosed (Ω p)]
    (s : ∀ p, Spec (.of (Ω p)) ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ (P → ModuleCat.{u + 1} R) :=
  Functor.pi' (fun p ↦ (pointSmallEtale (s p)).sheafFiber)

/-- The product of geometric-point skyscraper sheaves. The factor at `p` has
sections the product of `M p` over lifts of `s p`; restrictions precompose the lift
and maps act coordinatewise, by `Point.skyscraperSheafFunctor` and `Pi.functor`.
Source: Stacks, Tag 00Y8 (blueprint: lem-per-etale-point-product-acyclic). -/
noncomputable def etalePointProduct (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    {P : Type (u + 1)} {Ω : P → Type u} [∀ p, Field (Ω p)] [∀ p, IsAlgClosed (Ω p)]
    (s : ∀ p, Spec (.of (Ω p)) ⟶ X) :
    (P → ModuleCat.{u + 1} R) ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  Functor.pi (fun p ↦ (pointSmallEtale (s p)).skyscraperSheafFunctor) ⋙ Pi.functor P

/-- The `(p,v)`-coordinate of sections of the point product, formed from the two
canonical product projections. Source: Stacks, Tag 00Y8
(blueprint: lem-per-etale-point-product-acyclic). -/
noncomputable def etalePointProductCoordinate (X : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] {P : Type (u + 1)} {Ω : P → Type u} [∀ p, Field (Ω p)]
    [∀ p, IsAlgClosed (Ω p)] (s : ∀ p, Spec (.of (Ω p)) ⟶ X)
    (M : P → ModuleCat.{u + 1} R) (V : X.Etale) (p : P)
    (v : (pointSmallEtale (s p)).fiber.obj V) :
    ((etalePointProduct X R s).obj M).obj.obj (op V) ⟶ M p :=
  (Pi.π (fun q ↦ (pointSmallEtale (s q)).skyscraperSheaf (M q)) p).hom.app (op V) ≫
    Pi.π (fun _ : (pointSmallEtale (s p)).fiber.obj V ↦ M p) v

/-- Evaluation on an etale object, in ordinary module sheaves. Source: Stacks,
Tag 05TI (blueprint: lem-per-etale-point-product-acyclic). -/
abbrev etaleModuleEvaluation (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    (V : X.Etale) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      ModuleCat.{u + 1} R :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ (ModuleCat.{u + 1} R)).obj (op V)

/-- Geometric-point products are exact, preserve injectivity and give sheaves acyclic
for evaluation on every etale object. The product formula is expressed by the canonical
coordinate fan being limiting. The adjunction unit is specified at every lift by the
germ map. The resolution clause identifies each term, differential and augmentation of
the sheaf resolution with the degreewise point product of the module resolutions.
Positive integer degrees are passed to `rightDerived` through `Int.toNat`.
Source: Stacks, Tags 00Y7, 00Y8, 04EQ, 05V8, 01DU, 013K, 05TH and 05TI
(blueprint: lem-per-etale-point-product-acyclic).

Proof:
1. For each point, functions on lifts form a sheaf by
   lem-fix-geometric-stalk-topos-point (Stacks 00Y8). Products of sheaves are
   sectionwise, so their coordinate fan is limiting. Addition and scalar action
   are coordinatewise. As an R_X-module, a section scalar acts through its germ
   at (p,v); lem-weil-pbc-constant-sheaf-geometric-stalk identifies that scalar
   stalk with R. Restrictions commute with these operations
   (def-weil-sheaf-of-modules-category).
2. A family t_p : F_p → M_p gives h_V(x)_(p,v) = t_p([V,v,x]). Conversely h
   gives t_p([V,v,x]) = h_V(x)_(p,v). These are well-defined by common pointed
   refinements (lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered), linear,
   inverse, and natural, by def-weil-pbc-geometric-stalks. This gives the family
   adjunction (00Y7). Identity t_p gives the displayed germ-unit formula.
3. By lem-weil-pbc-module-sheaves-colimits-forgetful and
   prop-weil-pbc-geometric-stalks-exact, each module stalk is exact; module kernels
   and images are the usual ones (lem-weil-pbc-ring-modules-enough-injectives).
   Family limits and colimits are componentwise, hence A_P is exact.
4. At every V, products of module sequences are exact: kernels are coordinatewise
   and surjections lift by choice at every (p,v). The size convention permits
   that choice. Sectionwise exactness implies sheaf exactness because kernels
   are sectionwise and cokernels are sheafified sectionwise cokernels
   (def-weil-sheaf-of-modules-category). Thus B_P and its evaluations are exact.
5. Given a mono F → G and F → B_P(M), transpose to F_p → M_p. Exact stalks
   make F_p → G_p mono. Injectivity of every M_p extends these maps; choice
   gives a family, whose transpose extends the original map. This is precisely
   def-sp-injective-resolutions, so B_P(M) is injective.
6. By lem-weil-pbc-ring-modules-enough-injectives and
   lem-weil-pbc-left-exact-injective-resolution-degree-zero choose nonnegative
   injective resolutions simultaneously. Applying B_P degreewise preserves the
   augmented exact complex by step 4 and gives injective terms by step 5.
   This constructs the stated sheaf resolution, with its indicated augmentation.
7. Evaluation is additive and module sheaves have enough injectives
   (lem-weil-pbc-module-sheaves-enough-injectives). The injective computation of
   lem-weil-pbc-right-derived-plus-injective identifies derived evaluation with
   the evaluated resolution from step 6. A positive-degree cocycle is a tuple of
   module cocycles; each has a preimage in the preceding degree, and small choice
   gives a preimage tuple. Thus positive cohomology vanishes. The argument also
   covers empty families and empty lift sets and uses no conservativity,
   Noetherianity or finiteness assumption. -/
theorem etalePointProduct_acyclic (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    {P : Type (u + 1)} {Ω : P → Type u} [∀ p, Field (Ω p)] [∀ p, IsAlgClosed (Ω p)]
    (s : ∀ p, Spec (.of (Ω p)) ⟶ X) :
    (∀ (M : P → ModuleCat.{u + 1} R) (V : X.Etale),
      Nonempty (IsLimit (Fan.mk (((etalePointProduct X R s).obj M).obj.obj (op V))
        (fun i : Σ p, (pointSmallEtale (s p)).fiber.obj V ↦
          etalePointProductCoordinate X R s M V i.1 i.2)))) ∧
    (∃ adj : etalePointStalkFamily X R s ⊣ etalePointProduct X R s,
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (V : X.Etale)
        (p : P) (v : (pointSmallEtale (s p)).fiber.obj V),
        (adj.unit.app F).hom.app (op V) ≫
          etalePointProductCoordinate X R s ((etalePointStalkFamily X R s).obj F) V p v =
            pointedEtaleGerm F (s p) V v) ∧
    PreservesFiniteLimits (etalePointStalkFamily X R s) ∧
    PreservesFiniteColimits (etalePointStalkFamily X R s) ∧
    (∀ V : X.Etale,
      PreservesFiniteLimits (etalePointProduct X R s ⋙ etaleModuleEvaluation X R V) ∧
      PreservesFiniteColimits (etalePointProduct X R s ⋙ etaleModuleEvaluation X R V)) ∧
    PreservesFiniteLimits (etalePointProduct X R s) ∧
    PreservesFiniteColimits (etalePointProduct X R s) ∧
    (∀ M : P → ModuleCat.{u + 1} R,
      (∀ p, Injective (M p)) → Injective ((etalePointProduct X R s).obj M)) ∧
    (∀ M : P → ModuleCat.{u + 1} R,
      Nonempty (∀ p, InjectiveResolution (M p)) ∧
      ∀ J : ∀ p, InjectiveResolution (M p),
        ∃ I : InjectiveResolution ((etalePointProduct X R s).obj M),
          ∃ e : ∀ n : ℕ, I.cocomplex.X n ≅
              (etalePointProduct X R s).obj (fun p ↦ (J p).cocomplex.X n),
            (∀ n m : ℕ, I.cocomplex.d n m ≫ (e m).hom =
              (e n).hom ≫ (etalePointProduct X R s).map (fun p ↦ (J p).cocomplex.d n m)) ∧
            I.ι.f 0 ≫ (e 0).hom =
              (etalePointProduct X R s).map (fun p ↦ (J p).ι.f 0)) ∧
    (∀ (M : P → ModuleCat.{u + 1} R) (V : X.Etale) (a : ℤ), 0 < a →
      IsZero (((etaleModuleEvaluation X R V).rightDerived a.toNat).obj
        ((etalePointProduct X R s).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme
