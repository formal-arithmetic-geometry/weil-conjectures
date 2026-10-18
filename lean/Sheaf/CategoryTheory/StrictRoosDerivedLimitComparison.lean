/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# The strict Roos comparison and its evaluation maps

Source: Stacks Project, Derived Categories, Tags 07KC and 08TC, and Cohomology on Sites,
Tags 0940 and 0941; the explicit comparison and evaluation square in the DAG proof
(blueprint: lem-sf-strict-roos-derived-limit-comparison).

The helper definitions spell out the products, transition endomorphism and signed cone
already introduced by this statement. The comparison maps are uniquely specified by
coordinates, rather than chosen as arbitrary isomorphisms of derived-limit triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

/-- The termwise product of the evaluated strict tower complexes. Index `n` means the
paper's positive index `n+1`. Source: Stacks 07KC and 08TC
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosProduct (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : CochainComplex A ℤ :=
  ∏ᶜ (fun n : ℕ ↦ X.asFunctor.obj (op n))

/-- The existing transition endomorphism, applied in the category of complexes.
Source: Stacks 08TC (blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosEndomorphism (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    strictRoosProduct X ⟶ strictRoosProduct X :=
  towerTransitionEndomorphism
    (fun n ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)

/-- The actual shifted mapping cone of `1-s`. In the coordinate order `(y,x)`, its
 differential is `(-dy-(1-s)x,dx)`. Source: Stacks 07KC and 08TC
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosComplex (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : CochainComplex A ℤ :=
  (CochainComplex.mappingCone (strictRoosEndomorphism X))⟦(-1 : ℤ)⟧

/-- The degree `p+1` coordinates `(y,x)`, interchanging Mathlib's source-first cone
summands. All transports are the canonical shift and cone isomorphisms.
Source: Stacks 08TC and the displayed differential of the node
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosCoordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (strictRoosComplex X).X (p + 1) ≅
      (strictRoosProduct X).X p ⊞ (strictRoosProduct X).X (p + 1) :=
  (CochainComplex.mappingCone (strictRoosEndomorphism X)).shiftFunctorObjXIso
      (-1) (p + 1) p (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (strictRoosEndomorphism X)
      p (p + 1) rfl ≪≫
    biprod.braiding _ _

/-- The product map induced by a strict map of tower complexes, on both cone coordinates.
Source: Stacks 07KC and the strict naturality square of the DAG proof
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosProductMap {X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ I) :
    strictRoosProduct X ⟶ strictRoosProduct I :=
  Limits.Pi.map (fun n ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))

/-- Both arrows of the prescribed strict Roos zigzag are quasi-isomorphisms, for an
arbitrary K-injective tower resolution, and its resulting isomorphism respects every
evaluation. `ε` is the image of the inclusion `η`; `θ` is precisely `Roos(u)` followed
by its inverse. `υ` is the image of the evaluated resolution, so its inverse gives
exactly the specified evaluation on the total derived limit, represented by `lim I`.

The sectionwise commutativity binder is the commutative-ring-sheaf hypothesis. The
module universe contains both site universes, without equating them. The sheafification
instances and the derived-category instance only supply the standard category structures.

Source: Stacks 07KC, 08TC, 0940 and 0941; explicit arbitrary-K-injective extension and
evaluation square in the node's proof
(blueprint: lem-sf-strict-roos-derived-limit-comparison).

Proof plan:
1. Exact countable products preserve quasi-isomorphisms (Stacks 07KC). Naturality of
   towerTransitionEndomorphism makes the two product maps commute with `1-s`; the
   induced cone map is `ρ` with the displayed coordinates. Thus `ρ` is a quasi-isomorphism,
   as also follows from the functor clause of lem-weil-strict-roos-comparison.
   Evaluation is exact by lem-weil-tower-category-levelwise-abelian.
2. The tower category is Grothendieck by lem-weil-pbc-small-module-diagrams-grothendieck.
   Apply lem-pur-kinjective-degreewise-existence to resolve I by a K-injective J with
   injective terms. The map I to J is a homotopy equivalence by
   lem-weil-pbc-kinjective-hom-derived. The injective-term normalization of
   lem-weil-strict-roos-comparison makes the inclusion lim J to Roos(J) a quasi-isomorphism.
3. Termwise limit preserves the homotopies of this equivalence. The coordinate identity
   Roos(v) η_I = η_J lim(v) and two-out-of-three on cohomology make the prescribed η_I
   a quasi-isomorphism, without requiring I to have injective terms.
4. lem-weil-pbc-ringed-strict-tower-homotopy-limit identifies lim I with total derived
   inverse limit. Set θ = Roos(u) η_I inverse. The chain projections a_n satisfy
   a_n^I η_I = pr_n and a_n^I Roos(u) = u_n a_n^X. Inverting the evaluated resolution
   gives e_n θ = a_n^X, for the actual zigzag. -/
theorem strictRoosDerivedLimitComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
    (u : X ⟶ I) [QuasiIso u] [I.IsKInjective] :
    ∃ (ρ : strictRoosComplex X ⟶ strictRoosComplex I)
      (η : limit I.asFunctor ⟶ strictRoosComplex I)
      (a : ∀ n : ℕ, strictRoosComplex X ⟶ X.asFunctor.obj (op n)),
      (∀ p : ℤ, ρ.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        (strictRoosCoordinates X p).hom ≫
          biprod.map ((strictRoosProductMap u).f p) ((strictRoosProductMap u).f (p + 1))) ∧
      (∀ p : ℤ, η.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1))) ∧
      (∀ (n : ℕ) (p : ℤ), (a n).f (p + 1) =
        (strictRoosCoordinates X p).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
      QuasiIso ρ ∧ QuasiIso η ∧
      ∃ (ε : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
          DerivedCategory.Q.{w}.obj (strictRoosComplex I))
        (θ : DerivedCategory.Q.{w}.obj (strictRoosComplex X) ≅
          DerivedCategory.Q.{w}.obj (limit I.asFunctor)),
        ε.hom = DerivedCategory.Q.{w}.map η ∧
        θ.hom = DerivedCategory.Q.{w}.map ρ ≫ ε.inv ∧
        ∀ n : ℕ, ∃ υ : DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n)) ≅
            DerivedCategory.Q.{w}.obj (I.asFunctor.obj (op n)),
          υ.hom = DerivedCategory.Q.{w}.map
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map u).app (op n)) ∧
          θ.hom ≫ DerivedCategory.Q.{w}.map (limit.π I.asFunctor (op n)) ≫ υ.inv =
            DerivedCategory.Q.{w}.map (a n) := by
  sorry

end CategoryTheory
