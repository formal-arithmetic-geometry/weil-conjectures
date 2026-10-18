/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ProEtaleLisseOrigin
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Topology.Stratification
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Triangulated.Generators
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.SixFunctors.FlatModelGeneration

/-!
# Flat models and generators

Source: Weil conjectures blueprint, main-20261015, `sec-six-functors-basics/`
`sk-lem-sf-flat-model`, statement and complement (blueprint: sk-lem-sf-flat-model).

## Main statements

* `proEtaleFlatModel`: bounded flat constructible representatives.
* `proEtaleFlatStratification`: finite projective constant local models on strata.
* `proEtaleThickGeneration`, `etaleThickGeneration`: the Noetherian complement.
* `proEtaleThickGeneration_eq`: equality with the thick envelope in the standing setting.

The generator predicates below spell out the statement's locally closed extension by zero.
They use the scheme-theoretic image of the actual stratum immersion, not an arbitrary closed
subscheme with the same underlying set. Closed direct image is exact here, so its value on
`L[0]` also represents `Rg_*j_!L`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The pro-etale closure generators of the statement: `g_*j_!L` in degree zero, where
`j` is the open factor of an actual stratum immersion through its scheme-theoretic image,
and `L` is lisse with flat stalks. The canonical intrinsic realization transports the
fixed-module extension and direct image, including their scalar actions. Lisse and flat
are equivalently locally finite projective over the finite ring.
Source: blueprint `sk-lem-sf-flat-model`, paragraph 1 and complement
(blueprint: sk-lem-sf-flat-model). -/
def sfProEtaleClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : proEtaleRingModules (str.domain i) (proEtaleConstantRing (str.domain i) A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsLisseProEtaleFixedModuleSheaf (str.domain i) (ULift.{u + 1, u} A)
      ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L) ∧
    SheafOfModules.IsFlatOnSite (J := ProEt.topology (str.domain i))
      (R := proEtaleConstantRing (str.domain i) A) L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L)))))

/-- The etale closure generators `Rg_*j_!L`: the closed direct image is exact, so the
ordinary sheaf in degree zero is its derived value. The equation on `j` fixes the open
factor through the scheme-theoretic image of the stratum immersion. Lisse flat sheaves
have finite projective constant local models over the finite coefficient ring.
Source: blueprint `sk-lem-sf-flat-model`, complement
(blueprint: sk-lem-sf-flat-model). -/
def sfEtaleClosureGenerators (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (str.immersion i).imageι).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)))

/-- Every finite-Tor bounded constructible pro-etale object in the standing setting has
an actual bounded complex of flat constructible sheaves as representative.
Source: blueprint `sk-lem-sf-flat-model`, first paragraph
(blueprint: sk-lem-sf-flat-model).

Proof plan (the node's steps 1--3): finite type over the standing field makes `X`
Noetherian (lem-weil-pbc-finite-type-over-noetherian), hence qcqs by
lem-weil-pbc-locally-noetherian-quasi-separated. The finite ring is Noetherian.
Use det-pe-finite-tor-comparison-noetherian to descend `K` with its Tor interval to the
etale site. Apply lem-sf-etale-flat-constructible. Apply the exact comparison pullback
termwise (lem-sf-comparison-pullback-exact). It preserves zero terms and the representing
quasi-isomorphism; flatness follows from lem-exc-constant-inverse-image-flat and
constructibility from lem-weil-pbc-finite-ring-constructible-sheaf-origin. The canonical
intrinsic coefficient realization identifies the resulting ordinary module sheaves. -/
theorem proEtaleFlatModel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : proEtaleDerivedCategory X A)
    (hbc : (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K))
    (hTor : HasFiniteProEtaleTorAmplitude X A K) :
    ∃ (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
      (a b : ℤ), a ≤ b ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
      (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := proEtaleConstantRing X A) (P.X q)) ∧
      (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A (P.X q)) ∧
      Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  sorry

/-- A flat constructible sheaf admits finite projective constant module local models
on a finite stratification. Finiteness and projectivity of the local modules are explicit.
Source: blueprint `sk-lem-sf-flat-model`, first paragraph, stratification clause
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1 and 4): finite type over the standing field is Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Every subset is quasi-compact, using
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal as in step 1. Apply clause 1 of
det-sf-flat-model-generation to the flat constructible sheaf. This supplies an ordered
finite stratification on which the restrictions are locally constant with finite projective
stalks. Refine each trivializing pro-etale covering; its constant module is isomorphic to
a stalk, hence finite projective. Empty members may use the zero projective module.
These module-sheaf isomorphisms give the displayed finite projective local models. -/
theorem proEtaleFlatStratification
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : IsConstructibleProEtaleModuleSheaf X A F)
    (hflat : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F) :
    ∃ str : LocallyClosedStratification X, ∀ i : Fin str.n,
      ∃ (I : Type (u + 1)) (U : I → (str.domain i).ProEt)
        (f : ∀ t : I, U t ⟶ ProEt.mk (𝟙 (str.domain i))),
        Presieve.ofArrows U f ∈ (ProEt.precoverage (str.domain i)).coverings _ ∧
        ∀ t : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          Finite M ∧ Module.Projective (ULift.{u + 1, u} A) M ∧
          Nonempty ((proEtaleConstantModulePullback (str.immersion i) A F).over (U t) ≅
            proEtaleConstantModuleSheafOver (str.domain i) A (U t) M) := by
  sorry

/-- The Noetherian complement on the pro-etale site, in its property formulation.
Source: blueprint `sk-lem-sf-flat-model`, complement
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1--7): finite rings are Noetherian; `X` is qcqs and all its strata
are quasi-compact by step 1. Descend through det-pe-finite-tor-comparison-noetherian,
resolve by lem-sf-etale-flat-constructible and pull back using
lem-sf-comparison-pullback-exact, lem-exc-constant-inverse-image-flat and
lem-weil-pbc-finite-ring-constructible-sheaf-origin. The result is a bounded flat
constructible model. Clauses 1--2 of det-sf-flat-model-generation give a finite ordered
stratification and an open--closed filtration of each term by locally closed extensions
of lisse flat sheaves. Factor the quasi-compact stratum immersions through their
scheme-theoretic images using lemma-nagata-immersion-open-in-scheme-image. By
lem-weil-pbc-proetale-ringed-open-closed closed direct image is exact; the complement is
quasi-compact by Noetherianity. By lem-weil-pbc-exact-functor-derived-functor it agrees
with its right derived functor on degree-zero objects. Hence the factors are exactly
the displayed closure generators. Convert sheaf short exact sequences to triangles by
lem-weil-pbc-complex-ses-triangle and induct over the finite filtration. For the model,
the degreewise split sequences of stupid tails give triangles with third term
`P^q[-q]`; start at the zero tail above the last degree and induct downwards. Shift,
extension and isomorphism stability give `P K`. Retract stability gives the thick
formulation; the empty scheme and zero complex use only its zero-object base case. -/
theorem proEtaleThickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (P : ObjectProperty (proEtaleDerivedCategory X A))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : sfProEtaleClosureGenerators X A ≤ P)
    (K : proEtaleDerivedCategory X A)
    (hbc : (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K))
    (hTor : HasFiniteProEtaleTorAmplitude X A K) : P K := by
  sorry

/-- The Noetherian complement on the etale site, with the recorded finite-value
constructibility and the recorded Tor tests on every module sheaf in degree zero.
Source: blueprint `sk-lem-sf-flat-model`, complement
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1 and 3--7): use lem-sf-etale-flat-constructible directly, without
a comparison descent. Apply the finite ordered sheaf stratification and filtration of
det-sf-flat-model-generation to each flat constructible term. Factor each stratum by
lemma-nagata-immersion-open-in-scheme-image. Exact closed pushforward follows from
lem-cbc-open-closed-recollement, and lem-weil-pbc-exact-functor-derived-functor identifies
it with the right derived functor on these sheaves. Thus each filtration factor is one
of sfEtaleClosureGenerators. Use lem-weil-pbc-complex-ses-triangle for the sheaf
filtrations and the degreewise split short exact sequences of stupid tails. Finite
induction, starting from zero above the final degree, gives the property for the model
from its shifted terms, then for K by its representing isomorphism. Retracts are
allowed by the property assumption, as stated in the complement. -/
theorem etaleThickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (P : ObjectProperty (Etale.DerivedCategoryModule A X))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : sfEtaleClosureGenerators X A ≤ P)
    (K : Etale.DerivedCategoryModule A X)
    (hbc : Etale.DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K) :
    P K := by
  sorry

/-- In the standing setting the pro-etale finite-Tor constructible category equals
its thick generator envelope, including reverse containment of the generators.
Source: blueprint `sk-lem-sf-flat-model`, first paragraph, generation clause
(blueprint: sk-lem-sf-flat-model).

Proof plan (node steps 1--7): the model, finite sheaf filtration and stupid-tail
triangles in steps 1--6 prove containment in the thick envelope, equivalently step 7
with the envelope as the property. Clause 3 of det-sf-flat-model-generation supplies
reverse containment and stability under direct summands: each lisse flat stratum sheaf
extended by zero is constructible of finite Tor amplitude, and this object class is
closed under shifts, extensions, isomorphisms and retracts. The scheme-theoretic closure
factorization and exact closed pushforward identify these extensions with our canonical
closure generators. These two containments give equality of object properties. -/
theorem proEtaleThickGeneration_eq
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (fun K : proEtaleDerivedCategory X A ↦
      ((∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
        ((_root_.DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor
            (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)) ∧
      HasFiniteProEtaleTorAmplitude X A K) =
      (sfProEtaleClosureGenerators X A).triangEnvelope := by
  sorry

end AlgebraicGeometry
