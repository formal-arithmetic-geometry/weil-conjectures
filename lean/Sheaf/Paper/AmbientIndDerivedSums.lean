/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.Paper.AmbientIndDerivedTriangulated
import Sheaf.Paper.IndConstructibleFilteredColimits
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SheafTensor
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale

/-!
# Sums and truncations for ind-constructible cohomology

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived,
`sk-cor-ambient-ind-derived-sums.md` and its proof (blueprint: det-ambient-ind-derived-sums).

The canonical comparison is written using arbitrary colimit cocones. Its source is a
coproduct of the cohomology objects and its target is the cohomology of the coproduct;
`IsColimit.desc` specifies the comparison by the original coprojections. This avoids
making any additional choice of coproducts or imposing a coproduct-existence hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- All three assertions for a finite subextension E.
Source: blueprint main-20261015, `sk-cor-ambient-ind-derived-sums.md`, clauses 1--3;
Stacks Project, Tags 03DB, 07D9 and 0118; the standing separated finite-type
positive-characteristic field setting of `sk-def-sfb-dc-setting`
(blueprint: det-ambient-ind-derived-sums).

Proof:
1. Identify internal modules with sectionwise modules via the sheaf tensor universal
   property (`sk-def-sfb-module-objects`, `sk-def-sfb-sheaf-tensor`). The ring-sheaf
   Grothendieck theorem (`lem-weil-pbc-ring-sheaves-grothendieck`) gives exact filtered
   colimits. Express an arbitrary sum as the filtered colimit of its finite subsums;
   finite sums are exact in an abelian category, so arbitrary sums are exact.
2. Represent each derived object by a complex. The termwise sum represents the derived
   sum (`det-def-localizing-closure-existence`). Exact sums preserve the two short exact
   sequences defining cycles, boundaries and cohomology, hence the canonical comparison
   from the sum of cohomologies is an isomorphism. The maps are induced by coprojections,
   so this is precisely the displayed `desc`, with no common boundedness assumption.
3. If all summands have ind-constructible cohomology, sum closure of IndCons
   (`det-ind-heart-filtered-colimits`) and step 2 give the same for their derived sum.
4. The canonical upper truncation retains cohomology in degrees at most n and has zero
   cohomology above n (`lem-weil-pbc-truncation-cohomology`). The lower truncation has
   zero terms below n; in degree n its cycles are ker(d^n)/im(d^(n-1)), with no incoming
   boundaries; in degree n+1 its boundaries are unchanged, and higher terms agree.
   Thus it retains cohomology in degrees at least n. These constructions preserve
   quasi-isomorphisms and descend to the standard derived truncations. The zero module
   is constructible by the zero scalar model on each affine open, hence ind-constructible
   via its one-object filtered diagram. Both truncations therefore satisfy the predicate.
5. A bounded constant-model constructible object has constructible cohomology in every
   degree (`sk-def-sfb-constructible`, `sk-def-sfb-bounded-constructible`). Each such module
   is its own filtered colimit over the one-object category; this proves Dbc is in Dic.
6. Dic is triangulated and replete (`det-ambient-ind-derived-triangulated`); step 3 gives
   sum closure and step 5 gives containment of Dbc. The intersection/minimality defining
   the localizing closure (`det-def-localizing-closure-existence`) gives Loc(Dbc) in Dic.
-/
theorem indConstructibleDerived_sums_and_truncations
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
      (c : Cofan K), IsColimit c → ∀ (n : ℤ)
      (d : Cocone (Discrete.functor K ⋙ DerivedCategory.homologyFunctor _ n))
      (hd : IsColimit d),
      IsIso (hd.desc ((DerivedCategory.homologyFunctor _ n).mapCocone c))) ∧
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
      (c : Cofan K), IsColimit c →
      (∀ s : S, ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj (K s))) →
      ∀ m : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ m).obj c.pt)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) (n : ℤ),
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) →
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K)))) ∧
    (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) ∧
    (localizingClosure (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X) ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) := by
  sorry

/-- All three assertions for the finite-subextension-valued condensed algebraic closure.
Source: blueprint main-20261015, `sk-cor-ambient-ind-derived-sums.md`, clauses 1--3;
Stacks Project, Tags 03DB, 07D9 and 0118; the standing separated finite-type
positive-characteristic field setting of `sk-def-sfb-dc-setting`
(blueprint: det-ambient-ind-derived-sums).

Proof:
1. Identify internal modules with sectionwise modules via the sheaf tensor universal
   property (`sk-def-sfb-module-objects`, `sk-def-sfb-sheaf-tensor`). The ring-sheaf
   Grothendieck theorem (`lem-weil-pbc-ring-sheaves-grothendieck`) gives exact filtered
   colimits. Express an arbitrary sum as the filtered colimit of its finite subsums;
   finite sums are exact in an abelian category, so arbitrary sums are exact.
2. Represent each derived object by a complex. The termwise sum represents the derived
   sum (`det-def-localizing-closure-existence`). Exact sums preserve the two short exact
   sequences defining cycles, boundaries and cohomology, hence the canonical comparison
   from the sum of cohomologies is an isomorphism. The maps are induced by coprojections,
   so this is precisely the displayed `desc`, with no common boundedness assumption.
3. If all summands have ind-constructible cohomology, sum closure of IndCons
   (`det-ind-heart-filtered-colimits`) and step 2 give the same for their derived sum.
4. The canonical upper truncation retains cohomology in degrees at most n and has zero
   cohomology above n (`lem-weil-pbc-truncation-cohomology`). The lower truncation has
   zero terms below n; in degree n its cycles are ker(d^n)/im(d^(n-1)), with no incoming
   boundaries; in degree n+1 its boundaries are unchanged, and higher terms agree.
   Thus it retains cohomology in degrees at least n. These constructions preserve
   quasi-isomorphisms and descend to the standard derived truncations. The zero module
   is constructible by the zero scalar model on each affine open, hence ind-constructible
   via its one-object filtered diagram. Both truncations therefore satisfy the predicate.
5. A bounded constant-model constructible object has constructible cohomology in every
   degree (`sk-def-sfb-constructible`, `sk-def-sfb-bounded-constructible`). Each such module
   is its own filtered colimit over the one-object category; this proves Dbc is in Dic.
6. Dic is triangulated and replete (`det-ambient-ind-derived-triangulated`); step 3 gives
   sum closure and step 5 gives containment of Dbc. The intersection/minimality defining
   the localizing closure (`det-def-localizing-closure-existence`) gives Loc(Dbc) in Dic.
-/
theorem indConstructibleDerived_sums_and_truncations_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)))
      (c : Cofan K), IsColimit c → ∀ (n : ℤ)
      (d : Cocone (Discrete.functor K ⋙ DerivedCategory.homologyFunctor _ n))
      (hd : IsColimit d),
      IsIso (hd.desc ((DerivedCategory.homologyFunctor _ n).mapCocone c))) ∧
    (∀ (S : Type (u + 1)) (K : S → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)))
      (c : Cofan K), IsColimit c →
      (∀ s : S, ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj (K s))) →
      ∀ m : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ m).obj c.pt)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))) (n : ℤ),
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) →
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      (∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K)))) ∧
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) ∧
    (localizingClosure (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ≤
      fun K ↦ ∀ m : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
