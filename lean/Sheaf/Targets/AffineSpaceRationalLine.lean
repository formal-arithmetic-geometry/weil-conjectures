/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

import WeilConjectures.Compactification.ProjectiveSpace
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CartesianCoefficientTwists
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Rational affine-line compact-support adjunction

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-cor-affine-space-rational/sk-cor-affine-space-rational-line.md`
(blueprint: det-cor-affine-space-rational-line).

## Main declarations

* `rationalLocalizingCategory`, `rationalLocalizingInclusion`: literal Loc(Dbc) and inclusion.
* `rationalTwistFunctor`: the existing derived tensor specialized to a Tate line.
* `affineLineChosenCompactification`: the published Nagata choice for the affine projection.
* `affineLineRationalAssertion`: the three clauses for one coefficient convention.
* `det_cor_affine_space_rational_line`: both rational coefficient cases.

The statement records the standard affine chart of the relative projective line, the
compactification lower-shriek functor, and the Tate-twisted shifted pullback.  The two
coefficient constructors below are the finite-subextension and finite-subextension-valued
algebraic-closure conventions of the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The localizing derived category used in the affine-line statement.
Source: blueprint `sk-def-localizing-closure` (blueprint: det-cor-affine-space-rational-line). -/
abbrev rationalLocalizingCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory

/-- The full inclusion of the localizing category into the ambient derived category.
Source: blueprint `sk-def-localizing-closure` (blueprint: det-cor-affine-space-rational-line). -/
noncomputable abbrev rationalLocalizingInclusion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).ι

/-- Derived tensor with a specified Tate line, placed in degree zero.
Source: blueprint `sk-def-sp-tate-twist` (blueprint: det-cor-affine-space-rational-line). -/
noncomputable def rationalTwistFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  (derivedTensor Λ X).flip.obj ((DerivedCategory.singleFunctor _ 0).obj L)

/-- The recorded Nagata choice for the affine projection as a morphism over k.
The instance arguments are the existing affine-space and composition instances, written
explicitly because typeclass search does not unfold the Over-object projections here.
Source: blueprint `sk-def-sfb-dc-setting`, chosen compactification convention
(blueprint: det-cor-affine-space-rational-line). -/
noncomputable def affineLineChosenCompactification
    (k : Type u) [Field k] (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))] :
    Compactification (𝔸(PUnit.{u + 1}; V) ↘ V) :=
  @compactificationOverField k _
    (Over.mk ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k))))
    (Over.mk (V ↘ Spec (.of k)))
    (inferInstanceAs (LocallyOfFiniteType
      ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact
      ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (IsSeparated
      ((𝔸(PUnit.{u + 1}; V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact (V ↘ Spec (.of k))))
    (inferInstanceAs (IsSeparated (V ↘ Spec (.of k))))
    (Over.homMk (𝔸(PUnit.{u + 1}; V) ↘ V) rfl)

/-- The complete assertion for one of the two rational coefficient conventions.
Source: blueprint `sk-cor-affine-space-rational-line`
(blueprint: det-cor-affine-space-rational-line).
The comparison isomorphisms to the ambient derived categories make every displayed functor
be the specified module-object functor, rather than an unrelated functor between subcategories.
-/
noncomputable def affineLineRationalAssertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (V : Scheme.{u})
    (c : Compactification (𝔸(PUnit.{u + 1}; V) ↘ V))
    (twist : ∀ X : Scheme.{u},
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) : Prop :=
  ∃ (J : rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)) ⥤
        rationalLocalizingCategory Λ (ProjectiveLine V))
    (R : rationalLocalizingCategory Λ (ProjectiveLine V) ⥤
        rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)))
    (_hJ : J ⋙ rationalLocalizingInclusion Λ (ProjectiveLine V) ≅
      rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ⋙
        D((ProjectiveLine.affineChart V)_!open⟦Λ⟧))
    (_hR : R ⋙ rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ≅
      rationalLocalizingInclusion Λ (ProjectiveLine V) ⋙
        D((ProjectiveLine.affineChart V)^*⟦Λ⟧))
    (_adjJ : J ⊣ R)
    (F : rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)) ⥤
        rationalLocalizingCategory Λ V)
    (Q : rationalLocalizingCategory Λ (ProjectiveLine V) ⥤
        rationalLocalizingCategory Λ V)
    (_hF : F ⋙ rationalLocalizingInclusion Λ V ≅
      rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ⋙
        rightDerivedLowerShriekOfCompactification Λ c)
    (_hQ : Q ⋙ rationalLocalizingInclusion Λ V ≅
      rationalLocalizingInclusion Λ (ProjectiveLine V) ⋙
        R((ProjectiveLine V ↘ V)_*⟦Λ⟧))
    (_hcomp : F ≅ J ⋙ Q)
    (P : rationalLocalizingCategory Λ V ⥤
        rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)))
    (_hP : P ⋙ rationalLocalizingInclusion Λ (𝔸(PUnit.{u + 1}; V)) ≅
      rationalLocalizingInclusion Λ V ⋙
        (CondensedRing.upperStar Λ (𝔸(PUnit.{u + 1}; V) ↘ V)).leftDerivedFunctor ⋙
          twist (𝔸(PUnit.{u + 1}; V)) ⋙ shiftFunctor _ (2 : ℤ))
    (adjP : CategoryTheory.Adjunction F P),
    ∀ (G : rationalLocalizingCategory Λ V ⥤
        rationalLocalizingCategory Λ (𝔸(PUnit.{u + 1}; V)))
      (adjG : CategoryTheory.Adjunction F G),
    ∃! (e : G ≅ P), (∀ N,
      F.map (e.hom.app N) ≫ adjP.counit.app N = adjG.counit.app N)

/-- Rational affine-line compact-support adjunction, for every finite coefficient
subextension and for the finite-subextension-valued algebraic closure.  The three assertions
are respectively clauses (1), (2), and (3) of the source statement.
Source: blueprint `sk-cor-affine-space-rational-line`
(blueprint: det-cor-affine-space-rational-line).

Proof (the ten steps of the DAG node):
1. The standard-chart theorem gives j and qj = p; finite-coordinate projective-space
properness gives proper q (`lemma-nagata-relative-affine-space-open-immersion`,
`lemma-nagata-projective-space-base-change-proper`).
2. On Spec R the affine projection is Spec R[t] -> Spec R, hence affine and locally of
finite type (`def-nagata-relative-affine-space`, `def-weil-finite-type-morphism`).
3. Affine-morphism permanence gives p quasi-compact and separated; proper q is separated
and quasi-compact. The qcqs-over-affine and qcqs permanence nodes give quasi-compact
V, affine line and projective line (`lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-qcqs-over-affine`, `lem-weil-pbc-qcqs-morphism-permanence`).
4. Composition preserves separatedness and local finite type; quasi-compactness over
Spec k follows from its quasi-separatedness. Both total spaces are separated finite-type
k-schemes and qcqs (`lem-weil-pbc-proper-fp-permanence`,
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-qcqs-morphism-permanence`).
5. A map from a quasi-compact scheme to a quasi-separated scheme is quasi-compact, so j
is quasi-compact and (j,q) is a compactification (`sk-def-nagata-sketch-data`).
6. For these rational coefficients Dctf = Dbc and their localizing closures agree.
Apply clause 1 of `det-sf-mate-open-restriction` and transport across this equality
(`det-def-localizing-closure-ctf-equals-bc`). This proves preservation and J adjoint R.
7. For (j,q), lower shriek is Rq_* j_! by definition. Compare the chosen compactification
to this one by `det-sf-comp-coherence-cocycle`, then use step 6 to obtain F isomorphic JQ.
8. Composition of exact module pullbacks gives j^* q^* isomorphic p^*. Levelwise exact
pullback commutes with shift, and `det-prop-sfb-cartesian-coefficients-twists` identifies
pullback of the Tate twist. Thus j^*(q^*N(1)[2]) is p^*N(1)[2]
(`sk-def-sfb-module-pushforward-pullback`, `sk-prop-sfb-cartesian-coefficients`).
9. Compose the natural Hom bijections of J adjoint R and Rq_* adjoint q^*(1)[2], supplied
by `det-prop-p1-adjunction-rational-triangle`, using steps 7 and 8. This gives F adjoint P
and preservation by P of the required localizing subcategory.
10. Any exceptional right adjoint G supplied by `sk-prop-sf-existence` is a right adjoint
to the same F. Transpose its counit under F adjoint P. Uniqueness of right adjoints gives
the natural isomorphism G to P and its uniqueness under the displayed counit identity
(`det-sp-unique-right-adjoint`).
-/
theorem det_cor_affine_space_rational_line
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      affineLineRationalAssertion (Profinite.continuousMapRingObj E.1) V
        (affineLineChosenCompactification k V)
        (fun X ↦ rationalTwistFunctor (Profinite.continuousMapRingObj E.1) X
          (spRationalTwist X ℓ E))) ∧
    affineLineRationalAssertion (Profinite.padicAlgClRingObj ℓ) V
      (affineLineChosenCompactification k V)
      (fun X ↦ rationalTwistFunctor (Profinite.padicAlgClRingObj ℓ) X
        (spQbarTwist X ℓ)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
