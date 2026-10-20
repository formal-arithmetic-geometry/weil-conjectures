/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Targets.AffineSpaceRationalLine
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.Paper.LocalizingClosureCtfEqualsBc
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.LocalizingLowerShriekComposition
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Rational purity for relative affine space in every dimension

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-cor-affine-space-rational/sk-cor-affine-space-rational-induction.md` and its proof
(blueprint: det-cor-affine-space-rational-induction).

The functors act on the literal localizing closures of the bounded constructible
module-object categories. Their comparisons with the ambient functors specify both
objects and maps. The Tate line is the existing signed power, transported back through
the existing equivalence with sectionwise modules before applying derived tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Derived tensor with the degree-d Tate line, in the internal-module encoding.
The signed line is the recorded tensor power; the existing sectionwise/internal module
equivalence changes only its presentation, not its coefficient ring or underlying sheaf.
Source: blueprint sk-def-sp-tate-twist, positive powers and derived twist formula
(blueprint: det-cor-affine-space-rational-induction). -/
def rationalDegreeTwistFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ℕ) :=
  rationalTwistFunctor Λ X
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.obj
        (spSignedTwist X (condensedRingObj Λ X) L (d : ℤ)))

/-- The Nagata compactification chosen in the chapter setting, for the projection
of relative affine d-space. The displayed over-objects and their instances are the
same canonical structure morphisms as those of the affine projection.
Source: blueprint sk-def-sfb-dc-setting, chosen compactification convention
(blueprint: det-cor-affine-space-rational-induction). -/
def affineSpaceChosenCompactification
    (k : Type u) [Field k] (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))] (d : ℕ) :
    Compactification (𝔸(ULift.{u} (Fin d); V) ↘ V) :=
  @compactificationOverField k _
    (Over.mk ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k))))
    (Over.mk (V ↘ Spec (.of k)))
    (inferInstanceAs (LocallyOfFiniteType
      ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact
      ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (IsSeparated
      ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact (V ↘ Spec (.of k))))
    (inferInstanceAs (IsSeparated (V ↘ Spec (.of k))))
    (Over.homMk (𝔸(ULift.{u} (Fin d); V) ↘ V) rfl)

/-- The ambient functor p_d^*(d)[2d], with the specified degree-d Tate tensor functor.
Source: blueprint sk-cor-affine-space-rational-induction, both conclusions
(blueprint: det-cor-affine-space-rational-induction). -/
def affineSpaceRationalPullTwistShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (V : Scheme.{u}) (d : ℕ)
    (twist : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V)))) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V))))) :=
  (CondensedRing.upperStar Λ (𝔸(ULift.{u} (Fin d); V) ↘ V)).leftDerivedFunctor ⋙
    twist ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- The two assertions for one rational coefficient convention. The functors F and P
are restrictions of the specified compactification lower shriek and twisted shifted
pullback, as witnessed by natural isomorphisms after the full inclusions. The adjunction
ensures existence of the exceptional right adjoint; every such adjoint G is isomorphic to P.
The final conjunct is preservation of Dbc by the ambient twisted shifted pullback itself.
Source: blueprint sk-cor-affine-space-rational-induction, entire statement
(blueprint: det-cor-affine-space-rational-induction). -/
def affineSpaceRationalAssertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (V : Scheme.{u}) (d : ℕ)
    (c : Compactification (𝔸(ULift.{u} (Fin d); V) ↘ V))
    (twist : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V)))) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V))))) : Prop :=
  (∃ (F : rationalLocalizingCategory Λ (𝔸(ULift.{u} (Fin d); V)) ⥤
        rationalLocalizingCategory Λ V)
      (P : rationalLocalizingCategory Λ V ⥤
        rationalLocalizingCategory Λ (𝔸(ULift.{u} (Fin d); V)))
      (_hF : F ⋙ rationalLocalizingInclusion Λ V ≅
        rationalLocalizingInclusion Λ (𝔸(ULift.{u} (Fin d); V)) ⋙
          rightDerivedLowerShriekOfCompactification Λ c)
      (_hP : P ⋙ rationalLocalizingInclusion Λ (𝔸(ULift.{u} (Fin d); V)) ≅
        rationalLocalizingInclusion Λ V ⋙ affineSpaceRationalPullTwistShift Λ V d twist)
      (_adjP : F ⊣ P),
      ∀ (G : rationalLocalizingCategory Λ V ⥤
          rationalLocalizingCategory Λ (𝔸(ULift.{u} (Fin d); V))),
        Nonempty (F ⊣ G) → Nonempty (G ≅ P)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)),
      constantModelBoundedConstructible Λ V K →
        constantModelBoundedConstructible Λ (𝔸(ULift.{u} (Fin d); V))
          ((affineSpaceRationalPullTwistShift Λ V d twist).obj K))

/-- Rational affine-space exceptional purity in every natural dimension, together
with preservation of bounded constructibility by p_d^*(d)[2d]. This includes d = 0,
all finite coefficient subextensions, and the finite-subextension-valued algebraic closure.
Source: blueprint sk-cor-affine-space-rational-induction, statement and proof
(blueprint: det-cor-affine-space-rational-induction).

Proof, following the seven DAG steps:
1. Put T_X = Loc(Dbc(X)). By det-def-localizing-closure-ctf-equals-bc the rational
   finite-Tor and bounded-constructible categories agree, as do their closures.
   det-proper-base-change-unbounded-pullback makes every inverse image exact,
   coproduct-preserving, and preserving Dbc and these precise closures.
2. The degree-one Tate line of sk-def-sp-tate-twist is locally free of rank one.
   Tensor with its dual is inverse to tensor with it. Thus its powers give exact
   coproduct-preserving tensor equivalences. On a common pro-etale trivializing
   cover they preserve finite constant scalar models and all vanishing degrees.
   They preserve Dbc, hence its localizing closure by the defining minimality of
   sk-def-localizing-closure. Shifts reindex cohomology and preserve both categories.
3. sk-prop-sfb-cartesian-coefficients identifies the pulled-back Tate lines.
   The strong monoidal inverse image and scalar comparison of def-sfb-module-upper-star
   give the tensor comparison, invertible locally where the line is trivial.
   Apply termwise to obtain pullback/twist/shift compatibility. Use the mate
   def-sfb-module-upper-star-comp for pullback composition. Reassociate the recorded
   tensor powers and add shifts to identify successive twists and shifts.
4. Induct on d uniformly over every base V in the setting. For d = 0 the affine
   projection is canonically the identity. Compare its chosen compactification with
   the identity by det-sf-comp-coherence-cocycle. Its lower shriek is therefore the
   identity; sk-prop-sf-existence and adjoint uniqueness identify its exceptional
   inverse image with the identity. The zero Tate power and shift give that functor.
5. lem-sfb-localizing-lower-shriek-composition and the adjunctions of
   sk-prop-sf-existence give Hom(Rb_! Ra_! M,N) = Hom(M,a^! b^! N), naturally.
   Uniqueness of the right adjoint gives (ba)^! isomorphic to a^! b^! on T.
6. For the step r to r+1 set W = A^r_V and let pi : A^1_W -> W be the projection.
   The polynomial-coordinate isomorphism phi : A^(r+1)_V -> A^1_W gives
   p_(r+1) = p_r pi phi. Finite polynomial generators and the closed diagonal show
   W is again separated finite type over k. For phi, compare with its proper
   compactification by det-sf-comp-coherence-cocycle; uniqueness gives phi^! = phi^*.
   Apply det-cor-affine-space-rational-line over W, the inductive hypothesis,
   and Step 5 twice. Move the twists and shifts through the pullbacks by Step 3,
   compose the pullbacks, then add the exponents and shifts to obtain (r+1)[2r+2].
7. For K in Dbc(V), Step 1 puts p_d^*K in Dbc and Step 2 preserves it under the
   degree-d twist and [2d]. A cohomological interval [a,b] becomes [a-2d,b-2d].
   This also handles the empty base and the zero complex. The natural isomorphism
   in Step 6 holds on the full localizing categories, including unbounded objects.
-/
theorem affineSpace_rational_induction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (d : ℕ) :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      affineSpaceRationalAssertion (Profinite.continuousMapRingObj E.1) V d
        (affineSpaceChosenCompactification k V d)
        (rationalDegreeTwistFunctor (Profinite.continuousMapRingObj E.1)
          (𝔸(ULift.{u} (Fin d); V)) (spRationalTwist (𝔸(ULift.{u} (Fin d); V)) ℓ E) d)) ∧
    affineSpaceRationalAssertion (Profinite.padicAlgClRingObj ℓ) V d
      (affineSpaceChosenCompactification k V d)
      (rationalDegreeTwistFunctor (Profinite.padicAlgClRingObj ℓ)
        (𝔸(ULift.{u} (Fin d); V)) (spQbarTwist (𝔸(ULift.{u} (Fin d); V)) ℓ) d) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
