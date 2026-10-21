/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen
import WeilConjectures.RepresentationTheory.IntegralModel

/-!
# Stratified finite coefficient models for continuous algebraic-closure coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), all-continuous obligation.
(blueprint: lem-sfb-continuous-algcl-stratified-finite-models).

The coefficient ring is C(-, PadicAlgCl ℓ) for the norm topology. The coefficient map
is postcomposition by a finite intermediate field's inclusion, pulled back from the point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite constant local models over the all-continuous algebraic closure descend to
lisse finite-extension models after refining the given constructible stratification.
Source: blueprint main-20261015, direct-image stability proof, paragraph (3).
(blueprint: lem-sfb-continuous-algcl-stratified-finite-models).

Proof:
1. On the given strata, finite scalar models over the field Ω have finite bases.
The basis isomorphism identifies each pulled-back model with a finite free B-module;
its inverse sends a tuple to the sum of its coordinates tensored with basis vectors.
Thus the restricted module is lisse, including rank zero (the local-model and lisse nodes).
2. Finite type over a field makes T Noetherian. Its closed subsets satisfy the minimal
condition. Open and closed subschemes and the successive reduced closed complements
remain separated of finite type, using finite-type composition and quasi-compact opens.
3. Induct on closed subsets of each original stratum. The empty subset has no pieces.
For a nonempty subset take its finitely many irreducible components, give them their
reduced induced structures, remove the other components, and choose a nonempty normal
open in each remaining integral component by lem-fin-dense-normal-open. These opens are
disjoint, and their complement is a proper closed subset. Induction gives finitely many
normal integral strata. Closed-immersion composition and restriction to an open show
that their immersions into T factor through their original strata. Noetherianity makes
the locally closed subsets constructible. Integral pieces are connected.
4. Pull back the finite free local models to these pieces, using module pullback and
the canonical coefficient comparison. On each nonempty normal connected piece choose
a geometric point. The node lem-sfb-normal-continuous-algcl-monodromy identifies the
lisse module with a continuous finite-dimensional representation over Ω.
5. Its étale fundamental group is compact. Apply the compact-matrix coefficient-descent
node lem-real-compact-matrix-coefficient-descent to its entrywise continuous matrix
representation to obtain a finite intermediate field containing all matrix entries.
6. The matrices of inverse group elements also lie in that field, giving a representation
over E. The restricted norm topology makes it continuous. The finite-field monodromy
inverse produces a lisse E-module. The same monodromy comparison for E → Ω identifies
its ordinary scalar extension with the original representation: the basis isomorphism
Ω ⊗_E Eⁿ ≅ Ωⁿ is equivariant. Full faithfulness gives the required module isomorphism.
7. Assemble the independent models on the finitely many refined pieces. No gluing
across strata or finite-subextension-valued restriction on coefficient sections is used.
For empty T use the empty partition; zero modules use rank zero and the base field. -/
theorem continuousAlgCl_stratified_finite_models
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) T))
    (P : T.FiniteLocallyClosedStratification)
    (hP : ∀ b : Fin P.n, Topology.IsConstructible (P.stratum b))
    (hM : ∀ b : Fin P.n,
      HasFiniteConstantLocalModel (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) (P.domain b)
        ((upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) (P.immersion b)).obj M)) :
    ∃ S : T.FiniteLocallyClosedStratification,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      (∀ a : Fin S.n, ∃ b : Fin P.n, S.stratum a ⊆ P.stratum b) ∧
      ∀ a : Fin S.n, ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
        FiniteDimensional ℚ_[ℓ] E ∧
        ∃ L : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) (S.domain a)),
          IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L ∧
          Nonempty ((Mod.extendScalars
            (R := condensedRingObj (Profinite.continuousMapRingObj E) (S.domain a))
            ((upperStarFromPoint (S.domain a)).map
              ((sheafCompose (coherentTopology Profinite.{u})
                (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
                  (Profinite.continuousMapRingSheafMapOfUniverse
                    (algebraMap E (PadicAlgCl ℓ)) continuous_subtype_val)))).obj L ≅
            (upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) (S.immersion a)).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
