/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FormalClosedSupport
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.FormalClosedSupportDerived
import Sheaf.Paper.RationalOpenDirectImageConstructible

/-!
# Rational closed support preserves finite constant constructibility

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-closed-adjoint-constructible-support.md`, final assertion, interpreted with
`sk-def-sfb-constructible` (blueprint: lem-sfb-rational-closed-support-constructible).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Closed support preserves bounded constructible complexes with finite constant scalar
models, both for finite subextensions E of Qbar and for the condensed algebraic closure.
The auxiliary open immersion j presents the complement of the given closed immersion i;
`formalClosedSupport` is the existing functor i* ker(id -> j*j*).

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-closed-adjoint-constructible-support.md`, final assertion and its proof
(blueprint: lem-sfb-rational-closed-support-constructible).

Proof:
1. The field is Noetherian. Finite type makes X and Z Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. X is quasi-separated by
   lem-weil-pbc-locally-noetherian-quasi-separated; the open complement is Noetherian
   and quasi-compact by lem-weil-pbc-noetherian-open-subscheme-noetherian. Thus j is
   quasi-compact by lem-weil-pbc-qcqs-morphism-permanence.
2. For f = i or j, sk-prop-sfb-cartesian-coefficients identifies coefficients and
   gives exact inverse image. Pull back the finite stratification by
   lemma-constructible-pullback-stratification and its local covers. The finite scalar
   matrices of det-def-sfb-constructible-local-model pull back to the same matrices;
   exactness preserves their cokernels. By lem-weil-pbc-site-pullback-abelian-exact
   and sk-def-sfb-derived-categories, cohomology pulls back termwise, retaining the
   original finite cohomological interval. Hence i* and j* preserve this Dbc.
3. Clause (3) of det-lem-formal-closed-support-derived gives the ambient distinguished
   triangle i_* RΓ_Z K -> K -> Rj_* j* K -> (i_* RΓ_Z K)[1], with the canonical unit.
   Its first term F is the fiber of this unit, without a constructibility premise.
4. Step 2 gives j* K in Dbc. Apply lem-sfb-rational-open-direct-image-constructible
   to the quasi-compact j: Rj_* j* K belongs to the same finite-model Dbc.
5. Apply the two-out-of-three and isomorphism closure of
   det-cor-coefficient-heart-ii-triangulated to obtain F in Dbc(X).
6. The fiber formula of det-lem-formal-closed-support-derived identifies RΓ_Z K
   with i* F. Step 2 for i and isomorphism closure give membership in Dbc(Z).
   The argument applies to both coefficient choices separately. -/
theorem rationalClosedSupportConstructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : DerivedCategory (FormalSupportModules (Profinite.continuousMapRingObj.{u} E) X)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Z
        ((formalClosedSupport (Profinite.continuousMapRingObj.{u} E) i j).rightDerivedFunctor.obj
          K)) ∧
    (∀ K : DerivedCategory (FormalSupportModules (Profinite.padicAlgClRingObj.{u} ℓ) X),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Z
        ((formalClosedSupport (Profinite.padicAlgClRingObj.{u} ℓ) i j).rightDerivedFunctor.obj
          K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
