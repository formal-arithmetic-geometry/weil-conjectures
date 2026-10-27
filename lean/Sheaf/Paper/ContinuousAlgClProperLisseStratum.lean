/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Proper finiteness for one all-continuous lisse stratum

Source: the lisse-piece calculation in the proof of
`det-sf-comp-continuous-algcl-heart-finiteness`.
(blueprint: lem-sfb-continuous-algcl-proper-lisse-stratum).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The proper image of one reduced locally closed lisse piece has constructible
cohomology over the actual all-continuous coefficient ring.

Source: det-sf-comp-continuous-algcl-heart-finiteness, its single proof step,
from the proper-image paragraph of det-sf-comp-coherence-single.
(blueprint: lem-sfb-continuous-algcl-proper-lisse-stratum).

Proof: work on a finite normal refinement of the reduced finite-type stratum S.
On a connected normal piece, the lisse module is a finite-rank continuous
representation of the profinite fundamental group. The compact-monodromy theorem
PadicAlgCl.exists_finiteDimensional_forall_mem puts its matrix entries in a finite
extension E of Q_ell. The invariant integral-lattice theorem supplies an O_E-lattice;
extend its E-coefficient sheaf by zero along the specified locally closed immersion.
Apply finite-coefficient proper finiteness, reduce the lattice modulo powers of ell,
and use the uniform proper torsion bound and the Milnor sequence to recover the
integral calculation. On an adapted target stratum this calculation has a bounded
finite-projective cochain model. The coefficient-change comparison on this model
is termwise the same finite sums, matrices and differentials. Inverting ell and
extending to the full continuous-map ring therefore computes the actual proper
image of the extended lisse piece. Its cohomology is finite constant on a further
finite target stratification. Negative cohomology vanishes by left t-exactness.
Descent of the trivializing covers gives finite
constant local models. The normalization/refinement localization sequences and
noetherian induction assemble the calculation on S. This argument treats only
one locally closed lisse piece: the finite filtration of an arbitrary constructible
sheaf is performed in the parent theorem. The zero lisse module and empty S give
zero models. The comparison must use all continuous maps to PadicAlgCl, including
those whose images lie in no finite subextension; no equality with the
finite-subextension-valued condensed ring is asserted. -/
theorem continuousAlgCl_proper_lisse_stratum
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
    (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) S))
    (hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) L) :
    ∀ n : ℤ, IsConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
      ((DerivedCategory.homologyFunctor _ n).obj
        ((lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((openImmersionLowerShriek (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) v).obj
              ((lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) t).obj L))))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
