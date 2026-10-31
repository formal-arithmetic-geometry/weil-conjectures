/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedPart
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Classical étale inputs with finite coefficients

Source: the current blueprint, `sk-prop-classical-inputs/_section.md`, the proper base
change, finiteness, and cohomological-dimension clauses; Stacks Project, Tags 0F0C, 0GL0,
and 0F10 (blueprint: sk-prop-classical-inputs).

The unbounded classical condition is the essential image of the derived comparison
inverse image. Compact supports are written using an arbitrary compactification,
which presents the same compact-support functor. The bounded constructible predicate
is the finite constant scalar-model predicate of `sk-def-sfb-constructible`.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper base change on unbounded classical complexes with finite ell-primary
coefficients, with the canonical unit-square-counit exchange map.

Source: current blueprint `sk-prop-classical-inputs`, Proper base change; Stacks 0F0C
(blueprint: sk-prop-classical-inputs).

Proof: write K as the comparison pullback of an unbounded etale complex E. The common
ell-power annihilator makes the coefficient ring torsion, so etale unbounded proper
base change applies. Unbounded direct-image comparison for finite-type schemes over
the given field and inverse-image comparison identify both endpoints. These comparisons
respect exchange: expand the mate into its unit, square, and counit and cancel the
intermediate unit/counit by the triangle identities. Thus the specified map is invertible.
-/
theorem classicalInputs_properBaseChange
    (ell : ℕ) (hEll : ell.Prime) (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : (ell : k) ≠ 0)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell ^ r) • (1 : A) = 0)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (p : X ⟶ S) [p.IsOver (Spec (.of k))] [IsProper p]
    {S' : Scheme.{u}} [S'.Over (Spec (.of k))]
    [IsSeparated (S' ↘ Spec (.of k))] [LocallyOfFiniteType (S' ↘ Spec (.of k))]
    [QuasiCompact (S' ↘ Spec (.of k))]
    (g : S' ⟶ S) [g.IsOver (Spec (.of k))]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.essImage K) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (IsPullback.of_hasPullback p g).toCommSq).app K) := by
  sorry

/-- Proper base change at an arbitrary algebraically closed geometric point, and the
resulting identification of the derived geometric stalk with fibre cohomology.

Source: current blueprint `sk-prop-classical-inputs`, Proper base change, final sentence
(blueprint: sk-prop-classical-inputs).

Proof: use the same etale proper base change as above. The proper fibre morphism is
finite type over Omega; apply the unbounded direct-image comparison to it over Omega
and to p over k. No finite-type hypothesis on the geometric point over k is used.
Spec Omega is w-contractible, so its pro-etale sections compute derived sections
termwise. Etale sheaves on Spec Omega are constant, and the stalk comparison identifies
these sections with the exact geometric stalk on classical objects, even unbounded ones.
Finally apply derived global sections to exchange and use unbounded composition of
right derived direct images to identify RΓ(Spec Omega, Rp'_*g'^*K) with fibre cohomology.
-/
theorem classicalInputs_geometricFiber
    (ell : ℕ) (hEll : ell.Prime) (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : (ell : k) ≠ 0)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell ^ r) • (1 : A) = 0)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (p : X ⟶ S) [p.IsOver (Spec (.of k))] [IsProper p]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.essImage K) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (IsPullback.of_hasPullback p s).toCommSq).app K) ∧
    Nonempty ((derivedGeometricStalk (ModuleCat.{u + 1} (ULift.{u + 1} A)) s).obj
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.obj K) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (pullback p s)).obj
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
            (pullback.fst p s)).leftDerivedFunctor.obj K)) := by
  sorry

/-- Compactly supported direct image preserves bounded constructibility, with no
finite-Tor-amplitude assumption. The compactification is a presentation of Rf_!.

Source: current blueprint `sk-prop-classical-inputs`, Finiteness; Stacks 0GL0
(blueprint: sk-prop-classical-inputs).

Proof: finite-type schemes over a field are Noetherian and qcqs, and the separated
finite-type morphism is finitely presented. A compactification exists by Nagata; its
open immersion is quasi-compact. The finite coefficient ring is Noetherian and its
additive orders are invertible on the target. Constructible comparison expresses the
input as the pullback of a bounded constructible etale complex. Stacks 0GL0 gives
constructible cohomology of its compact-support image. Exact open extension and the
finite relative cohomological dimension of the proper compactification map bound the
image in a finite interval. Compact-support comparison and constructible comparison
transport this bounded constructible object to the given internal coefficient modules.
-/
theorem classicalInputs_finiteness
    (ell : ℕ) (hEll : ell.Prime) (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : (ell : k) ≠ 0)
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ r : ℕ, (ell ^ r) • (1 : A) = 0)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : _root_.DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
    (hK : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X K) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) S
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (FiniteDiscreteOrdinary.coefficient A) c).obj K) := by
  sorry

/-- Finite cohomological amplitude of ordinary and compactly supported direct images
on bounded-below classical complexes, and finiteness of relative ell-dimension.

Source: current blueprint `sk-prop-classical-inputs`, Cohomological dimension;
Stacks 0F10 (blueprint: sk-prop-classical-inputs).

Proof: 0F10(1) supplies a uniform nonnegative higher-direct-image bound for torsion
abelian etale sheaves. The common coefficient exponent transfers it to module sheaves;
forgetting modules detects zero objects. Enough injectives and the finite-cd derived
upper-bound lemma give the upper bound b+d, while left exactness gives the lower bound a.
The bounded-below classical equivalence and exact comparison pullback transport these
bounds and classicality to pro-etale complexes. For compact supports write Rf_! as
Rq_*D(j_!) for c. Exactness of j_! preserves all intervals; apply the preceding bound to
q and compact-support comparison. Enlarge the two nonnegative bounds to a common d.
Finally 0F10 bounds all locally ell-power torsion sheaves, with no common exponent;
the comparison in sk-def-cd identifies their relative supremum with the etale one.
-/
theorem classicalInputs_cohomologicalAmplitude
    (ell : ℕ) (hEll : ell.Prime) (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : (ell : k) ≠ 0)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell ^ r) • (1 : A) = 0)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    relativeCohomologicalDimension ell hEll f < ⊤ ∧
    ∃ d : ℕ, ∀ K : _root_.DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))),
      ClassicalPlus X (ULift.{u + 1} A) K →
      ClassicalPlus S (ULift.{u + 1} A)
        ((lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctorPlus.obj K) ∧
      ClassicalPlus S (ULift.{u + 1} A)
        ((rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K) ∧
      ∀ a b : ℤ, _root_.DerivedCategory.IsGE K.obj a →
        _root_.DerivedCategory.IsLE K.obj b →
        _root_.DerivedCategory.IsGE
          ((lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor.obj K.obj) a ∧
        _root_.DerivedCategory.IsLE
          ((lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor.obj K.obj) (b + d) ∧
        _root_.DerivedCategory.IsGE
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K.obj) a ∧
        _root_.DerivedCategory.IsLE
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K.obj) (b + d) := by
  sorry

end AlgebraicGeometry.ProEtale
