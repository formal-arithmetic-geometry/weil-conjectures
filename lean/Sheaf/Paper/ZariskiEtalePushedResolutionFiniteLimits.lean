module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction
/-- Abelian pullback along an open-restriction lift preserves finite limits.

Source: Stacks Project, Sites, Tags 00X5 and 00X6; Etale Cohomology, Tag 09AX;
Modules on Sites, Tag 03DJ.
(blueprint: lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits)

Proof: put W = i(top). The forgetful equality identifies the underlying scheme of
W with X. Each map i(U) -> W has underlying map X|U -> X, hence is the usual open
immersion into the underlying scheme of W. Thus i factors through the localized
etale site over W as its usual Zariski inclusion. Restriction of etale sheaves to
W followed by the usual Zariski direct image is the given continuous direct image.
The usual abelian inverse image is exact. Restriction to W has exact left adjoint
extension by zero: its presheaf construction is the direct sum over arrows to W,
which preserves monomorphisms, followed by exact sheafification; its adjunction
also gives right exactness. Compose these two exact left adjoints. Uniqueness of
left adjoints identifies that composite with the displayed sheaf pullback. Exact
additive functors between abelian categories preserve finite limits, giving the
claim. This argument applies to arbitrary i, without asserting that W is terminal
in X.Etale. Neither a coefficient sheaf nor cohomology vanishing is needed. -/
theorem zariski_etale_pushed_resolution_finite_limits
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    :
    PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) := by sorry
