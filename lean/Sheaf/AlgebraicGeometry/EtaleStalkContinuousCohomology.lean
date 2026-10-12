/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Continuous cohomology of the geometric stalk over a field

Source: Stacks Project, Tags 04JQ, 03QU and Section 0DVG.
(blueprint: lem-sc-etale-stalk-continuous-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Compare cohomology of any abelian etale sheaf with continuous cohomology of its stalk.
The additive identification `c` must carry geometric transport of germs to the action on
`M`. Coefficients live in the field universe; sheaf values may be one universe higher.

Source: Stacks Project, Tags 04JQ and 03QU; Section 0DVG.
(blueprint: lem-sc-etale-stalk-continuous-cohomology).

Proof: The abelian geometric stalk equivalence of Tag 04JQ carries `F` to a discrete
Galois module. Every Galois automorphism of the separable closure extends to the algebraic
closure, and germs jointly generate the stalk. Thus `hc` says precisely that `c` is an
isomorphism of coefficient modules. Global sections are the invariant elements (03QU).
The equivalence is exact and preserves injectives, so transport an injective resolution
of `F` to obtain the derived invariants of its stalk.
For a profinite group and discrete coefficients, continuous cochains form an exact
cohomological delta-functor: a cochain has finite image on each compact finite power, so
one can choose finitely many lifts through any surjection. It is effaceable in positive
degrees by embedding a module into locally constant functions on the group, with action
by right translation and embedding the orbit function. Compactness gives a common open
stabilizer for each such function. Insertion of the first coordinate gives the contracting
homotopy, and its continuity follows from the finite clopen partitions. Hence this
universal delta-functor agrees with derived invariants in every degree. This argument
uses integer modules, with no finiteness hypothesis on the coefficient ring.
Finally the compact-open exponential law identifies iterated continuous maps with maps on
finite powers. Evaluation at `(1, g1, g1*g2, ...)` and the inverse
`c ↦ ((g0, ..., gn) ↦ g0 • c(g0⁻¹*g1, ..., g(n-1)⁻¹*gn))` identify homogeneous invariant
cochains with inhomogeneous cochains and commute with differentials. The resulting
cohomology equivalences, followed by coefficient transport along `c`, give the assertion;
universe lifts are removed using their canonical additive equivariant lift/down maps. -/
theorem nonempty_equiv_etale_cohomology_continuous_stalk
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (M : TopRep.{u} ℤ (Gal(Ks/K))) [DiscreteTopology M]
    (c : ((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F
      ≃+ M)
    (hc : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      c ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z) =
      M.ρ g (c ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z)))
    (n : ℕ) :
    Nonempty (Sheaf.H.{u + 1} F n ≃ continuousCohomology n M) := by sorry

end AlgebraicGeometry.Scheme
