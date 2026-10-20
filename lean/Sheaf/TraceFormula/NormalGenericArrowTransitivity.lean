/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Sheaf.CategoryTheory.Sites.GeometricMorphism

import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.RingTheory.ProEtale.IndEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.TraceFormula.PointArrowsStrictLocalLifts
import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# Generic geometric specialization arrows over a normal base

Source: Orgogozo, *Modifications et cycles proches sur une base générale*, proof of
Lemma 8.3.2, printed p. 18 (blueprint: lem-trf-normal-generic-arrow-transitivity).

Arrows are natural transformations on direct images, following
`CategoryTheory.GeometricMorphism`. Mathlib's skyscraper functor is the canonical
right adjoint to the set-valued geometric stalk, by `Point.skyscraperSheafAdjunction`.
Thus its natural transformations are exactly the required topos-point arrows.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The direct image of the geometric point defined by the given residue-field embedding.
When `η` is generic and `Ω` is an algebraic closure of its residue field, this is the direct
image of the geometric generic point in Orgogozo, proof of Lemma 8.3.2, printed p. 18
(blueprint: lem-trf-normal-generic-arrow-transitivity).

The scheme map is `Spec (κ(η) → Ω)` followed by the canonical residue-field point;
the direct image is Mathlib's skyscraper sheaf functor, with no choice of a point morphism. -/
noncomputable def genericGeometricPointDirectImage
    (N : Scheme.{u}) (η : N) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra (N.residueField η) Ω] :
    Type (u + 1) ⥤ Sheaf N.smallEtaleTopology (Type (u + 1)) :=
  (pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap (N.residueField η) Ω)) ≫
      N.fromSpecResidueField η)).skyscraperSheafFunctor

/-- On a normal integral scheme, generic geometric specialization arrows to a fixed geometric
point form a nonempty transitive set under precomposition by generic-point automorphisms.
Source: Orgogozo, proof of Lemma 8.3.2, printed p. 18
(blueprint: lem-trf-normal-generic-arrow-transitivity).

Proof (the seven DAG steps):
1. Choose an affine neighbourhood `Spec B` of the support of `n`. Its generic point has
   residue field `Frac B`, and `B` is a normal domain (integrality, generic points and
   localization at the zero prime).
2. The strict-local ring `C` at `n` is the local filtered colimit of the pointed étale
   residue-triple diagram (`etale_local_ring_triples`, `strictHenselization_triples`).
   The normal local-colimit theorem makes `C` a normal domain and `B → C` injective.
3. The extension `Frac C / Frac B` is algebraic separable by ind-étaleness and
   `Algebra.IndEtale.isSeparable_residueField` at the zero prime.
4. Extend the embedding of the function field to `Frac C → Ωη`. Its restriction to `C`
   gives a strict-local lift, hence a point arrow by
   lem-trf-point-arrows-strict-local-lifts. This proves nonemptiness.
5. The strict-local lifts of any two arrows give injective `B`-maps `C → Ωη`: a nonzero
   element satisfies an algebraic relation with nonzero constant coefficient, after
   clearing denominators. Extend these to embeddings of `Frac C`.
6. Extend the isomorphism between their images to an endomorphism of `Ωη` fixing the
   function field (lem-weil-pbc-algebraic-extension-embeds-algebraically-closed). It is
   surjective because it permutes the finite set of distinct roots of every minimal
   polynomial. This includes inseparable polynomials.
7. Equivariance of the strict-local lift/arrow correspondence gives `a = σ.hom ≫ b`.
   Categorical composition makes this the right precomposition action: for a point arrow
   `a` its value at `σ` is `σ.hom ≫ a`. Identity and associativity are the usual functor
   category laws, with the target fixed. No freeness or uniqueness is claimed. -/
theorem normal_generic_arrow_transitivity
    {N : Scheme.{u}} [IsIntegral N]
    (hN : ∀ x : N,
      IsDomain (N.presheaf.stalk x) ∧ IsIntegrallyClosed (N.presheaf.stalk x))
    (η : N) (hη : IsGenericPoint η Set.univ)
    (Ωη : Type u) [Field Ωη] [IsAlgClosed Ωη] [Algebra (N.residueField η) Ωη]
    [Algebra.IsAlgebraic (N.residueField η) Ωη]
    {Ωn : Type u} [Field Ωn] [IsAlgClosed Ωn] (n : Spec (.of Ωn) ⟶ N) :
    Nonempty (genericGeometricPointDirectImage N η Ωη ⟶
      (pointSmallEtale n).skyscraperSheafFunctor (A := Type (u + 1))) ∧
    ∀ (a b : genericGeometricPointDirectImage N η Ωη ⟶
      (pointSmallEtale n).skyscraperSheafFunctor (A := Type (u + 1))),
      ∃ σ : Aut (genericGeometricPointDirectImage N η Ωη), a = σ.hom ≫ b := by
  sorry

end AlgebraicGeometry.Scheme
