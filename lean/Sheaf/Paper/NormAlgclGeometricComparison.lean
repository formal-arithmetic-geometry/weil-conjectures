/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.NormAlgclCoefficientMap
public import Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Galois.Profinite
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Normalizing geometric coefficient comparison before arithmetic invariants

Source: steps 1 and 4 of the agent coefficient-topology obligation
`lem-sfb-norm-algcl-cohomology-topology-comparison`, and the normalized geometric
finite scalar model and condensed Galois descent cited there. An exact external
reference for this inherited norm-topology obligation remains WANTED.
The conclusion concerns a bounded geometric complex and a commuting square; it makes
no invertibility assertion about the arithmetic comparison. The coefficient constructions
are shared verbatim with the parent theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open Profinite.AlgclInvariantsComparison
open CategoryTheory.CondensedBar

namespace AlgebraicGeometry.ProEtale.NormAlgclComparison

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] (ks : Type u) [Field ks] [Algebra k ks] [IsSepClosure k ks]

/-- Geometric cohomology and scalar-compatible Galois descent give a bounded comparison
model for the actual sectionwise coefficient inclusion. Its cohomology objects are the
condensations of finite-dimensional continuous representations. The two families of cohomology
isomorphisms identify the actual global coefficient map with the specified universal
left-derived tensor transformation, followed by ordinary right-derived invariants.
In particular, the conclusion does not assume or assert that any component of that
transformation is invertible.

Source: steps 1 and 4 of
`lem-sfb-norm-algcl-cohomology-topology-comparison`, using the geometric finite scalar
model and ordinary condensed Galois descent
(blueprint: lem-sfb-norm-algcl-geometric-comparison-normalization).

Proof:
Choose the normalized geometric finite scalar model over the specified separable
closure. Identify its finite coefficient ring with `scalarRing` and its two closure
coefficient rings with the published finite-subextension and norm-continuous rings.
These identifications are the sectionwise identity (with the canonical universe-lift
identifications when the arbitrary-closure model is used); they preserve multiplication,
restriction, generalized Galois actions, and the scalar inclusions. Take K to be its
finite-field geometric derived sections. Before applying the model, transport V through
its canonical scheme-module localization equivalence; this equivalence factors the
same complex localization, preserves homology and the canonical derived scalar tensors,
and therefore preserves constant-model bounded constructibility. Boundedness and the
finite-dimensional
continuous representations of each H^q(K) are the geometric model's first clauses.
Any two condensations of the same representation are canonically isomorphic: compose
their section identifications, and use the scalar, restriction and action equations to
obtain mutually inverse equivariant module maps.

The supplied tensor models have the prescribed ordinary diagonal action. Thus forgetting
that action identifies them with the two relative tensor functors. Their universal
left-derived counits identify their derived functors with the restrictions of the
geometric model's equivariant derived scalar extensions; uniqueness of total derived
functors makes these identifications compatible with the actual coefficient morphism.
The equation for `eta` and the section equation for `c` ensure that this is the original
inclusion, rather than an independently chosen arrow. The same uniqueness argument
identifies the supplied invariant-submodule functor with the geometric model's one:
both are the right adjoint to trivial inflation with the specified fixed-section
inclusion. Exact point evaluation commutes with its ordinary right derived functor.

Finite type over the affine field spectrum makes X quasi-compact, and separatedness
makes it quasi-separated, so the hypotheses of ordinary Galois descent hold.
Compose the two geometric projection isomorphisms with the descent isomorphisms to
obtain endpoint isomorphisms in the larger localization universe. The canonical
comparison of two localization universes commutes with homology: both homology
functors factor the same complex homology functor through quasi-isomorphisms.
Applying homology therefore gives eC and eB in the common category of abelian groups.
Forgetting the finite coefficient action identifies the right-derived global sections
used here with ordinary derived global sections of the underlying abelian sheaf.
For this composition assertion one also uses preservation of K-injectives: the
free-coefficient left adjoint is exact because the finite coefficient sheaf is
sectionwise a rational vector space, hence flat as an abelian sheaf. The normalized
internal/section-module equivalence identifies these tensors and their adjunctions.
Apply derived invariants and point evaluation to the
C-linear geometric coefficient square. Scalar naturality of descent, together with
the sectionwise construction of `coefficientModuleMap`, identifies its top edge with
the displayed global
map and its bottom edge with the universal derived transformation. This gives precisely
the equation below. No comparison isomorphism is inferred for that bottom edge, and
no finite cohomological dimension or convergence of an infinite tower is used. The
zero complex, empty scheme and rank-zero representation obey the same equations.
-/
theorem geometric_comparison_normalization
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    [ActionAbelian (scalarRing.{u} ℓ E) (ks ≃ₐ[k] ks)]
    [IsGrothendieckAbelian.{u + 1} (Equivariant (scalarRing.{u} ℓ E) (ks ≃ₐ[k] ks))]
    [HasDerivedCategory.{u + 2} (Equivariant (scalarRing.{u} ℓ E) (ks ≃ₐ[k] ks))]
    [HasDerivedCategory.{u + 2} Ab.{u + 1}]
    (I : Invariants (scalarRing.{u} ℓ E) (ks ≃ₐ[k] ks))
    [(pointEvaluation.{u} ℓ E).Additive]
    (TC : TensorModel ℓ E (ks ≃ₐ[k] ks) (finiteModule ℓ E))
    (TB : TensorModel ℓ E (ks ≃ₐ[k] ks) (normModule ℓ E))
    (c : finiteModule.{u} ℓ E ⟶ normModule ℓ E)
    (eta : TC.functor ⟶ TB.functor)
    (LC : DerivedTensor ℓ E (ks ≃ₐ[k] ks) TC)
    (LB : DerivedTensor ℓ E (ks ≃ₐ[k] ks) TB)
    (hc : ∀ (S : Profinite.{u}) (z : (finiteModule ℓ E).X.obj.obj (op S)),
      ((c.hom.hom.app (op S)) z).down = z.down.val)
    (heta : ∀ M : Equivariant (scalarRing ℓ E) (ks ≃ₐ[k] ks),
      (eta.app M).val ≫ TB.underlying.hom.app M =
        TC.underlying.hom.app M ≫ c ▷ M.module)
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hV : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X V) :
    let alpha := Functor.whiskerRight (derivedCoefficientMap ℓ E (ks ≃ₐ[k] ks) LC LB eta)
      (I.functor ⋙ pointEvaluation ℓ E).rightDerivedFunctor
    let H := DerivedCategory.homologyFunctor Ab.{u + 1}
    letI : HasDerivedCategory.{u + 1} Ab.{u + 1} :=
      HasDerivedCategory.ofIsGrothendieckAbelian Ab.{u + 1}
    ∃ K : DerivedCategory (Equivariant (scalarRing.{u} ℓ E) (ks ≃ₐ[k] ks)),
      DerivedCategory.TStructure.t.bounded K ∧
      (∀ q : ℤ, ∃ (W : Type (u + 1)) (ng : NormedAddCommGroup W),
        letI := ng
        ∃ (ns : NormedSpace E W), letI := ns
        ∃ (fd : FiniteDimensional E W) (rho : (ks ≃ₐ[k] ks) →* Module.End E W),
          Continuous (fun x : (ks ≃ₐ[k] ks) × W ↦ rho x.1 x.2) ∧
          ∃ N : RepresentationModel ℓ E (ks ≃ₐ[k] ks) W rho,
            Nonempty ((DerivedCategory.homologyFunctor _ q).obj K ≅ N.object)) ∧
      ∃ (eC : ∀ q : ℤ,
          (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj ((derivedGlobalSections ℓ X E).obj
            (Arrow.mk (comparison ℓ X E V)).left) ≅
            (H q).obj (Arrow.mk (alpha.app K)).left)
        (eB : ∀ q : ℤ,
          (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj ((derivedGlobalSections ℓ X E).obj
            (Arrow.mk (comparison ℓ X E V)).right) ≅
            (H q).obj (Arrow.mk (alpha.app K)).right),
        ∀ q : ℤ, (DerivedCategory.homologyFunctor Ab.{u + 1} q).map
          ((derivedGlobalSections ℓ X E).map
            (comparison ℓ X E V)) ≫
            (eB q).hom = (eC q).hom ≫ (H q).map (alpha.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.NormAlgclComparison
