/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-! # The fundamental group of the spectrum of a field

Source: Stacks Project, Tag 0BNE, lemma-fundamental-group-Galois-group (1)-(2),
and Tag 0BQ9, remark-variance (blueprint: lem-dl-a1-field-fundamental-galois).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Restriction from an algebraic closure and the geometric-fibre action identify the two
field automorphism groups with the fundamental group, compatibly with intermediate fields.

Source: Stacks Project, Tags 0BNE and 0BQ9, with the base-change map of Tag 0BND (3)
(blueprint: lem-dl-a1-field-fundamental-galois).

`Ks` is the embedded separable closure in `Ω`. The pair of hypotheses `IsAlgClosed Ω` and
`Algebra.IsAlgebraic K Ω` is exactly `IsAlgClosure K Ω`. `G` is any small fundamental-group
model of the existing finite-etale fibre functor, with its fibre-functor topology.
The Yoneda comparison in `exists_finiteEtale_flc_equivalence_sheaf` identifies this group
with the natural automorphisms of the recorded `flcFiber`, including evaluation topologies.
The equation defining `r` says that it is restriction. The equation with
`galoisToFundamentalGroup` specifies `e` by the canonical action, with no choice of path.
For every finite etale algebra `A`, the equivalence `β` is characterized by its actual
geometric point in `Ω`, and the second equation is postcomposition by `g`. This includes
finite separable fields and every field factor of an arbitrary finite etale algebra.
For an intermediate field `L`, the path `τ` is characterized by projection on every
geometric point of every base-changed cover. Thus the last equation uses exactly the
canonical map induced by `Spec L ⟶ Spec K`, also for infinite intermediate extensions.

Proof, following the node's eight steps:
1. An automorphism of Ω preserves Ks because it preserves separable polynomials.
`lem-exc-galois-automorphism-extension` gives surjectivity of restriction. By
`lem-weil-pbc-separable-first-purely-inseparable`, Ω/Ks is purely inseparable, so every
extension is unique: equality on suitable p-power powers implies equality in a field.
In characteristic zero Ks = Ω. This constructs the group isomorphism r.
2. The Krull neighbourhood basis consists of stabilizers of finite sets. Restriction
pulls such stabilizers back to stabilizers. Conversely, replace each element of Ω by
a suitable p-power power in Ks; the two stabilizers agree. Hence r and its inverse
are continuous, including in positive characteristic.
3. `thm-galois-lc-etale` identifies finite covers and FLC sheaves with their fibres.
Finite covers are affine by `def-weil-finite-integral-morphism`; the product theorem
`lem-weil-pbc-etale-algebra-over-field-product` decomposes their coordinate algebras
into finite separable fields. Their geometric embeddings factor uniquely through Ks.
This gives the equivalences β naturally, including the empty product.
4. Postcomposition by a Galois element commutes with algebra homomorphisms, hence
is a natural automorphism. On geometric points it is precomposition with Spec of
its unique lift to Ω. On a finite Galois intermediate field, evaluate an arbitrary
natural automorphism at the inclusion; normality makes this a field automorphism.
5. Naturality makes these finite-Galois automorphisms compatible. The inverse-limit
identification `lem-exc-galois-krull-finite-limit` reconstructs a unique g. By
`lem-weil-pbc-finite-set-in-finite-galois-subextension`, each finite separable
embedding factors through such a finite Galois subfield. Naturality therefore gives
the displayed action formula on each factor and proves that e is bijective.
6. `lem-exc-etale-field-geometric-action-continuous` proves continuity of the action.
Finite-Galois evaluations and the inverse-limit description prove continuity of its
inverse. `lem-galois-aut-profinite` gives profiniteness of the fibre automorphisms;
transport along r and e proves all the displayed profiniteness assertions.
7. `lem-weil-pbc-separable-closure-exists-galois` makes Ks/L separable algebraic and
normal. Ks remains separably closed, so is a separable closure of L. Ω is still an
algebraic closure of L, and the same construction gives eL with the stated action.
8. A point of a pulled-back cover projects to its original geometric point, giving
the path τ of `lem-galois-pi1-functoriality`. A lift to Ω of an L-automorphism fixes
L, so precomposition preserves the second component of the lifted point and acts
on the first by the same automorphism. The equivariance equation for
`fundamentalGroupMap` gives the inclusion formula on every fibre, hence in G. -/
theorem field_fundamental_galois
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (Ks : IntermediateField K Ω) [IsSepClosure K Ks]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj P)]
    [IsFundamentalGroup (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))) G] :
    ∃ (r : Gal(Ω/K) ≃ₜ* Gal(Ks/K)) (e : Gal(Ks/K) ≃ₜ* G),
      (∀ (σ : Gal(Ω/K)) (a : Ks),
        algebraMap Ks Ω (r σ a) = σ (algebraMap Ks Ω a)) ∧
      (∀ σ : Gal(Ω/K), e (r σ) =
        galoisToFundamentalGroup (𝟙 (Spec (.of K))) (Iso.refl _) G σ) ∧
      (∀ A : FiniteEtaleAlgebra K,
        ∃ β : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj
            (constantCover (𝟙 (Spec (.of K))) A) ≃ (A.1 →ₐ[K] Ks),
          (∀ x, (fiberConstantCoverEquiv (𝟙 (Spec (.of K)))
              (pointOfAlgebra Ω (𝟙 (Spec (.of K)))) A x).1 =
            (algebraMap Ks Ω).comp (β x).toRingHom) ∧
          (∀ (g : Gal(Ks/K)) (x), β (e g • x) = g.toAlgHom.comp (β x))) ∧
      CompactSpace Gal(Ω/K) ∧ T2Space Gal(Ω/K) ∧ TotallyDisconnectedSpace Gal(Ω/K) ∧
      CompactSpace Gal(Ks/K) ∧ T2Space Gal(Ks/K) ∧ TotallyDisconnectedSpace Gal(Ks/K) ∧
      T2Space G ∧ TotallyDisconnectedSpace G ∧
      ∀ L : IntermediateField K Ks,
        IsSepClosure L Ks ∧
        ∀ (Gsub : Type u) [Group Gsub] [TopologicalSpace Gsub] [IsTopologicalGroup Gsub]
          [CompactSpace Gsub]
          [∀ Q, MulAction Gsub ((fiber (pointOfAlgebra Ω (𝟙 (Spec (.of L))))).obj Q)]
          [IsFundamentalGroup (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of L))))) Gsub],
          ∃ (eL : Gal(Ks/L) ≃ₜ* Gsub)
            (τ : pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
              fiber (pointOfAlgebra Ω (𝟙 (Spec (.of L)))) ≅
                fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))),
            (∀ (h : Gal(Ks/L)) (σ : Gal(Ω/L)),
              (∀ a : Ks, σ (algebraMap Ks Ω a) = algebraMap Ks Ω (h a)) →
              eL h = galoisToFundamentalGroup (𝟙 (Spec (.of L))) (Iso.refl _) Gsub σ) ∧
            (∀ (P : (Spec (.of K)).FiniteEtale)
              (z : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of L))))).obj
                ((pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj P)),
              (τ.hom.app P z).left = z.left ≫
                Limits.pullback.fst P.obj.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ∧
            (∀ h : Gal(Ks/L),
              fundamentalGroupMap τ Gsub G (eL h) = e (h.restrictScalars K)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
