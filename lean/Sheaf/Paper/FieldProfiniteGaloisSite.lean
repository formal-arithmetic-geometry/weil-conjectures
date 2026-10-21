/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.Topology.FilteredSpectrumTopologicalLimit
import Sheaf.FieldTheory.AlgebraicSeparableSmooth
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The pro-etale field site as profinite Galois sets

Source: Bhatt--Scholze, Examples 4.1.9--4.1.10, pp. 27--28, and Definition 4.1.1.
(blueprint: lem-sfb-field-profinite-galois-site).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.FieldGaloisSite

/-- The qcqs full inclusion followed by forgetting to schemes over the base.
Source: Bhatt--Scholze, Example 4.1.10.
(blueprint: lem-sfb-field-profinite-galois-site). -/
abbrev qcqsOver (X : Scheme.{u}) : Scheme.ProEt.Qcqs X ⥤ Over X :=
  Scheme.ProEt.qcqsInclusion X ⋙ Scheme.ProEt.forget X

/-- The recorded relative test scheme functor, retaining its structure map.
Source: Bhatt--Scholze, Example 4.1.9; `profinite_test_object_functor`.
(blueprint: lem-sfb-field-profinite-galois-site). -/
abbrev testOver (X : Scheme.{u}) : Profinite.{u} ⥤ Over X :=
  profiniteToProEtOf X ⋙ Scheme.ProEt.forget X

/-- The profinite set with the trivial continuous action, functorially in the set.
Source: Bhatt--Scholze, Examples 4.1.9--4.1.10.
(blueprint: lem-sfb-field-profinite-galois-site). -/
def trivial (G : Type u) [Group G] [TopologicalSpace G] :
    Profinite.{u} ⥤ ContAction Profinite.{u} G where
  obj P := ⟨Action.trivial G P, ⟨continuous_snd⟩⟩
  map f := ObjectProperty.homMk
    { hom := f
      comm := fun _ ↦ by simp [Action.trivial] }

/-- The product `G × P`, with left translation on the first factor and trivial second factor.
Source: Bhatt--Scholze, Example 4.1.10, the geometric-point Galois torsor.
(blueprint: lem-sfb-field-profinite-galois-site). -/
def regular (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Profinite.{u} ⥤ ContAction Profinite.{u} G where
  obj P :=
    ⟨{ V := Profinite.of (G × P)
       ρ :=
        { toFun := fun g ↦ CompHausLike.ofHom _
            ⟨fun x ↦ (g * x.1, x.2), by fun_prop⟩
          map_one' := by
            apply ConcreteCategory.hom_ext
            intro x
            exact Prod.ext (one_mul x.1) rfl
          map_mul' := by
            intro g h
            apply ConcreteCategory.hom_ext
            intro x
            exact Prod.ext (mul_assoc g h x.1) rfl } },
     ⟨by
       change Continuous (fun x : G × (G × P) ↦ (x.1 * x.2.1, x.2.2))
       fun_prop⟩⟩
  map f := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun x ↦ (x.1, f x.2), by fun_prop⟩
      comm := fun _ ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        rfl }
  map_id P := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp {P Q R} f g := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- The natural equivariant projection `(g,p) ↦ p`.
Source: Bhatt--Scholze, Examples 4.1.9--4.1.10.
(blueprint: lem-sfb-field-profinite-galois-site). -/
def projection (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    regular G ⟶ trivial G where
  app P := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun x ↦ x.2, continuous_snd⟩
      comm := fun _ ↦ by ext x; rfl }
  naturality {P Q} f := by ext x; rfl

/-- The structural map between two normalized test functors. Its definition uses the actual
projection `G × P → P`; the theorem below pins it to the scheme map induced by the base map.
Source: Bhatt--Scholze, Examples 4.1.9--4.1.10.
(blueprint: lem-sfb-field-profinite-galois-site). -/
def normalizedArrow (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (E : Scheme.ProEt.Qcqs (Spec (.of k)) ≌ ContAction Profinite.{u} (Ω ≃ₐ[k] Ω))
    (a : trivial (Ω ≃ₐ[k] Ω) ⋙ E.inverse ⋙ qcqsOver (Spec (.of k)) ≅
      testOver (Spec (.of k)))
    (b : regular (Ω ≃ₐ[k] Ω) ⋙ E.inverse ⋙ qcqsOver (Spec (.of k)) ≅
      testOver (Spec (.of Ω)) ⋙ Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) :
    testOver (Spec (.of Ω)) ⋙ Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶
      testOver (Spec (.of k)) :=
  b.inv ≫ Functor.whiskerRight (projection (Ω ≃ₐ[k] Ω))
    (E.inverse ⋙ qcqsOver (Spec (.of k))) ≫ a.hom

/-- The qcqs pro-etale site of a field is the site of continuous profinite Galois sets.

The first clause identifies covering sieves with the existence of a finite jointly surjective
family in the sieve after applying the equivalence. This is precisely the topology generated
by the covering families in the node. The second clause is density with the induced topology.
The third clause gives the analogous topological equivalence over the separable closure.
The fourth is the natural comparison of geometric base change with forgetting the action.
The final two natural isomorphisms identify `s[P]` and `bar s[P]` over `s` with the trivial
and regular actions. The last equation says their projection preserves the `Spec LC(P,ℤ)`
coordinate. Since it is already an arrow over `s`, pullback uniqueness identifies it with
the canonical structural map `bar s[P] → s[P]`.

Source: Bhatt--Scholze, Examples 4.1.9--4.1.10, pp. 27--28; Definition 4.1.1.
(blueprint: lem-sfb-field-profinite-galois-site).

Proof plan, following the eight steps of the DAG:
1. A weakly etale field algebra is a union of finite etale subalgebras. All its primes are
maximal. Qcqs zero-dimensional schemes are affine, so this describes every qcqs object.
2. Finite etale field algebras correspond contravariantly to finite continuous Galois sets
by embeddings into Ω, acted on by left composition. Products treat disconnected objects.
3. Take inverse limits of these finite fibres. The Krull group is profinite. Inclusions of
finite subalgebras give surjective fibre maps; handle the zero algebra by the empty fibre.
4. Continuous equivariant fibre maps factor through finite stages, by finite presentation
and profinite function factorization. Surjective projections descend equivariance and
ensure uniqueness; the empty fibres give exactly the exceptional empty Hom sets.
5. Invariant finite clopen partitions present every continuous profinite action. The colimit
of their finite etale algebras is ind-etale and has the required fibre and topology.
6. Tensoring with Ω identifies the base-changed fibre with the same profinite set without
its action. Over Ω, every residue field is Ω; finite splitting gives the topology and
naturality of this identification.
7. Finite joint surjectivity of geometric fibres is equivalent to the fpqc covering test
for affine objects. Affine open coverings of arbitrary site objects give the dense subsite.
8. At finite parameters, `s[P]` has trivial fibre P and `bar s[P]` has fibre G × P.
A k-embedding Ω → Ω is an automorphism by restriction to finite Galois subextensions.
Pass to the finite-quotient limits. Precomposition with k → Ω forgets the G coordinate,
and parameter maps preserve that coordinate, proving the two natural identifications and
the projection equation. The empty parameter gives the empty scheme on both sides. -/
theorem field_profinite_galois_site (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] :
    ∃ (E : Scheme.ProEt.Qcqs (Spec (.of k)) ≌ ContAction Profinite.{u} (Ω ≃ₐ[k] Ω))
      (Eb : Scheme.ProEt.Qcqs (Spec (.of Ω)) ≌ Profinite.{u}),
      (∀ (U : Scheme.ProEt.Qcqs (Spec (.of k))) (R : Sieve U),
        R ∈ (Scheme.ProEt.qcqsInclusion (Spec (.of k))).inducedTopology
          (Scheme.ProEt.topology (Spec (.of k))) U ↔
        ∃ (n : ℕ) (V : Fin n → Scheme.ProEt.Qcqs (Spec (.of k)))
          (f : ∀ i : Fin n, V i ⟶ U),
          (∀ i : Fin n, R (f i)) ∧
          ∀ x : (E.functor.obj U).obj.V, ∃ (i : Fin n) (y : (E.functor.obj (V i)).obj.V),
            (E.functor.map (f i)).hom.hom y = x) ∧
      (Scheme.ProEt.qcqsInclusion (Spec (.of k))).IsDenseSubsite
        ((Scheme.ProEt.qcqsInclusion (Spec (.of k))).inducedTopology
          (Scheme.ProEt.topology (Spec (.of k)))) (Scheme.ProEt.topology (Spec (.of k))) ∧
      (Scheme.ProEt.qcqsInclusion (Spec (.of Ω))).inducedTopology
          (Scheme.ProEt.topology (Spec (.of Ω))) =
        Eb.functor.inducedTopology (coherentTopology Profinite.{u}) ∧
      Nonempty (E.functor ⋙ forget₂ (ContAction Profinite.{u} (Ω ≃ₐ[k] Ω)) Profinite.{u} ⋙
        Eb.inverse ⋙ qcqsOver (Spec (.of Ω)) ≅
        qcqsOver (Spec (.of k)) ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ∧
      ∃ (a : trivial (Ω ≃ₐ[k] Ω) ⋙ E.inverse ⋙ qcqsOver (Spec (.of k)) ≅
          testOver (Spec (.of k)))
        (b : regular (Ω ≃ₐ[k] Ω) ⋙ E.inverse ⋙ qcqsOver (Spec (.of k)) ≅
          testOver (Spec (.of Ω)) ⋙ Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))),
        ∀ P : Profinite.{u}, ((normalizedArrow k Ω E a b).app P).left ≫
          pullback.fst ((profiniteToProEt.obj P).hom) (toSpecZ (Spec (.of k))) =
          pullback.fst ((profiniteToProEt.obj P).hom) (toSpecZ (Spec (.of Ω))) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldGaloisSite
