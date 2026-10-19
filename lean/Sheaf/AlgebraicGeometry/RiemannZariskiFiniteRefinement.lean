/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.Topology.Maps.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Topology.Spectral.Basic
import Sheaf.Topology.SpectralDirectedLimit
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.RingTheory.ValuationAlgebraicHeight
import Sheaf.TraceFormula.AbhyankarFiniteTypeFieldHeight

/-!
# Valuation neighbourhoods and common finite Riemann--Zariski refinement

Source: Temkin, *Stable modification*, §3.2, pp. 15--17, and §2.1, pp. 7--8
(blueprint: lem-trf-riemann-zariski-finite-refinement).

The space is the actual type of compatible families in all proper models, with
its initial topology. The auxiliary structures unpack notions introduced in this
same node; none chooses an unspecified space, map, topology, or proposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.RiemannZariski

/-- A generic factorization of `η` through an integral scheme. The image of the
unique point of `Spec L` is required to be generic. Source: Temkin §3.2, opening
paragraph, p. 15 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
structure GenericScheme (T : Scheme.{u}) (L : Type u) [Field L]
    (η : Spec (.of L) ⟶ T) where
  X : Scheme.{u}
  [integral : IsIntegral X]
  map : X ⟶ T
  generic : Spec (.of L) ⟶ X
  generic_point : generic (IsLocalRing.closedPoint L) = genericPoint X
  fac : generic ≫ map = η

attribute [instance] GenericScheme.integral

/-- An `L`-model is a proper generic factorization. Source: Temkin §3.2, opening
paragraph, p. 15 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
structure Model (T : Scheme.{u}) (L : Type u) [Field L]
    (η : Spec (.of L) ⟶ T) extends GenericScheme T L η where
  [proper : IsProper map]

attribute [instance] Model.proper

/-- An `L`-quasi-model is a separated finite-type generic factorization.
Source: Temkin §3.2, opening paragraph, p. 15
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
structure QuasiModel (T : Scheme.{u}) (L : Type u) [Field L]
    (η : Spec (.of L) ⟶ T) extends GenericScheme T L η where
  [separated : IsSeparated map]
  [locally_finite_type : LocallyOfFiniteType map]
  [quasi_compact : QuasiCompact map]

attribute [instance] QuasiModel.separated QuasiModel.locally_finite_type QuasiModel.quasi_compact

variable {T : Scheme.{u}} {L : Type u} [Field L] {η : Spec (.of L) ⟶ T}

/-- Every model is a quasi-model, using the existing properness instances.
Source: Temkin §3.2, p. 15 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def Model.toQuasiModel (M : Model T L η) : QuasiModel T L η where
  toGenericScheme := M.toGenericScheme

/-- A morphism of models is a `T`-morphism respecting the specified `Spec L` maps.
Source: Temkin §3.2, p. 15 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
structure ModelHom (M N : Model T L η) where
  hom : M.X ⟶ N.X
  over : hom ≫ N.map = M.map
  generic : M.generic ≫ hom = N.generic

/-- The points of `RZ_L(T)` are families of points in **all** proper `L`-models,
compatible with every model morphism. Using all models avoids a skeleton choice.
Source: Temkin §3.2, p. 15 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def Point (T : Scheme.{u}) (L : Type u) [Field L] (η : Spec (.of L) ⟶ T) :=
  {x : (M : Model T L η) → M.X //
    ∀ (M N : Model T L η) (f : ModelHom M N), f.hom (x M) = x N}

/-- The limit topology: the coarsest topology making every model projection continuous.
Source: Temkin §3.2, definition of `RZ_K(S)`, p. 15
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
instance pointTopologicalSpace : TopologicalSpace (Point T L η) :=
  ⨅ M : Model T L η, TopologicalSpace.induced (fun x : Point T L η ↦ x.1 M) inferInstance

/-- The embedding of a model's function field into `L`, obtained from the generic
map on stalks and the specified equality of generic points. It is not chosen.
Source: Temkin §3.2, opening paragraph, p. 15
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def GenericScheme.fieldEmbedding (G : GenericScheme T L η) : G.X.functionField →+* L :=
  ((G.X.presheaf.stalkCongr (.of_eq G.generic_point.symm)).hom ≫
    Scheme.stalkClosedPointTo G.generic).hom

/-- A finite separable function-field extension inside the specified `L`: the
embedding into `L` must extend `ι`. Source: Temkin §3.2, opening paragraph, p. 15
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def GenericScheme.IsFiniteSeparableOver (G : GenericScheme T L η)
    {K : Type u} [Field K] (ι : K →+* L) : Prop :=
  ∃ φ : K →+* G.X.functionField,
    G.fieldEmbedding.comp φ = ι ∧ φ.Finite ∧
      @Algebra.IsSeparable K G.X.functionField _ _ φ.toAlgebra

/-- A centred valuation point remembers both a valuation **subring of `L`** and
its morphism to `T`. The map from `Spec L` is the canonical inclusion on spectra.
Source: Temkin §3.2, Corollary 3.2.5, p. 16
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
structure ValuationPoint (T : Scheme.{u}) (L : Type u) [Field L]
    (η : Spec (.of L) ⟶ T) where
  V : ValuationSubring L
  centre : Spec (.of V) ⟶ T
  fac : Spec.map (CommRingCat.ofHom V.subtype) ≫ centre = η

/-- Characterization of the canonical valuation-point correspondence by closed-point
images of the proper valuative lifts in every model. Source: Temkin Corollary 3.2.5,
p. 16 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def Corresponds (x : Point T L η) (v : ValuationPoint T L η) : Prop :=
  ∀ M : Model T L η, ∃ l : Spec (.of v.V) ⟶ M.X,
    l ≫ M.map = v.centre ∧ Spec.map (CommRingCat.ofHom v.V.subtype) ≫ l = M.generic ∧
      l (IsLocalRing.closedPoint v.V) = x.1 M

/-- A valuation point lifts to a quasi-model exactly when there is a lift of its
centre respecting the specified generic maps. Source: Temkin §3.2, Corollary 3.2.7,
p. 17 (blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def ValuationPoint.LiftsTo (v : ValuationPoint T L η) (U : QuasiModel T L η) : Prop :=
  ∃ l : Spec (.of v.V) ⟶ U.X,
    l ≫ U.map = v.centre ∧ Spec.map (CommRingCat.ofHom v.V.subtype) ≫ l = U.generic

/-- Composition of a valuation centre on `U` with `U → T`, retaining the same
valuation subring and canonical generic inclusion. Source: Temkin §3.2, p. 16
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
def ValuationPoint.push (U : QuasiModel T L η) (v : ValuationPoint U.X L U.generic) :
    ValuationPoint T L η where
  V := v.V
  centre := v.centre ≫ U.map
  fac := by rw [← Category.assoc, v.fac, U.fac]

/-- A common refinement has an actual proper `L`-model and actual opens in it,
with proper dominant `T`-maps to the given quasi-models. All generic maps agree.
The function-field inclusions are finite separable inside `L`.
Source: Temkin Proposition 3.2.6, pp. 16--17
(blueprint: lem-trf-riemann-zariski-finite-refinement). -/
structure FiniteRefinement {I : Type w} (U : I → QuasiModel T L η) where
  model : Model T L η
  W : I → model.X.Opens
  map : ∀ i : I, (W i).toScheme ⟶ (U i).X
  [proper : ∀ i : I, IsProper (map i)]
  [dominant : ∀ i : I, IsDominant (map i)]
  over : ∀ i : I, map i ≫ (U i).map = (W i).ι ≫ model.map
  generic : ∀ i : I, Spec (.of L) ⟶ (W i).toScheme
  generic_model : ∀ i : I, generic i ≫ (W i).ι = model.generic
  generic_quasi_model : ∀ i : I, generic i ≫ map i = (U i).generic
  finite_separable : ∀ i : I,
    model.toGenericScheme.IsFiniteSeparableOver (U i).toGenericScheme.fieldEmbedding

/--
Source: Temkin, *Stable modification*, §3.2, Propositions 3.2.1 and 3.2.6,
Corollaries 3.2.4--3.2.7, pp. 15--17; §2.1, pp. 7--8
(blueprint: lem-trf-riemann-zariski-finite-refinement).

Proof, following the twelve steps of the node:
1. A nonempty affine chart has a finitely generated coordinate domain with
   fraction field in the separable algebraic extension `L/k(T)`. Finitely many
   generators give a finite separable extension. The same argument makes `k(T)`
   finitely generated over its prime field.
2. Finite-type schemes over `T` are Noetherian and qcqs, by
   `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-locally-noetherian-quasi-separated`. The reduced generic closure
   in a proper scheme is integral and proper, using
   `lem-weil-pbc-reduced-induced-closed-subscheme` and
   `lem-weil-pbc-closed-immersion-proper`.
3. Reduced generic closures in products give common model refinements, using
   `lem-weil-pbc-proper-base-change` and `lem-weil-pbc-proper-composition`.
   Separatedness makes compatible maps unique. Finite affine presentations
   provide a set of representatives for this cofiltered system.
4. The models are spectral (`lem-weil-pbc-qcqs-scheme-spectral`), and transition
   maps are proper (`lemma-nagata-proper-to-separated-target`). Apply
   `lem-weil-pbc-spectral-directed-limit-spectral` to obtain quasi-compactness
   for precisely the initial topology used here.
5. For a compatible point family take the union in `L` of its model local
   rings. These local inclusions form a directed system and their union is local;
   its morphism to `T` has the specified generic restriction.
6. For each nonzero `f` in `L`, take the reduced closure of its graph in
   `T × P¹_ℤ`. Properness follows from
   `lemma-nagata-projective-space-base-change-proper`. The two affine charts
   (`def-nagata-affine-proj`, `lemma-nagata-relative-affine-space-open-immersion`)
   show that `f` or its inverse lies in the union, making it a valuation ring
   with fraction field `L`.
7. Conversely `lemma-nagata-proper-separated-valuation-extension` supplies
   unique lifts to every proper model; their closed-point images are compatible.
   `lemma-nagata-valuation-intersection` identifies the union of local rings with
   the original valuation ring. This gives the characterized bijections, with
   their actual centre maps even when `T` is nonseparated.
8. Restriction to `k(T)` preserves height
   (`lem-trf-valuation-algebraic-height`), and the Abhyankar bound for finitely
   generated fields (`lem-trf-abhyankar-finite-type-field-height`) bounds strict
   prime chains by the finite transcendence degree plus one.
9. Compactify a quasi-model and take its reduced generic closure
   (`thm-nagata-compactification`). A valuation lift is unique
   (`lemma-nagata-separated-valuation-lift-unique`), and exists exactly when its
   closed point in that proper compactification lies in the open quasi-model.
10. Compactify further models over the quasi-model to see that its inverse-limit
    topology agrees with this open subspace topology. Proper base change gives
    the converse continuity. Thus the characterized injections are open embeddings.
11. The reduced generic closure in the finite product of the compactifications
    is a common model. Inverse images of the original opens give `W_i`; proper
    base change makes their maps proper, and the generic maps give dominance and
    finite separable field extensions. For an empty family take the identity model `T`.
12. A point of the common model has a dominating valuation in its function field
    (`lemma-nagata-local-domain-valuation-dominates`), extended to `L` by
    `lemma-nagata-valuation-ring-extension`. A neighbourhood cover provides a lift
    to some `U_i`; uniqueness of its proper extension puts the point in `W_i`.
    The image description and the bijection also give the arbitrary-family
    valuation-lift covering clause.
-/
theorem finite_refinement
    (T : Scheme.{u}) [IsIntegral T]
    (t : T ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType t] [QuasiCompact t]
    (L : Type u) [Field L] [Algebra T.functionField L] [IsSepClosure T.functionField L] :
    (∀ U : QuasiModel T L
      (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
        T.fromSpecStalk (genericPoint T)),
      U.toGenericScheme.IsFiniteSeparableOver (algebraMap T.functionField L)) ∧
    CompactSpace (Point T L
      (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
        T.fromSpecStalk (genericPoint T))) ∧
    ∃ e : Point T L
        (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
          T.fromSpecStalk (genericPoint T)) ≃
      ValuationPoint T L
        (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
          T.fromSpecStalk (genericPoint T)),
      (∀ x, Corresponds x (e x)) ∧
      (∀ v : ValuationPoint T L
        (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
          T.fromSpecStalk (genericPoint T)),
        ∃ N : ℕ, ∀ (n : ℕ) (p : Fin (n + 1) → PrimeSpectrum v.V),
          StrictMono p → n ≤ N) ∧
      ∃ (eU : ∀ U : QuasiModel T L
          (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T)),
          Point U.X L U.generic ≃ ValuationPoint U.X L U.generic)
        (j : ∀ U : QuasiModel T L
          (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T)),
          Point U.X L U.generic → Point T L
            (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
              T.fromSpecStalk (genericPoint T))),
        (∀ U x, Corresponds x (eU U x)) ∧
        (∀ U, IsOpenEmbedding (j U)) ∧
        (∀ U x, e (j U x) = ValuationPoint.push U (eU U x)) ∧
        (∀ U x, x ∈ Set.range (j U) ↔ (e x).LiftsTo U) ∧
        (∀ (I : Type w) (U : I → QuasiModel T L
            (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
              T.fromSpecStalk (genericPoint T))),
          (∀ v, ∃ i : I, ValuationPoint.LiftsTo v (U i)) → ∀ x, ∃ i : I, x ∈ Set.range (j (U i))) ∧
        (∀ (I : Type w) [Finite I] (U : I → QuasiModel T L
            (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
              T.fromSpecStalk (genericPoint T))),
          ∃ r : FiniteRefinement U,
            (∀ x, ∃ i : I, x ∈ Set.range (j (U i))) →
              ∀ y : r.model.X, ∃ i : I, y ∈ r.W i) := by
  sorry

end AlgebraicGeometry.RiemannZariski
