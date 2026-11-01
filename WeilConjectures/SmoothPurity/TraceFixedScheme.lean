/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.TrfOrdinaryStage.TraceExceptionalAdmissibility
public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.Topology.Connected.Clopen

/-!
# Fixed schemes and their clopen connected components

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-trf-fixed-scheme.md`
(blueprint: def-trf-fixed-scheme), with the source clarifications recorded in the DAG.

The construction uses only the geometric map of the recorded finite-coefficient
correspondence. The diagonal is Mathlib's `pullback.diagonal`, whose projections are
identities. Components use Mathlib's `ConnectedComponents`, the quotient by equality of
connected components; the fibre over a quotient point is the maximal nonempty connected
subset it names. Component subschemes carry the entire restricted structure sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

namespace TrfCohomologicalCorrespondence

variable {F : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime]
  {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {n : ℕ}
  {hl : l ≠ F.p} {X : Over (Spec (.of F.k))}
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  {K : (trfFiniteTorFixed l E n X.left).FullSubcategory}

end TrfCohomologicalCorrespondence

/-- The geometric graph `(id_X,h)` of an endomorphism over the base. Its coefficient
map is neither needed nor requested. Source: blueprint def-trf-fixed-scheme, graph sentence
(blueprint: def-trf-fixed-scheme). -/
def trfFixedGraphMap {F : FiniteFieldDatum.{u}} (X : Over (Spec (.of F.k)))
    (h : X ⟶ X) : X.left ⟶ pullback X.hom X.hom :=
  pullback.lift (𝟙 X.left) h.left ((Category.id_comp X.hom).trans h.w.symm)

/-- The fixed scheme of an endomorphism over `s`, using just its geometric graph.
The over-category condition is precisely `h ≫ a_X = a_X`.
Source: blueprint def-trf-fixed-scheme, second display
(blueprint: def-trf-fixed-scheme). -/
def trfEndomorphismFixedScheme {F : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of F.k))) (h : X ⟶ X) : Scheme.{u} :=
  pullback (trfFixedGraphMap X h) (pullback.diagonal X.hom)

/-- The first projection of the fixed scheme of a geometric graph.
Source: blueprint def-trf-fixed-scheme, equalizer sentence
(blueprint: def-trf-fixed-scheme). -/
def trfEndomorphismFixedInclusion {F : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of F.k))) (h : X ⟶ X) : trfEndomorphismFixedScheme X h ⟶ X.left :=
  pullback.fst (trfFixedGraphMap X h) (pullback.diagonal X.hom)

/-- The first projection represents the scheme-theoretic equalizer of `h` and the identity:
composition with it is a bijection from morphisms `T → Fix(h)` onto morphisms `t : T → X`
with `t ≫ h = t`. The first conjunct says every such composite is fixed; the second says
a morphism `t` has exactly one lift if and only if it is fixed.
Source: blueprint def-trf-fixed-scheme, equalizer sentence
(blueprint: def-trf-fixed-scheme).

Proof: a map into the pullback is a pair `(t,d)` with `(t,h t) = (d,d)` in the
fibre product `X ×_s X`. Projecting with the two projections of `X ×_s X`, by
`pullback.lift_fst`, `pullback.lift_snd`, `pullback.diagonal_fst` and
`pullback.diagonal_snd`, gives `t=d` and `t ≫ h=t`; this proves the first conjunct
and the forward implication. Conversely, from the latter equality use `(t,t)` and the
two fibre-product universal properties to construct the map. Any such map has both
projections `t`, so pullback uniqueness proves uniqueness. This applies to every test
scheme, including empty ones. -/
theorem trfEndomorphismFixedScheme_equalizer {F : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of F.k))) (h : X ⟶ X) (T : Scheme.{u}) (t : T ⟶ X.left) :
    (∀ g : T ⟶ trfEndomorphismFixedScheme X h,
        (g ≫ trfEndomorphismFixedInclusion X h) ≫ h.left =
          g ≫ trfEndomorphismFixedInclusion X h) ∧
      ((∃! g : T ⟶ trfEndomorphismFixedScheme X h,
        g ≫ trfEndomorphismFixedInclusion X h = t) ↔ t ≫ h.left = t) := by
  have hproj (g : T ⟶ trfEndomorphismFixedScheme X h) :
      g ≫ trfEndomorphismFixedInclusion X h =
        g ≫ pullback.snd (trfFixedGraphMap X h) (pullback.diagonal X.hom) := by
    have hc := congrArg (fun f ↦ g ≫ f ≫ pullback.fst X.hom X.hom)
      (pullback.condition (f := trfFixedGraphMap X h) (g := pullback.diagonal X.hom))
    simpa [trfEndomorphismFixedInclusion, trfFixedGraphMap, Category.assoc] using hc
  have hfixed (g : T ⟶ trfEndomorphismFixedScheme X h) :
      (g ≫ trfEndomorphismFixedInclusion X h) ≫ h.left =
        g ≫ trfEndomorphismFixedInclusion X h := by
    have hc := congrArg (fun f ↦ g ≫ f ≫ pullback.snd X.hom X.hom)
      (pullback.condition (f := trfFixedGraphMap X h) (g := pullback.diagonal X.hom))
    simp only [Category.assoc, trfFixedGraphMap, pullback.lift_snd,
      pullback.diagonal_snd, Category.comp_id] at hc
    simpa only [trfEndomorphismFixedInclusion, trfFixedGraphMap, Category.assoc] using
      hc.trans (hproj g).symm
  refine ⟨hfixed, ?_⟩
  constructor
  · rintro ⟨g, hg, _⟩
    simpa [hg] using hfixed g
  · intro ht
    have hc : t ≫ trfFixedGraphMap X h = t ≫ pullback.diagonal X.hom := by
      apply pullback.hom_ext
      · simp [trfFixedGraphMap, Category.assoc]
      · simpa [trfFixedGraphMap, Category.assoc] using ht
    refine ⟨pullback.lift t t hc, ?_, ?_⟩
    · exact pullback.lift_fst _ _ _
    · intro g hg
      apply pullback.hom_ext
      · simpa [trfEndomorphismFixedInclusion] using hg
      · simpa using (hproj g).symm.trans hg

end WeilConjectures

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
