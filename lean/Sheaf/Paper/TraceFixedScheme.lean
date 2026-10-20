/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.TraceCohomologicalCorrespondence
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

/-- The scheme-theoretic inverse image of the diagonal along the geometric correspondence.
The coefficient map is unused. Source: blueprint def-trf-fixed-scheme, first display
(blueprint: def-trf-fixed-scheme). -/
def fixedScheme (c : TrfCohomologicalCorrespondence F l E n hl X K) : Scheme.{u} :=
  pullback c.toProduct (pullback.diagonal X.hom)

/-- The first projection `i_F : Fix(c) → C`.
Source: blueprint def-trf-fixed-scheme, first display
(blueprint: def-trf-fixed-scheme). -/
def fixedInclusion (c : TrfCohomologicalCorrespondence F l E n hl X K) :
    c.fixedScheme ⟶ c.C.left :=
  pullback.fst c.toProduct (pullback.diagonal X.hom)

/-- The second projection `d : Fix(c) → X`.
Source: blueprint def-trf-fixed-scheme, first display
(blueprint: def-trf-fixed-scheme). -/
def fixedProjection (c : TrfCohomologicalCorrespondence F l E n hl X K) :
    c.fixedScheme ⟶ X.left :=
  pullback.snd c.toProduct (pullback.diagonal X.hom)

/-- The fibre-product relation and its two projection identities.
Source: blueprint def-trf-fixed-scheme, the sentence after the first display
(blueprint: def-trf-fixed-scheme).

Proof: the defining relation is `pullback.condition`. Postcompose with each projection
of `X ×_s X`. The two projections of the diagonal are identities, and the projections
of `c.toProduct` are `c.c₁.left` and `c.c₂.left` by `pullback.lift_fst` and
`pullback.lift_snd`. These give the two displayed identities. -/
theorem fixedScheme_relations (c : TrfCohomologicalCorrespondence F l E n hl X K) :
    c.fixedInclusion ≫ c.toProduct = c.fixedProjection ≫ pullback.diagonal X.hom ∧
      c.fixedInclusion ≫ c.c₁.left = c.fixedProjection ∧
      c.fixedInclusion ≫ c.c₂.left = c.fixedProjection := by
  have hc : c.fixedInclusion ≫ c.toProduct =
      c.fixedProjection ≫ pullback.diagonal X.hom := pullback.condition
  refine ⟨hc, ?_, ?_⟩
  · simpa [toProduct, Category.assoc] using
      congrArg (fun f ↦ f ≫ pullback.fst X.hom X.hom) hc
  · simpa [toProduct, Category.assoc] using
      congrArg (fun f ↦ f ≫ pullback.snd X.hom X.hom) hc

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

/-- Finiteness of the set of all connected components, with every component clopen.
The fibre of `ConnectedComponents.mk` is a whole connected component, including its
nonemptiness; this does not select only those components which happen to be open.
Source: blueprint def-trf-fixed-scheme, component convention
(blueprint: def-trf-fixed-scheme). -/
def HasFiniteClopenConnectedComponents (F : Scheme.{u}) : Prop :=
  Finite (_root_.ConnectedComponents F) ∧
    ∀ β : _root_.ConnectedComponents F, IsClopen (ConnectedComponents.mk ⁻¹' {β})

/-- A component as an open subset, for a scheme satisfying the finite clopen convention.
Source: blueprint def-trf-fixed-scheme, final display
(blueprint: def-trf-fixed-scheme). -/
def clopenConnectedComponentOpen (F : Scheme.{u}) (hF : F.HasFiniteClopenConnectedComponents)
    (β : _root_.ConnectedComponents F) : F.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {β}, (hF.2 β).2⟩

/-- The component subscheme with its full restricted structure sheaf, without reduction.
Source: blueprint def-trf-fixed-scheme, final display
(blueprint: def-trf-fixed-scheme). -/
def clopenConnectedComponentScheme (F : Scheme.{u}) (hF : F.HasFiniteClopenConnectedComponents)
    (β : _root_.ConnectedComponents F) : Scheme.{u} :=
  (F.clopenConnectedComponentOpen hF β).toScheme

/-- The canonical map from the coproduct of component subschemes to the original scheme.
Source: blueprint def-trf-fixed-scheme, final display
(blueprint: def-trf-fixed-scheme). -/
def clopenConnectedComponentsMap (F : Scheme.{u}) (hF : F.HasFiniteClopenConnectedComponents) :
    (∐ F.clopenConnectedComponentScheme hF) ⟶ F :=
  Sigma.desc (fun β ↦ (F.clopenConnectedComponentOpen hF β).ι)

/-- The canonical component map is an isomorphism, including for the empty scheme.
Source: blueprint def-trf-fixed-scheme, final display; the DAG's scheme coproduct and
morphism-gluing dependencies (blueprint: def-trf-fixed-scheme).

Proof: the fibres of the component quotient partition the underlying space. They are
open by `hF`, hence form an open cover by the indicated open subschemes, with disjoint
pairwise intersections. On each member use the corresponding coproduct inclusion to
map to the coproduct. On intersections the maps agree because intersections of
distinct components are empty, while equal indices give the same map. The morphism
gluing theorem gives an inverse. Its composites restrict to identities on every cover
member, so cover extensionality and the coproduct universal property give both inverse
identities. For the empty index type the same argument is the initial-scheme identity.
Finiteness is the stated convention; no reduction of the structure sheaf occurs. -/
theorem isIso_clopenConnectedComponentsMap (F : Scheme.{u})
    (hF : F.HasFiniteClopenConnectedComponents) : IsIso (F.clopenConnectedComponentsMap hF) := by
  apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk F (fun β ↦ (F.clopenConnectedComponentOpen hF β).ι))).mp
  apply nonempty_isColimit_cofanMk_of
  · simp only [Scheme.Opens.opensRange_ι]
    change ⨆ β, F.clopenConnectedComponentOpen hF β = ⊤
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  · intro β γ hβγ
    simp only [Scheme.Opens.opensRange_ι]
    change Disjoint (F.clopenConnectedComponentOpen hF β)
      (F.clopenConnectedComponentOpen hF γ)
    exact TopologicalSpace.Opens.coe_disjoint.mp
      ((Set.disjoint_singleton.mpr hβγ).preimage ConnectedComponents.mk)

/-- The canonical identification of the component coproduct with the scheme. Its inverse
is uniquely determined by the canonical map, rather than chosen from arbitrary data.
Source: blueprint def-trf-fixed-scheme, final display
(blueprint: def-trf-fixed-scheme). -/
def clopenConnectedComponentsIso (F : Scheme.{u}) (hF : F.HasFiniteClopenConnectedComponents) :
    (∐ F.clopenConnectedComponentScheme hF) ≅ F :=
  @asIso _ _ _ _ (F.clopenConnectedComponentsMap hF) (F.isIso_clopenConnectedComponentsMap hF)

end AlgebraicGeometry.Scheme
