/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import Sheaf.Paper.StrictHenselizationPointEvaluationImage
import Sheaf.Paper.StrictHenselizationPointEvaluationProperties
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Inert étale comparison of finite scheme and log quotients

Source: Stacks Project, Tag 0DT9; ILO VIII 5.3.6--5.3.7 and Proposition 5.4.2,
printed pp.124--127 (blueprint: lem-per-inert-etale-quotient-comparison).

The scheme assertion uses no log or tameness assumption. The log assertion uses
actual invariant direct images, without assuming that the quotient log structures
are fs. All comparison maps are normalized by their two projections.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The locus of equality of geometric stabilizers; the point condition quantifies
all algebraically closed lifts of an underlying point. Source: ILO VIII 5.3.6
(blueprint: lem-per-inert-etale-quotient-comparison). -/
def inertEtaleLocus {G : Type v} [Group G] {V U : Scheme.{u}}
    (aV : G →* Aut V) (aU : G →* Aut U) (h : V ⟶ U) : Set V :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V),
    t default = x → ∀ g : G,
      t ≫ (aV g).hom = t ↔ (t ≫ h) ≫ (aU g).hom = t ≫ h}

/-- The inert locus is open and invariant. Source: ILO VIII 5.3.6--5.3.7 and
Stacks Tag 0DT9 (blueprint: lem-per-inert-etale-quotient-comparison).

Proof (DAG step 1): For each g, separatedness makes the fixed loci closed.
Inside the inverse image of U^g, the inclusion V^g is the pullback of the
relative diagonal of h. This diagonal is open by def-weil-unramified-morphism
and closed by separatedness. The complement is closed in V. Remove the finite
union of these bad loci. Conjugation permutes them, proving invariance. -/
theorem isOpen_inertEtaleLocus {G : Type v} [Group G] [Finite G]
    {V U : Scheme.{u}} [V.IsSeparated] [U.IsSeparated]
    [IsLocallyNoetherian V] [IsLocallyNoetherian U]
    (aV : G →* Aut V) (aU : G →* Aut U) (h : V ⟶ U) [Etale h]
    (hequiv : ∀ g : G, (aV g).hom ≫ h = h ≫ (aU g).hom)
    (haV : ∀ x : V, ∃ W : V.affineOpens,
      x ∈ W.1 ∧ ∀ (g : G) (y : V), (aV g).hom y ∈ W.1 ↔ y ∈ W.1)
    (haU : ∀ x : U, ∃ W : U.affineOpens,
      x ∈ W.1 ∧ ∀ (g : G) (y : U), (aU g).hom y ∈ W.1 ↔ y ∈ W.1) :
    IsOpen (inertEtaleLocus aV aU h) ∧
      ∀ (g : G) (x : V),
        (aV g).hom x ∈ inertEtaleLocus aV aU h ↔ x ∈ inertEtaleLocus aV aU h := by
  sorry

/-- An inert equivariant étale map descends to an étale quotient map and its
canonical comparison is an equivariant isomorphism. Geometric orbit fibres are
stated explicitly, in addition to the underlying orbit quotient predicate.
Source: Stacks Tag 0DT9 (blueprint: lem-per-inert-etale-quotient-comparison).

Proof (DAG steps 2--11): On finite affine quotient charts write C=A^G and D=B^G.
Finite presentation follows from lem-weil-pbc-lfp-affine-opens-finite-presentation.
Use lem-weil-pbc-flat-tensor-exact on the finite family of differences g-1 to
commute invariants with flat base change. Use def-weil-pbc-strict-henselization-limit,
lem-weil-pbc-strict-henselization-local-structure, the underlying-module and flat
filtered-colimit lemmas, and the two point-evaluation lemmas to pass to the strict
henselian local base H with its specified closed geometric point. Decompose the
finite H-algebra by lem-weil-pbc-finite-over-henselian-local-product and
lem-weil-pbc-finite-affine-coproduct-spectrum. The sepclosed finite-extension
unique-embedding lemma identifies the component stabilizer with geometric inertia.
Use lem-exc-etale-lift-sepclosed-base, lem-weil-pbc-henselian-etale-retraction and
lem-weil-pbc-etale-section-clopen-immersion to get the unique clopen section.
Inertness makes it stabilizer-invariant; its disjoint translates give an equivariant
copy of the whole target. Its invariant idempotent splits D_H with one factor H.
Descend this idempotent, all relations, and both inverse identities using
lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise. The resulting pointed
étale covers prove étaleness by lem-trf-etale-descent-through-source-cover.
Descend the canonical comparison by lem-weil-pbc-fpqc-descend-isomorphism.
The inverse is unique, so the affine comparisons glue and are equivariant. -/
theorem inert_etale_quotient_comparison {G : Type v} [Group G] [Finite G]
    {V U VQ UQ : Scheme.{u}} [V.IsSeparated] [U.IsSeparated]
    [IsLocallyNoetherian V] [IsLocallyNoetherian U]
    (aV : G →* Aut V) (aU : G →* Aut U) (h : V ⟶ U) [Etale h]
    (hequiv : ∀ g : G, (aV g).hom ≫ h = h ≫ (aU g).hom)
    (haV : ∀ x : V, ∃ W : V.affineOpens,
      x ∈ W.1 ∧ ∀ (g : G) (y : V), (aV g).hom y ∈ W.1 ↔ y ∈ W.1)
    (haU : ∀ x : U, ∃ W : U.affineOpens,
      x ∈ W.1 ∧ ∀ (g : G) (y : U), (aU g).hom y ∈ W.1 ↔ y ∈ W.1)
    (hinert : ∀ x : V, x ∈ inertEtaleLocus aV aU h)
    (qV : V ⟶ VQ) (qU : U ⟶ UQ)
    (hqV : IsAdmissibleFiniteSchemeQuotient aV qV)
    (hqU : IsAdmissibleFiniteSchemeQuotient aU qU)
    (horbitV : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ V), s ≫ qV = t ≫ qV ↔ ∃ g : G, s ≫ (aV g).hom = t)
    (horbitU : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ U), s ≫ qU = t ≫ qU ↔ ∃ g : G, s ≫ (aU g).hom = t) :
    ∃ hb : VQ ⟶ UQ, ∃ hc : h ≫ qU = qV ≫ hb,
      Etale hb ∧ IsIso (pullback.lift h qV hc) ∧
        (∀ g : G, (aV g).hom ≫ pullback.lift h qV hc =
          pullback.lift h qV hc ≫
            pullback.lift (pullback.fst qU hb ≫ (aU g).hom) (pullback.snd qU hb)
              (by rw [Category.assoc, hqU.2.2.1 g]; exact pullback.condition)) ∧
        ∀ hb' : VQ ⟶ UQ, qV ≫ hb' = h ≫ qU → hb' = hb := by
  sorry

/-- Strict equivariant comparison descends to the actual invariant log sheaves.
The last equality characterizes the descended log map by pullback of sections;
no arbitrary isomorphism between log structures is substituted.
Source: ILO VIII Proposition 5.4.2, pp.126--127, equal-group étale case
(blueprint: lem-per-inert-etale-quotient-comparison).

Proof (DAG steps 12--13): By lem-weil-pbc-etale-inverse-image-algebraic-structures
and lem-weil-pbc-etale-localization-functor-adjoint, inverse image along an étale
map is restriction, also for monoid sheaves. The graph test object gives the
terminal value in the inverse-image colimit. The structure ring and units restrict
identically. Apply the scheme comparison to identify the two pullback test schemes.
Strictness of h identifies their log sections equivariantly. Taking invariants and
using dU.image and dV.image gives the canonical bijection on quotient log sections,
compatible with every restriction and structural map. This is strictness of the
induced log map; the normalization equation is precisely that construction. -/
theorem inert_etale_log_quotient_strict
    {G : Type v} [Group G] [Finite G] {V U : FineSaturatedLogScheme.{u}}
    {VQ UQ : Scheme.{u}} (aV : FSLogGroupAction G V) (aU : FSLogGroupAction G U)
    (h : EtaleLogHom V U) [Etale h.base] (hstrict : h.toLogMap.IsStrictEtale)
    (hequiv : aV.IsEquivariant aU h) (htV : aV.IsVeryTame) (htU : aU.IsVeryTame)
    (qV : V.scheme ⟶ VQ) (qU : U.scheme ⟶ UQ) (hb : VQ ⟶ UQ) [Etale hb]
    (hc : h.base ≫ qU = qV ≫ hb) (hcart : IsIso (pullback.lift h.base qV hc))
    (hqV : IsAdmissibleFiniteSchemeQuotient aV.baseAction qV)
    (hqU : IsAdmissibleFiniteSchemeQuotient aU.baseAction qU)
    (NV : EtaleLogStructure VQ) (NU : EtaleLogStructure UQ)
    (dV : aV.InvariantDirectImage qV NV) (dU : aU.InvariantDirectImage qU NU) :
    ∃ H : NV.HomAlong NU hb, H.IsStrictEtale ∧
      ∀ (E : UQ.Etale) (F : VQ.Etale) (k : F.left ⟶ E.left)
        (hk : k ≫ E.hom = F.hom ≫ hb)
        (l : (logInvariantTest qV F).left ⟶ (logInvariantTest qU E).left)
        (hl : l ≫ (logInvariantTest qU E).hom =
          (logInvariantTest qV F).hom ≫ h.base),
        l ≫ pullback.fst E.hom qU = pullback.fst F.hom qV ≫ k →
          ∀ s : NU.monoidSheaf.obj.obj (op E),
            dV.pullbackMap F (H.sectionMap E F k hk s) =
              h.sectionMap (logInvariantTest qU E) (logInvariantTest qV F) l hl
                (dU.pullbackMap E s) := by
  sorry

/-- Canonical comparisons commute with arbitrary quotient base change, hence with
quotient opens and pointed étale neighbourhoods. Source: Stacks Tag 0DT9;
ILO VIII 5.3.7 (blueprint: lem-per-inert-etale-quotient-comparison).

Proof (DAG step 14): Both maps have the same three projections, namely h on the
original scheme, the quotient projection, and the base-change projection.
Apply the fibre-product universal property (def-pc-fibre-product) twice. -/
theorem inert_etale_comparison_baseChange {V U VQ UQ T : Scheme.{u}}
    (h : V ⟶ U) (qV : V ⟶ VQ) (qU : U ⟶ UQ) (hb : VQ ⟶ UQ)
    (hc : h ≫ qU = qV ≫ hb) (t : T ⟶ VQ) :
    pullback.map qV t (pullback.snd qU hb) t
        (pullback.lift h qV hc) (𝟙 T) (𝟙 VQ) (by simp) (by simp) ≫
      pullback.lift (pullback.fst (pullback.snd qU hb) t ≫ pullback.fst qU hb)
        (pullback.snd (pullback.snd qU hb) t)
        (by
          rw [Category.assoc, pullback.condition, ← Category.assoc,
            pullback.condition, Category.assoc]) =
    pullback.lift (f := qU) (g := t ≫ hb)
      (pullback.fst qV t ≫ h) (pullback.snd qV t)
      (by rw [Category.assoc, hc, ← Category.assoc, pullback.condition, Category.assoc]) := by
  sorry

/-- Canonical comparisons compose by their projection normalization. Source: Stacks
Tag 0DT9; ILO VIII 5.4.2 (blueprint: lem-per-inert-etale-quotient-comparison).

Proof (DAG step 14): For composable inert maps, equality of stabilizers composes.
For the comparisons, both projections are respectively the composite scheme map
and the quotient map. Their universal characterization gives the stated equality.
The section normalization of the log comparison gives the identical composition
law on invariant log sections, since restriction of sections composes. -/
theorem inert_etale_comparison_comp {W V U WQ VQ UQ : Scheme.{u}}
    (k : W ⟶ V) (h : V ⟶ U) (qW : W ⟶ WQ) (qV : V ⟶ VQ) (qU : U ⟶ UQ)
    (kb : WQ ⟶ VQ) (hb : VQ ⟶ UQ)
    (kc : k ≫ qV = qW ≫ kb) (hc : h ≫ qU = qV ≫ hb) :
    pullback.lift k qW kc ≫
      pullback.lift (pullback.fst qV kb ≫ h) (pullback.snd qV kb)
        (by rw [Category.assoc, hc, ← Category.assoc, pullback.condition, Category.assoc]) =
    pullback.lift (f := qU) (g := kb ≫ hb) (k ≫ h) qW
      (by rw [Category.assoc, hc, ← Category.assoc, kc, Category.assoc]) := by
  sorry

end AlgebraicGeometry
