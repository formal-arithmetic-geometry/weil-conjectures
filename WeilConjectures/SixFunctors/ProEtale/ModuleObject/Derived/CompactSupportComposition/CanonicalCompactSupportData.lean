/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData

/-! # The canonical condensed compact-support comparison record

Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2), proof paragraphs
"The composition isomorphism", "Verification of canonicity and associativity" and
"Base change" (blueprint: def-sf-canonical-compact-support-data).

`CompactSupportComposition.canonicalCoherentData ℓ k Λ hΛ` is the one chosen record of
`CoherentData Λ k` (def-sf-condensed-compact-support-composition-data, whose module is
imported unchanged). It is determined by `coherentData_subsingleton` (stated here; its proof
is the canonicity clause of sk-thm-sf-comp-composition). The twelve laws of `ComparisonLawsFor`
are restated on it as `canonicalCoherentData_*` (clauses (1)--(12) of
def-sf-canonical-compact-support-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace CompactSupportComposition

/-! ### The canonical record, as data

`canonicalCoherentData` is the one place where a `CoherentData` record is picked. Every other
site (`CurrentCompactKunneth.operationsOver`, `CondensedSectionBaseChange.coherentData`,
`zlComparisonData`, `CondensedTensorHomMates.compositionData`, `coefficientCoherent` and the
inline `let H := Classical.choice (coherentData_exists ..)` of the Verdier files) is meant to
become an abbreviation of it. The choice is determined: `coherentData_subsingleton`
(AGENTS.md §5). The body is not exposed; downstream files use only the fields, the laws below
and `eq_canonicalCoherentData`. The hypotheses are field-general (`ringChar k` prime and
different from `ℓ`), so the record does not depend on a chosen characteristic `p` or `CharP`
instance. -/

section Canonical

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)

/-- The normalized compact-support comparison record over a field is unique.
Source: sk-thm-sf-comp-composition, canonicity ("Verification of canonicity and
associativity"; "Base change"); lem-pur-condensed-support-data-unique
(blueprint: sk-thm-sf-comp-composition).
This module states only what the definition below needs (AGENTS.md §5: the choice is
determined). The proof belongs to the canonicity clause of sk-thm-sf-comp-composition and is
delivered with that node; it is not imported here (no `import all` of the private
`coherentData_unique`).
Proof plan (the proof of the private `coherentData_unique` of
Sheaf/Paper/CondensedWeilEquivarianceParent.lean:159, which uses no property of `D.k` beyond
being a field):
1. Every morphism `f` of `SepFinType k` is separated, locally of finite type and
quasi-compact: its composite with the structure map of the target is (`Over.w`,
`IsSeparated.of_comp`, `locallyOfFiniteType_of_comp`, `QuasiCompact.of_comp`).
2. Let `H J` be two records. For compactifications `c d` of `f`, take the common dense
boundary refinement `r` of `c` and `d` (det-nagata-refinement-common-dense). Law
`refinement` for `H` and for `J` gives
`(H.comparison f c d).hom.app K ≫ ρ_d = ρ_c = (J.comparison f c d).hom.app K ≫ ρ_d` with the
refinement component `ρ_d` an isomorphism; cancel it, so `H.comparison = J.comparison`.
3. Law `open_normalized` gives `(H.openIso sq c).inv = openExchange Λ sq c =
(J.openIso sq c).inv`, hence `H.openIso = J.openIso` (`Iso.ext` on inverses).
4. For `comp`: on a compactification triangle `T`, law `comp_normalized` writes both
`H.comp f g T.cf T.cg T.cfg` and `J.comp ..` as the same explicit composite, where the
interchange `m` is unique by det-sf-comp-composition-interchange (identity on the open,
dense middle open immersion: the dense-triangle lemma above `coherentData_unique`). For
arbitrary `c d e`, law `comp_independent` together with step 2 transports to a triangle.
5. Law `exchange_normalized` writes `H.exchange` and `J.exchange` through `openIso` and
`comparison`, equal by steps 2--3.
6. `preserves`, `pullback_preserves` and `laws` are Props; conclude with the
extensionality of `CoherentData` (`cases H; cases J; congr`, funext on the families). -/
theorem coherentData_subsingleton (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    Subsingleton (CoherentData Λ k) := by
  sorry

/-- The canonical normalized compact-support comparison record of sk-thm-sf-comp-composition,
clauses (1)--(2), at an admissible coefficient over a field of characteristic different from
`ℓ`. Existence is `coherentData_exists` at `p = ringChar k`; by `coherentData_subsingleton`
the record does not depend on the choice. The body is not exposed: use the fields, the
`canonicalCoherentData_*` laws and `eq_canonicalCoherentData`.
Source: sk-thm-sf-comp-composition, clauses (1)--(2)
(blueprint: def-sf-canonical-compact-support-data). -/
@[no_expose] def canonicalCoherentData : CoherentData Λ k :=
  Classical.choice (coherentData_exists ℓ (ringChar k) (Fact.out : ringChar k ≠ ℓ) k Λ hΛ)

/-- Every normalized record equals the canonical one.
Source: sk-thm-sf-comp-composition, canonicity (blueprint: sk-thm-sf-comp-composition).
Proof: `coherentData_subsingleton`. -/
theorem eq_canonicalCoherentData (H : CoherentData Λ k) :
    H = canonicalCoherentData ℓ k Λ hΛ := by
  sorry

/-! ### The twelve laws on the canonical record

Each lemma is one conjunct of `ComparisonLawsFor`, stated on `canonicalCoherentData`. While
the record is `Classical.choice` of `coherentData_exists`, each one is the projection of the
`laws` field written in its docstring. Once the record is an explicit construction
(steps 1--7 of `coherent_exists`), the proof is the cited construction step; the statement
does not change. -/

/-- Law 1 (refinement): the comparison followed by the refinement component of `d` is the
refinement component of `c`, for every common dense boundary refinement.
Source: sk-thm-sf-comp-composition, canonical refinement normalization
(blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.1 f c d r hc hd K`. After the
construction: the comparison is defined by the common refinement (step 3 of
`coherent_exists`, det-sf-comp-coherence-refinement), and the equation is its defining
property, independent of `r` by det-nagata-refinement-common-dense. -/
theorem canonicalCoherentData_refinement {X Y : SepFinType k} (f : X ⟶ Y)
    (c d : Compactification f.hom.left)
    (r : Compactification.DenseBoundaryCompactification f.hom.left)
    [QuasiCompact f.hom.left]
    (hc : r.obj ⟶ detSfBoundaryCompactification c)
    (hd : r.obj ⟶ detSfBoundaryCompactification d)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    ((canonicalCoherentData ℓ k Λ hΛ).comparison f c d).hom.app K ≫
        compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj := by
  sorry

/-- Law 2 (comparison_id): the comparison of a compactification with itself is the identity.
Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.1 f c`. After the construction:
refine by `c` itself; both refinement components agree, so the comparison is the identity
(det-sf-comp-coherence-refinement). -/
theorem canonicalCoherentData_comparison_id {X Y : SepFinType k} (f : X ⟶ Y)
    (c : Compactification f.hom.left) :
    (canonicalCoherentData ℓ k Λ hΛ).comparison f c c = Iso.refl _ := by
  sorry

/-- Law 3 (comparison_cocycle).
Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.1 f c d e`. After the construction:
take a common dense refinement of `c d e`; all three comparisons are cancelled through its
refinement components (det-sf-comp-coherence-cocycle). -/
theorem canonicalCoherentData_comparison_cocycle {X Y : SepFinType k} (f : X ⟶ Y)
    (c d e : Compactification f.hom.left) :
    (canonicalCoherentData ℓ k Λ hΛ).comparison f c d ≪≫
        (canonicalCoherentData ℓ k Λ hΛ).comparison f d e =
      (canonicalCoherentData ℓ k Λ hΛ).comparison f c e := by
  sorry

set_option maxHeartbeats 2000000 in
-- The normalized composite instantiates several derived-functor comparison types.
/-- Law 4 (comp_normalized): on a compactification triangle the compositor is the proper
image of a normalized middle interchange, followed by the open-factor and the derived
direct-image compositors.
Source: sk-thm-sf-comp-composition, "The composition isomorphism"
(blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.1 f g T K`. After the construction:
this is the definition of the compositor on triangles (step 2 of `coherent_exists`,
det-sf-comp-composition-interchange, lem-weil-derived-direct-image-composition). -/
theorem canonicalCoherentData_comp_normalized {X Y Z : SepFinType k} (f : X ⟶ Y)
    (g : Y ⟶ Z) (T : Compactification.Triangle f.hom.left g.hom.left)
    [QuasiCompact (T.cf.g ≫ T.cg.i)]
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      ((canonicalCoherentData ℓ k Λ hΛ).comp f g T.cf T.cg T.cfg).hom.app K =
        R((T.cg.g)_*⟦Λ⟧).map
          (m ≫ R((T.p)_*⟦Λ⟧).map
            ((openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) := by
  sorry

/-- Law 5 (comp_independent): the compositor commutes with change of its three
compactifications.
Source: sk-thm-sf-comp-composition, independence of choices
(blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.1 f g c c' d d' e e' K`. After
the construction: step 3 of `coherent_exists` (mate-pasting commutes with refinement,
lem-zl-condensed-open-proper-pasting, det-sf-comp-coherence-cocycle). -/
theorem canonicalCoherentData_comp_independent {X Y Z : SepFinType k} (f : X ⟶ Y)
    (g : Y ⟶ Z) (c c' : Compactification f.hom.left) (d d' : Compactification g.hom.left)
    (e e' : Compactification (f.hom.left ≫ g.hom.left))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    ((canonicalCoherentData ℓ k Λ hΛ).comp f g c d e).hom.app K ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map
          (((canonicalCoherentData ℓ k Λ hΛ).comparison f c c').hom.app K) ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comparison g d d').hom.app
          ⟨_, ((canonicalCoherentData ℓ k Λ hΛ).preserves f c').1 K.obj K.property⟩ ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comp f g c' d' e').hom.app K := by
  sorry

/-- Law 6 (unit_left): composition with the identity compactification on the left is the
canonical identity normalization.
Source: sk-thm-sf-comp-composition, identity equations (blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.1 f c K`. After the
construction: step 4 of `coherent_exists` with the identity model (`identity`,
def-sfb-derived-open-lower-shriek-id). -/
theorem canonicalCoherentData_unit_left {X Y : SepFinType k} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    ((canonicalCoherentData ℓ k Λ hΛ).comp (𝟙 X) f
        (Compactification.ofIsProper (𝟙 X.obj.left)) c
        (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map
        ((identity Λ X.obj.left).hom.app K.obj) := by
  sorry

/-- Law 7 (unit_right).
Source: sk-thm-sf-comp-composition, identity equations (blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.2.1 f c K`. After the
construction: as `canonicalCoherentData_unit_left`, with the identity model on the target. -/
theorem canonicalCoherentData_unit_right {X Y : SepFinType k} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    ((canonicalCoherentData ℓ k Λ hΛ).comp f (𝟙 Y) c
        (Compactification.ofIsProper (𝟙 Y.obj.left))
        (c.copy (Category.comp_id f.hom.left))).hom.app K =
      (identity Λ Y.obj.left).hom.app
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Six compactifications and two threefold composites.
/-- Law 8 (assoc): the two threefold composition paths agree (canonical associators).
Source: sk-thm-sf-comp-composition, "Verification of canonicity and associativity"
(blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.2.2.1 f g h c d e cd de cde K`.
After the construction: step 4 of `coherent_exists` (disjoint moves commute, overlapping
moves are mixed pasting or the proper/open compositor associativity,
lem-zl-condensed-open-proper-pasting). -/
theorem canonicalCoherentData_assoc {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification h.hom.left)
    (cd : Compactification (f.hom.left ≫ g.hom.left))
    (de : Compactification (g.hom.left ≫ h.hom.left))
    (cde : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification Λ e).map
        (((canonicalCoherentData ℓ k Λ hΛ).comp f g c d cd).hom.app K) ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comp (f ≫ g) h cd e cde).hom.app K =
      ((canonicalCoherentData ℓ k Λ hΛ).comp g h d e de).hom.app
          ⟨_, ((canonicalCoherentData ℓ k Λ hΛ).preserves f c).1 K.obj K.property⟩ ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comp f (g ≫ h) c de
          (cde.copy (Category.assoc _ _ _).symm)).hom.app K := by
  sorry

/-- Law 9 (open_normalized): the inverse of the open isomorphism is the canonical
open-adjunction exchange mate.
Source: sk-thm-sf-comp-composition, "Base change" (blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.2.2.2.1 sq c`. After the
construction: `openIso` is defined as the inverse of `openExchange Λ sq c`, invertible by
lem-zl-condensed-open-proper-pasting (step 6 of `coherent_exists`). -/
theorem canonicalCoherentData_open_normalized {X Y X' Y' : SepFinType k} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback a f'.hom.left f.hom.left v) (c : Compactification f.hom.left) :
    ((canonicalCoherentData ℓ k Λ hΛ).openIso sq c).inv = openExchange Λ sq c := by
  sorry

set_option maxHeartbeats 2000000 in
-- The exchange composite instantiates the ambient proper exchange and two comparisons.
/-- Law 10 (exchange_normalized): the exchange is the proper base-change mate, then the
proper image of the open isomorphism, then the compactification comparison.
Source: sk-thm-sf-comp-composition, "Base change" (blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.2.2.2.2.1 sq c d K`. After the
construction: the definition of the exchange (step 6 of `coherent_exists`,
lemma-nagata-compactification-base-change, lem-weil-pbc-proper-base-change). -/
theorem canonicalCoherentData_exchange_normalized {X Y X' Y' : SepFinType k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X'.obj.left ⟶ X.obj.left}
    {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback a f'.hom.left f.hom.left v)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    ((canonicalCoherentData ℓ k Λ hΛ).exchange sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map
          (((canonicalCoherentData ℓ k Λ hΛ).openIso sq c).hom.app K.obj) ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, ((canonicalCoherentData ℓ k Λ hΛ).pullback_preserves X' X a).1
            K.obj K.property⟩ := by
  sorry

/-- Law 11 (exchange_independent): the exchange commutes with compactification comparisons.
Source: sk-thm-sf-comp-composition, "Base change", choice independence
(blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.2.2.2.2.2.1 sq c c' d d' K`.
After the construction: lem-sfb-compact-support-refinement-base-change and the cocycle
(step 6 of `coherent_exists`). -/
theorem canonicalCoherentData_exchange_independent {X Y X' Y' : SepFinType k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X'.obj.left ⟶ X.obj.left}
    {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback a f'.hom.left f.hom.left v)
    (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    (moduleObjectDerivedPullback Λ v).map
        (((canonicalCoherentData ℓ k Λ hΛ).comparison f c c').hom.app K) ≫
        ((canonicalCoherentData ℓ k Λ hΛ).exchange sq c' d').hom.app K =
      ((canonicalCoherentData ℓ k Λ hΛ).exchange sq c d).hom.app K ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comparison f' d d').hom.app
          ⟨_, ((canonicalCoherentData ℓ k Λ hΛ).pullback_preserves X' X a).1
            K.obj K.property⟩ := by
  sorry

set_option maxHeartbeats 2000000 in
-- Two stacked Cartesian squares, three exchanges and two compositors.
/-- Law 12 (comp_exchange): composition and exchange commute for two vertically stacked
Cartesian squares.
Source: sk-thm-sf-comp-composition, clause (2) and "Base change"
(blueprint: sk-thm-sf-comp-composition).
Proof: now `(canonicalCoherentData ℓ k Λ hΛ).laws.2.2.2.2.2.2.2.2.2.2.2 f g f' g' a b v sf sg
c d e c' d' e' K`. After the construction: step 7 of `coherent_exists` (mate pasting, the
mixed cube equation and open composition; lem-zl-condensed-open-proper-pasting,
lem-weil-pbc-mate-pasting, lem-sfb-ringed-derived-monoidal-comparisons). -/
theorem canonicalCoherentData_comp_exchange {X Y Z X' Y' Z' : SepFinType k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : X'.obj.left ⟶ X.obj.left) (b : Y'.obj.left ⟶ Y.obj.left)
    (v : Z'.obj.left ⟶ Z.obj.left)
    (sf : IsPullback a f'.hom.left f.hom.left b)
    (sg : IsPullback b g'.hom.left g.hom.left v)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left))
    (c' : Compactification f'.hom.left) (d' : Compactification g'.hom.left)
    (e' : Compactification (f'.hom.left ≫ g'.hom.left))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    (moduleObjectDerivedPullback Λ v).map
        (((canonicalCoherentData ℓ k Λ hΛ).comp f g c d e).hom.app K) ≫
        ((canonicalCoherentData ℓ k Λ hΛ).exchange (X := X) (Y := Z) (X' := X') (Y' := Z')
          (f := f ≫ g) (f' := f' ≫ g') (a := a) (v := v) (sf.paste_vert sg) e e').hom.app K =
      ((canonicalCoherentData ℓ k Λ hΛ).exchange (f := g) (f' := g') (a := b) (v := v)
          sg d d').hom.app
          ⟨_, ((canonicalCoherentData ℓ k Λ hΛ).preserves f c).1 K.obj K.property⟩ ≫
        (rightDerivedLowerShriekOfCompactification Λ d').map
          (((canonicalCoherentData ℓ k Λ hΛ).exchange (f := f) (f' := f') (a := a) (v := b)
            sf c c').hom.app K) ≫
        ((canonicalCoherentData ℓ k Λ hΛ).comp f' g' c' d' e').hom.app
          ⟨_, ((canonicalCoherentData ℓ k Λ hΛ).pullback_preserves X' X a).1
            K.obj K.property⟩ := by
  sorry

end Canonical

end CompactSupportComposition
end AlgebraicGeometry.ProEtale.CondensedRing
