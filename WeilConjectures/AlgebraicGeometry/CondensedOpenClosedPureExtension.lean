/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.AdicLocalCharacteristicFactor
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-! # Condensed Weil sheaves under open and closed extension

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-pure-extension).

The helpers expand the clauses of this assertion using the recorded coefficient,
Weil-module, geometric-evaluation and punctual-weight definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Limits
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- Base change of a model morphism through the chosen geometric-fibre functor.
Source: latest blueprint, open/closed gluing paragraph
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
abbrev extensionGeometricMap
    {S₀ T₀ : Over (Spec (.of D.k₀))} (f₀ : S₀ ⟶ T₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

variable (S₀ T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom]
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]

/-- Scalar geometric evaluation on actual Weil modules.
Source: latest blueprint, open/closed gluing paragraph
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def extensionFiber (K : Type u) [Field K] [IsAlgClosed K]
    (z : Spec (.of K) ⟶ (D.geometricFiber S₀).left) :
    WeilModule D l S₀ ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  IsoAlgebra.forget _ ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
    CondensedQbarGeometricEvaluation.fieldFiber K l

/-- Exactness, constructibility, purity and the original weights of every filtration.
Source: latest blueprint, open/closed gluing paragraph
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def ExtensionWeights (E : WeilModule D l S₀ ⥤ WeilModule D l T₀)
    (iota : PadicAlgCl l ≃+* ℂ) : Prop :=
  PreservesFiniteLimits E ∧ PreservesFiniteColimits E ∧
  (∀ M : WeilModule D l S₀,
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber S₀).left M.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber T₀).left (E.obj M).carrier) ∧
  (∀ (M : WeilModule D l S₀) (w : ℝ),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber S₀).left M.carrier →
    Pure D l S₀ M iota.toRingHom w → Pure D l T₀ (E.obj M) iota.toRingHom w) ∧
  (∀ (M : WeilModule D l S₀) (w : ℝ),
    Mixed D l S₀ M iota.toRingHom w → Mixed D l T₀ (E.obj M) iota.toRingHom w) ∧
  (∀ (m : ℕ) (G : Fin (m + 1) → WeilModule D l S₀)
      (φ : ∀ r : Fin m, G r.castSucc ⟶ G r.succ) (v : Fin m → ℝ),
    (∀ r, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber S₀).left (G r).carrier) →
    IsZero (G 0) → (∀ r, Mono (φ r)) →
    (∀ r, Pure D l S₀ (cokernel (φ r)) iota.toRingHom (v r)) →
      IsZero (E.obj (G 0)) ∧ (∀ r, Mono (E.map (φ r))) ∧
      ∀ r, (∃ e : cokernel (E.map (φ r)) ≅ E.obj (cokernel (φ r)),
        cokernel.π (E.map (φ r)) ≫ e.hom = E.map (cokernel.π (φ r))) ∧
        Pure D l T₀ (cokernel (E.map (φ r))) iota.toRingHom (v r))

/-- Natural supported fibres, zero fibres elsewhere, and the same comparisons
intertwining the local geometric Frobenius with unchanged residue cardinality.
Source: latest blueprint, open/closed gluing paragraph
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def ExtensionFibers (f₀ : S₀ ⟶ T₀)
    (E : WeilModule D l S₀ ⥤ WeilModule D l T₀) : Prop :=
  ∃ τ : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (z : Spec (.of K) ⟶ (D.geometricFiber S₀).left),
      E ⋙ extensionFiber D l T₀ K (z ≫ extensionGeometricMap D f₀) ≅
        extensionFiber D l S₀ K z,
  (∀ (K : Type u) [Field K] [IsAlgClosed K]
      (z : Spec (.of K) ⟶ (D.geometricFiber T₀).left),
    Disjoint (Set.range z) (Set.range (extensionGeometricMap D f₀)) →
    ∀ M : WeilModule D l S₀, IsZero ((extensionFiber D l T₀ K z).obj (E.obj M))) ∧
  (∀ (s : {s : S₀.left // s ∈ closedPoints S₀.left})
      (t : {t : T₀.left // t ∈ closedPoints T₀.left}),
    f₀.left s.val = t.val →
      Nat.card (S₀.left.residueField s.val) = Nat.card (T₀.left.residueField t.val) ∧
      ∀ (a : S₀.left.residueField s.val →+* D.k)
        (ha : a.comp (S₀.hom.residueFieldAlgebraMap s.val) = algebraMap D.k₀ D.k)
        (b : T₀.left.residueField t.val →+* D.k)
        (hb : b.comp (T₀.hom.residueFieldAlgebraMap t.val) = algebraMap D.k₀ D.k),
      localClosedPoint D S₀ s a ha ≫ extensionGeometricMap D f₀ =
        localClosedPoint D T₀ t b hb →
      ∀ M : WeilModule D l S₀,
      ∃ e : closedFiber D l T₀ (E.obj M) t b hb ≅ closedFiber D l S₀ M s a ha,
        HEq e.hom ((τ D.k (localClosedPoint D S₀ s a ha)).hom.app M) ∧
        closedOperator D l T₀ (E.obj M) t b hb ≫ e.hom =
          e.hom ≫ closedOperator D l S₀ M s a ha)

variable {U₀ Z₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The actual open extension functor on module objects.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def openModuleExtension (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [hj : IsOpenImmersion (extensionGeometricMap D j₀)] :=
  CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l)
    (extensionGeometricMap D j₀)

/-- The actual closed direct image on module objects.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def closedModuleExtension (i₀ : Z₀ ⟶ X₀) :=
  CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (extensionGeometricMap D i₀)

/-- Actual inverse image on module objects.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def moduleRestriction (f₀ : U₀ ⟶ X₀) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (extensionGeometricMap D f₀)

/-- Transport of the actual open extension to Weil modules.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def openWeilExtension (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [hj : IsOpenImmersion (extensionGeometricMap D j₀)]
    (e : openModuleExtension D l j₀ ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius U₀).hom ⋙ openModuleExtension D l j₀) :
    WeilModule D l U₀ ⥤ WeilModule D l X₀ :=
  IsoAlgebra.mapOfNatIso e

/-- Transport of the actual closed direct image to Weil modules.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def closedWeilExtension (i₀ : Z₀ ⟶ X₀)
    (e : closedModuleExtension D l i₀ ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius Z₀).hom ⋙ closedModuleExtension D l i₀) :
    WeilModule D l Z₀ ⥤ WeilModule D l X₀ :=
  IsoAlgebra.mapOfNatIso e

/-- The restriction of an actual Weil module along a Frobenius square.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
def weilRestriction (f₀ : U₀ ⟶ X₀)
    (sq : CommSq (D.geometricFrobenius U₀).hom (extensionGeometricMap D f₀)
      (extensionGeometricMap D f₀) (D.geometricFrobenius X₀).hom) :
    WeilModule D l X₀ ⥤ WeilModule D l U₀ :=
  IsoAlgebra.mapOfNatIso (CondensedRing.upperStarSquareComparison
    (Profinite.padicAlgClRingObj l) sq).symm

set_option maxHeartbeats 800000 in
-- Allow elaboration of the actual condensed module and fixed-pair comparison types.
/-- The canonical comparison data for the two extensions; the open comparison is
fixed by the adjunction mate and the closed one by direct-image base change.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
structure OpenClosedComparison (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left]
    [hj : IsOpenImmersion (extensionGeometricMap D j₀)] where
  sj : CommSq (D.geometricFrobenius U₀).hom (extensionGeometricMap D j₀)
    (extensionGeometricMap D j₀) (D.geometricFrobenius X₀).hom
  si : CommSq (D.geometricFrobenius Z₀).hom (extensionGeometricMap D i₀)
    (extensionGeometricMap D i₀) (D.geometricFrobenius X₀).hom
  ej : openModuleExtension D l j₀ ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius U₀).hom ⋙ openModuleExtension D l j₀
  ei : closedModuleExtension D l i₀ ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius X₀).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius Z₀).hom ⋙ closedModuleExtension D l i₀
  open_mate : ej.inv = ((mateEquiv
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj l) (extensionGeometricMap D j₀))
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj l) (extensionGeometricMap D j₀))).symm
        (.mk _ _ _ _ (CondensedRing.upperStarSquareComparison
          (Profinite.padicAlgClRingObj l) sj).inv)).natTrans
  closed_baseChange : ei.hom =
    CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l) si

set_option maxHeartbeats 800000 in
-- Allow elaboration of the actual condensed module and fixed-pair comparison types.
/-- The actual localization arrows as an exact sequence of Weil modules.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
structure OpenClosedWeilSequence (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left]
    [hj : IsOpenImmersion (extensionGeometricMap D j₀)] (c : OpenClosedComparison D l j₀ i₀)
    (M : WeilModule D l X₀) where
  a : (openWeilExtension D l j₀ c.ej).obj ((weilRestriction D l j₀ c.sj).obj M) ⟶ M
  b : M ⟶ (closedWeilExtension D l i₀ c.ei).obj ((weilRestriction D l i₀ c.si).obj M)
  open_counit : HEq a.hom.f
    ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj l) (extensionGeometricMap D j₀)).counit.app M.carrier)
  closed_unit : HEq b.hom.f ((CondensedRing.upperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj l) (extensionGeometricMap D i₀)).unit.app M.carrier)
  mono : Mono a.hom.f
  epi : Epi b.hom.f
  exact : (ComposableArrows.mk₂ a.hom.f b.hom.f).Exact

set_option maxHeartbeats 800000 in
-- Allow elaboration of the actual condensed module and fixed-pair comparison types.
/-- The assertions attached to the two actual Weil extension functors.
Source: latest blueprint, open--closed gluing
(blueprint: lem-zl-condensed-open-closed-pure-extension). -/
structure OpenClosedPureExtension (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left]
    [hj : IsOpenImmersion (extensionGeometricMap D j₀)] (iota : PadicAlgCl l ≃+* ℂ) where
  comparison : OpenClosedComparison D l j₀ i₀
  open_weights : ExtensionWeights D l U₀ X₀ (openWeilExtension D l j₀ comparison.ej) iota
  closed_weights : ExtensionWeights D l Z₀ X₀ (closedWeilExtension D l i₀ comparison.ei) iota
  open_fibers : ExtensionFibers D l U₀ X₀ j₀ (openWeilExtension D l j₀ comparison.ej)
  closed_fibers : ExtensionFibers D l Z₀ X₀ i₀ (closedWeilExtension D l i₀ comparison.ei)
  sequence : ∀ M : WeilModule D l X₀,
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier →
    Nonempty (OpenClosedWeilSequence D l j₀ i₀ comparison M)

/-- The geometric open immersion and the canonical Frobenius comparison data of the open
and closed extensions exist.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-comparison-data-core).

Proof: Geometric base change preserves open immersions, so the base change of `j₀` is
an open immersion. The geometric Frobenius `id × Spec(z ↦ z^{1/q})` is an automorphism
natural in the `k₀`-scheme, so `j₀` and `i₀` give commuting Frobenius squares `sj`, `si`,
and these squares are cartesian. For the open extension take `ej` with inverse the
adjunction mate (for `j_! ⊣ j^*`) of the inverse of the inverse-image square comparison;
it is invertible because the square is cartesian and `j_!` commutes with base change
along it. For the closed extension take `ei` with forward map the direct-image base
change of `si`, invertible by base change for the closed immersion along the cartesian
square. The equations `open_mate` and `closed_baseChange` hold by construction.
-/
theorem comparison_data_core
    (_hl : l ≠ D.p) (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ) :
    ∃ hj : IsOpenImmersion (extensionGeometricMap D j₀),
      Nonempty (OpenClosedComparison (hj := hj) D l j₀ i₀) := by
  sorry

/-- For the canonical comparison data, both Weil extensions are exact, preserve
constructibility, punctual purity of each weight, mixedness and the weights of finite
filtrations, and have the natural geometric fibres.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-extension-properties-core).

Proof: The comparison data are unique (fixed by `open_mate` and `closed_baseChange`).
The geometric schemes are Noetherian and qcqs and the open immersion is quasi-compact,
so module localization applies to the finite-subextension coefficient ring. Append the
zero complementary stratum to each finite lisse stratification to obtain
constructibility. Exactness of the underlying module functors and the exact Frobenius
autoequivalences make the lifted functors exact. Base change to any geometric point
gives the identity on the support and the empty scheme off it, proving the natural
fibre formulas. The open local-extension lemma normalizes the open comparison; the
transpose identity of the closed comparison makes the closed counit a Weil isomorphism,
and the immersion local-Frobenius lemma identifies its local return and residue field.
On the support eigenvalues and residue cardinalities are unchanged; off it a zero fibre
has no eigenvalues: purity at each weight. Exactness applied to the successive
filtration sequences identifies the new quotients with extensions of the old ones, so
each keeps its weight.
-/
theorem extension_properties_core
    (_hl : l ≠ D.p) (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ)
    (iota : PadicAlgCl l ≃+* ℂ)
    (hj : IsOpenImmersion (extensionGeometricMap D j₀))
    (c : OpenClosedComparison (hj := hj) D l j₀ i₀) :
    ExtensionWeights D l U₀ X₀ (openWeilExtension D l j₀ c.ej) iota ∧
      ExtensionWeights D l Z₀ X₀ (closedWeilExtension D l i₀ c.ei) iota ∧
      ExtensionFibers D l U₀ X₀ j₀ (openWeilExtension D l j₀ c.ej) ∧
      ExtensionFibers D l Z₀ X₀ i₀ (closedWeilExtension D l i₀ c.ei) := by
  sorry

/-- The canonical Frobenius comparisons of the open and closed extensions, their
exactness, constructibility and weight preservation, and their natural fibres.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-comparison-extension-data).

Proof: `comparison_data_core` gives the geometric open immersion and the canonical
comparison `c`; `extension_properties_core` gives the weight and fibre clauses of both
extensions for `c`.
-/
theorem comparison_and_extension_data
    (_hl : l ≠ D.p) (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ)
    (iota : PadicAlgCl l ≃+* ℂ) :
    ∃ hj : IsOpenImmersion (extensionGeometricMap D j₀),
      ∃ c : OpenClosedComparison (hj := hj) D l j₀ i₀,
      ExtensionWeights D l U₀ X₀ (openWeilExtension D l j₀ c.ej) iota ∧
      ExtensionWeights D l Z₀ X₀ (closedWeilExtension D l i₀ c.ei) iota ∧
      ExtensionFibers D l U₀ X₀ j₀ (openWeilExtension D l j₀ c.ej) ∧
      ExtensionFibers D l Z₀ X₀ i₀ (closedWeilExtension D l i₀ c.ei) := by
  obtain ⟨hj, ⟨c⟩⟩ := comparison_data_core D l _hl U₀ Z₀ X₀ j₀ i₀ _hcomp
  obtain ⟨hwj, hwi, hfj, hfi⟩ :=
    extension_properties_core D l _hl U₀ Z₀ X₀ j₀ i₀ _hcomp iota hj c
  exact ⟨hj, c, hwj, hwi, hfj, hfi⟩

/-- For the canonical comparison data, the actual counit of `j_! ⊣ j^*` and unit of
`i^* ⊣ i_*` at the carrier of a Weil module are the carriers of Weil morphisms.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-localization-maps-core).

Proof: The Weil structures of `j_!j^*M` and `i_*i^*M` are built from `ej`, `ei` and the
inverse-image square comparisons of `sj`, `si`. Since `ej.inv` is the mate of the
square comparison (`open_mate`), the counit commutes with these Frobenius structures
and the one of `M` (the defining property of the mate); since `ei.hom` is the
direct-image base change (`closed_baseChange`), the unit does likewise (the transpose
identity of base change). Hence both carrier maps lift to Weil morphisms.
-/
theorem localization_maps_core
    (_hl : l ≠ D.p) (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ)
    (iota : PadicAlgCl l ≃+* ℂ) (hj : IsOpenImmersion (extensionGeometricMap D j₀))
    (c : OpenClosedComparison (hj := hj) D l j₀ i₀)
    (M : WeilModule D l X₀) :
    ∃ a : (openWeilExtension D l j₀ c.ej).obj
          ((weilRestriction D l j₀ c.sj).obj M) ⟶ M,
      ∃ b : M ⟶ (closedWeilExtension D l i₀ c.ei).obj
          ((weilRestriction D l i₀ c.si).obj M),
      HEq a.hom.f
        ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj l) (extensionGeometricMap D j₀)).counit.app M.carrier) ∧
      HEq b.hom.f ((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj l) (extensionGeometricMap D i₀)).unit.app M.carrier) := by
  sorry

/-- Weil morphisms whose carriers are the actual counit of `j_! ⊣ j^*` and unit of
`i^* ⊣ i_*` have carriers forming a short exact sequence.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-localization-exactness-core).

Proof: The geometric schemes are Noetherian and qcqs and the open immersion is
quasi-compact, so module localization applies; its clause (3) says that, for every
module, the counit `j_!j^*M → M` is a monomorphism, the unit `M → i_*i^*M` an
epimorphism, and the two form an exact sequence. Through `ha` and `hb` these are the
carriers of `a` and `b`.
-/
theorem localization_exactness_core
    (_hl : l ≠ D.p) (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ)
    (iota : PadicAlgCl l ≃+* ℂ) (hj : IsOpenImmersion (extensionGeometricMap D j₀))
    (c : OpenClosedComparison (hj := hj) D l j₀ i₀)
    (M : WeilModule D l X₀)
    (a : (openWeilExtension D l j₀ c.ej).obj
          ((weilRestriction D l j₀ c.sj).obj M) ⟶ M)
    (b : M ⟶ (closedWeilExtension D l i₀ c.ei).obj
          ((weilRestriction D l i₀ c.si).obj M))
    (ha : HEq a.hom.f
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj l) (extensionGeometricMap D j₀)).counit.app M.carrier))
    (hb : HEq b.hom.f ((CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) (extensionGeometricMap D i₀)).unit.app M.carrier)) :
    Mono a.hom.f ∧ Epi b.hom.f ∧ (ComposableArrows.mk₂ a.hom.f b.hom.f).Exact := by
  sorry

/-- For the canonical comparison, the actual counit of `j_! ⊣ j^*` and unit of
`i^* ⊣ i_*` form an exact sequence of Weil modules on every constructible Weil module.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-localization-sequence-data).

Proof: `localization_maps_core` gives the Weil morphisms `a`, `b` with the actual
counit and unit as carriers; `localization_exactness_core` gives their mono, epi and
exactness clauses; package them as `OpenClosedWeilSequence`.
-/
theorem localization_sequence_data
    (_hl : l ≠ D.p) (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ)
    (iota : PadicAlgCl l ≃+* ℂ) (hj : IsOpenImmersion (extensionGeometricMap D j₀))
    (c : OpenClosedComparison (hj := hj) D l j₀ i₀) :
    ∀ M : WeilModule D l X₀,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left M.carrier →
      Nonempty (OpenClosedWeilSequence D l j₀ i₀ c M) := by
  intro M hM
  obtain ⟨a, b, ha, hb⟩ :=
    localization_maps_core D l _hl U₀ Z₀ X₀ j₀ i₀ _hcomp iota hj c M
  obtain ⟨hma, hbe, hex⟩ :=
    localization_exactness_core D l _hl U₀ Z₀ X₀ j₀ i₀ _hcomp iota hj c M a b ha hb
  exact ⟨⟨a, b, ha, hb, hma, hbe, hex⟩⟩

/-- Exact open and closed extensions, with natural fibres, the canonical Frobenius
comparisons, the unchanged pure quotient weights, and the actual localization arrows.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 8--9
(blueprint: lem-zl-condensed-open-closed-pure-extension).

Proof: `comparison_and_extension_data` gives the geometric open immersion, the
canonical comparison and its weight and fibre clauses; `localization_sequence_data`
gives the Weil localization sequence for that comparison.
-/
theorem condensed_openClosed_pure_extension (_hl : l ≠ D.p)
    (U₀ Z₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
    (_hcomp : Set.range j₀.left = (Set.range i₀.left)ᶜ)
    (iota : PadicAlgCl l ≃+* ℂ) :
    ∃ hj : IsOpenImmersion (extensionGeometricMap D j₀),
      Nonempty (OpenClosedPureExtension (hj := hj) D l j₀ i₀ iota) := by
  obtain ⟨hj, c, hwj, hwi, hfj, hfi⟩ :=
    comparison_and_extension_data D l _hl U₀ Z₀ X₀ j₀ i₀ _hcomp iota
  refine ⟨hj, ⟨⟨c, hwj, hwi, hfj, hfi, ?_⟩⟩⟩
  intro M hM
  exact localization_sequence_data D l _hl U₀ Z₀ X₀ j₀ i₀ _hcomp iota hj c M hM

end WeilConjectures.CondensedWeil
