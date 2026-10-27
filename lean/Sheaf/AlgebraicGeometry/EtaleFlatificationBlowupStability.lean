/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.ModuleStrictTransformFlatPullback
import Sheaf.AlgebraicGeometry.StrictTransformComparisonEpimorphism
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
import WeilConjectures.Blowup.Complement
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Stability of étale local module flatification under blowup

Source: Stacks Project, Flatness, Tag 0814, `lemma-flatten-module-etale-localize`,
proof paragraph 1; Divisors, Tags 0805, 080A, 080D, 080F and 080I
(blueprint: lem-trf-etale-flatification-blowup-stability).

The chart constructions below use the actual fibre products `T = Sᵢ ×[S] Bl_I S`
and `Y = Xᵢ ×[S] Bl_I S`. Cokernel expressions are the existing module strict
transform unfolded; they avoid assuming quasi-coherence or finite type of objects
whose corresponding properties are conclusions of the theorem. The quotient maps are
the strict-transform cokernel projections, and composition comparisons are the
section-normalized `tensorPullbackSectionComp` of the module-pullback node, transported
along the stated equalities of morphisms; only cited definition nodes are used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
namespace EtaleFlatification

/-- The new local base `Tᵢ`. Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable abbrev base {S T : Scheme.{u}} (e : T ⟶ S) (I : S.IdealSheafData) :=
  Limits.pullback e I.blowupMap

/-- The new local source `Yᵢ`. Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable abbrev source {S T V : Scheme.{u}} (e : T ⟶ S) (g : V ⟶ T)
    (I : S.IdealSheafData) :=
  Limits.pullback (g ≫ e) I.blowupMap

/-- The induced structural map `Yᵢ → Tᵢ`. Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable def structureMap {S T V : Scheme.{u}} (e : T ⟶ S) (g : V ⟶ T)
    (I : S.IdealSheafData) : source e g I ⟶ base e I :=
  pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)

/-- The induced étale map `Yᵢ → X₁`, determined by both projections.
Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable def sourceMap {X S T V : Scheme.{u}} (f : X ⟶ S) (e : T ⟶ S)
    (g : V ⟶ T) (j : V ⟶ X) (h : j ≫ f = g ≫ e) (I : S.IdealSheafData) :
    source e g I ⟶ Limits.pullback f I.blowupMap :=
  pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) ((Category.comp_id _).trans h.symm) (by simp)

/-- The ambient fibre product for the final local module transform.
Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable abbrev finalSpace {S T V : Scheme.{u}} (e : T ⟶ S) (g : V ⟶ T)
    (I : S.IdealSheafData) (J : T.IdealSheafData) :=
  Limits.pullback (structureMap e g I) (J.comap (pullback.fst e I.blowupMap)).blowupMap

/-- The map from the final ambient space to `Yᵢ`.
Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable abbrev finalProjection {S T V : Scheme.{u}} (e : T ⟶ S) (g : V ⟶ T)
    (I : S.IdealSheafData) (J : T.IdealSheafData) : finalSpace e g I J ⟶ source e g I :=
  pullback.fst _ _

/-- The final ambient space's map to the original local source `Xᵢ`.
Source: Stacks, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable abbrev originalProjection {S T V : Scheme.{u}} (e : T ⟶ S) (g : V ⟶ T)
    (I : S.IdealSheafData) (J : T.IdealSheafData) : finalSpace e g I J ⟶ V :=
  finalProjection e g I J ≫ pullback.fst (g ≫ e) I.blowupMap

/-- The final strict transform of `(Yᵢ → X₁)* F₁`, using the retained centre `J O_T`.
This is `moduleStrictTransform`'s supported-section quotient, with its body unfolded.
Source: Stacks, Tags 0814 and 080D (1)
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable def finalModule {X S T V : Scheme.{u}} (f : X ⟶ S) (e : T ⟶ S)
    (g : V ⟶ T) (j : V ⟶ X) (h : j ≫ f = g ≫ e)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] (J : T.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] : (finalSpace e g I J).Modules :=
  cokernel (kernel.ι (moduleStrictTransformRestriction (structureMap e g I)
    (J.comap (pullback.fst e I.blowupMap))
    ((tensorPullback (sourceMap f e g j h I)).obj (moduleStrictTransform f I F))))

/-- The quotient from the ordinary pullback of `j* F` to the final module.
The composition comparisons use the section-normalized tensor adjunction, transported
along the projection identity of the explicit fibre-product construction; the two
quotients are the cokernel projections defining the module strict transforms.
Source: Stacks, Tags 0814, 080D (1), 080I (1), and 0097
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
noncomputable def finalQuotient {X S T V : Scheme.{u}} (f : X ⟶ S) (e : T ⟶ S)
    (g : V ⟶ T) (j : V ⟶ X) (h : j ≫ f = g ≫ e)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] (J : T.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] :
    (tensorPullback (originalProjection e g I J)).obj ((tensorPullback j).obj F) ⟶
      finalModule f e g j h I J F :=
  (tensorPullbackSectionComp (originalProjection e g I J) j).inv.app F ≫
    eqToHom (congrArg (fun φ ↦ (tensorPullback φ).obj F)
      (show originalProjection e g I J ≫ j =
          finalProjection e g I J ≫ sourceMap f e g j h I ≫ pullback.fst f I.blowupMap by
        simp [sourceMap, originalProjection, Category.assoc])) ≫
    (tensorPullbackSectionComp (finalProjection e g I J)
      (sourceMap f e g j h I ≫ pullback.fst f I.blowupMap)).hom.app F ≫
    (tensorPullback (finalProjection e g I J)).map
      ((tensorPullbackSectionComp (sourceMap f e g j h I)
        (pullback.fst f I.blowupMap)).hom.app F) ≫
    (tensorPullback (finalProjection e g I J)).map
      ((tensorPullback (sourceMap f e g j h I)).map
        (cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F)))) ≫
    cokernel.π (kernel.ι (moduleStrictTransformRestriction (structureMap e g I)
      (J.comap (pullback.fst e I.blowupMap))
      ((tensorPullback (sourceMap f e g j h I)).obj (moduleStrictTransform f I F))))

/-- The comparison clauses for one chart, including the reverse blowup order and
compatibility with the actual quotient maps. The isomorphisms `t`, `c`, `r` are over `Sᵢ`;
a morphism into a blowup over its base is unique (Stacks, Tag 0806), so they are the
canonical comparisons, in particular `t` is the flat base-change comparison of Tag 0805.
The maps on ambient fibre products are fixed by both projections; the module
isomorphism is fixed by its quotient square.
Source: Stacks, Tag 0814, proof paragraph 1; Tags 0805, 080A and 080I (1)
(blueprint: lem-trf-etale-flatification-blowup-stability). -/
def ChartConclusion {X S T V : Scheme.{u}} (U : S.Opens)
    (f : X ⟶ S) (e : T ⟶ S) (g : V ⟶ T) (j : V ⟶ X)
    (h : j ≫ f = g ≫ e) (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : T.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] : Prop :=
  (J.comap (pullback.fst e I.blowupMap)).ofFiniteType ∧
  Disjoint ((pullback.snd e I.blowupMap ⁻¹ᵁ (I.blowupMap ⁻¹ᵁ U)) : Set (base e I))
    ((J.comap (pullback.fst e I.blowupMap)).support : Set (base e I)) ∧
  IsCompact ((pullback.snd e I.blowupMap ⁻¹ᵁ (I.blowupMap ⁻¹ᵁ U)) : Set (base e I)) ∧
  (finalModule f e g j h I J F).IsFlatOver (pullback.snd _ _) ∧
  ∃ (t : base e I ≅ (I.comap e).blowup),
    t.hom ≫ (I.comap e).blowupMap = pullback.fst e I.blowupMap ∧
    ∃ (c : (J.comap (pullback.fst e I.blowupMap)).blowup ≅ ((I.comap e) * J).blowup)
      (r : (J.comap (pullback.fst e I.blowupMap)).blowup ≅
        ((I.comap e).comap J.blowupMap).blowup),
      c.hom ≫ ((I.comap e) * J).blowupMap =
        (J.comap (pullback.fst e I.blowupMap)).blowupMap ≫
          pullback.fst e I.blowupMap ∧
      r.hom ≫ ((I.comap e).comap J.blowupMap).blowupMap ≫ J.blowupMap =
        (J.comap (pullback.fst e I.blowupMap)).blowupMap ≫
          pullback.fst e I.blowupMap ∧
      (((I.comap e) * J).support : Set T) =
        ((I.comap e).support : Set T) ∪ (J.support : Set T) ∧
      ∃ (hA : ((I.comap e).comap J.blowupMap).toModules.IsFiniteType)
        (hH : ((tensorPullback j).obj F).IsQuasicoherent)
        (hHJ : (@moduleStrictTransform _ _ g J inferInstance
          ((tensorPullback j).obj F) hH).IsQuasicoherent)
        (m : finalSpace e g I J ⟶
          Limits.pullback (pullback.snd g J.blowupMap)
            ((I.comap e).comap J.blowupMap).blowupMap)
        (hm : m ≫ pullback.fst _ _ ≫ pullback.fst g J.blowupMap =
          originalProjection e g I J),
        IsIso m ∧
        m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ r.hom ∧
        ∃! θ : finalModule f e g j h I J F ≅
            (tensorPullback m).obj
              (@moduleStrictTransform _ _ (pullback.snd g J.blowupMap)
                ((I.comap e).comap J.blowupMap) hA
                (@moduleStrictTransform _ _ g J inferInstance ((tensorPullback j).obj F) hH)
                hHJ),
          finalQuotient f e g j h I J F ≫ θ.hom =
            eqToHom (congrArg (fun φ ↦ (tensorPullback φ).obj ((tensorPullback j).obj F))
              hm.symm) ≫
            (tensorPullbackSectionComp m
              (pullback.fst (pullback.snd g J.blowupMap)
                ((I.comap e).comap J.blowupMap).blowupMap ≫
                  pullback.fst g J.blowupMap)).hom.app ((tensorPullback j).obj F) ≫
            (tensorPullback m).map
              ((tensorPullbackSectionComp
                (pullback.fst (pullback.snd g J.blowupMap)
                  ((I.comap e).comap J.blowupMap).blowupMap)
                (pullback.fst g J.blowupMap)).hom.app ((tensorPullback j).obj F)) ≫
            (tensorPullback m).map
              ((tensorPullback (pullback.fst (pullback.snd g J.blowupMap)
                  ((I.comap e).comap J.blowupMap).blowupMap)).map
                (cokernel.π (kernel.ι
                  (moduleStrictTransformRestriction g J ((tensorPullback j).obj F)))) ≫
              cokernel.π (kernel.ι (moduleStrictTransformRestriction
                (pullback.snd g J.blowupMap) ((I.comap e).comap J.blowupMap)
                (@moduleStrictTransform _ _ g J inferInstance ((tensorPullback j).obj F) hH))))

end EtaleFlatification

/-- Étale local flatification data remain valid after any admissible blowup, with
canonical comparisons for both blowup orders and their module quotient maps.
Source: Stacks Project, Flatness, Tag 0814, proof paragraph 1
(blueprint: lem-trf-etale-flatification-blowup-stability).

Proof: (1) Module admissible-blowup calculus (2) gives a qcqs new base and
quasi-coherent F₁. Admissible blowup over the preserved open is an isomorphism,
so U₁ is quasi-compact.
(2) Extend I to each Sᵢ. Finite local generators extend and localize, and the ideal
is unit on eᵢ⁻¹U. Flat base change of blowups identifies Tᵢ with Bl_{I O_{Sᵢ}} Sᵢ.
Apply the same calculus to obtain qcqs of Tᵢ.
(3) Étale and quasi-compact base-change stability give the new maps' properties.
Fibre-product associativity identifies Yᵢ with Xᵢ ×[X] X₁. Covering base change gives
joint surjectivity separately for either family whenever its original family covers.
(4) Extend Jᵢ to Tᵢ. It is finite type and unit on the inverse image of U₁, which is
quasi-compact. The product (I O_{Sᵢ}) Jᵢ is likewise finite type and unit on eᵢ⁻¹U.
(5) Product-ideal blowup comparison in both orders gives c and r. The product's
zero set is the union of the two zero sets. The complement isomorphism also gives
the composite-centre support identity needed by the module comparison in either order.
(6) Module strict transform commutes with flat pullback along eᵢ and jᵢ, respecting
the ordinary-pullback quotient maps (lem-trf-module-strict-transform-flat-pullback).
(7) The strict-transform comparison epimorphism, together with the absence of
sections supported on the exceptional union (lem-trf-iterated-transform-exceptional-support),
is an isomorphism in each order. Both orders identify with the product-centre
transform. Their quotient squares make the comparison unique.
(8) In the reverse order the first transform is flat by hypothesis. Module
admissible-blowup calculus (2) says its next transform is its ordinary pullback,
hence is flat. Transfer this flatness through the comparisons of (6)--(7). -/
theorem etaleFlatification_blowup_stability
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (_hU : IsCompact (U : Set S)) (f : X ⟶ S)
    (F : X.Modules) [hF : F.IsQuasicoherent]
    (ι : Type v) [Finite ι] (T V : ι → Scheme.{u})
    [∀ i : ι, CompactSpace (T i)] [∀ i : ι, QuasiSeparatedSpace (T i)]
    (e : ∀ i : ι, T i ⟶ S) [∀ i : ι, QuasiCompact (e i)] [∀ i : ι, Etale (e i)]
    (g : ∀ i : ι, V i ⟶ T i) (j : ∀ i : ι, V i ⟶ X) [∀ i : ι, Etale (j i)]
    (h : ∀ i : ι, j i ≫ f = g i ≫ e i)
    (J : ∀ i : ι, (T i).IdealSheafData) [∀ i : ι, (J i).toModules.IsFiniteType]
    (_hJ : ∀ i : ι, Disjoint ((e i ⁻¹ᵁ U) : Set (T i)) ((J i).support : Set (T i)))
    (_hflat : ∀ i : ι,
      (cokernel (kernel.ι (moduleStrictTransformRestriction (g i) (J i)
        ((tensorPullback (j i)).obj F)))).IsFlatOver (pullback.snd (g i) (J i).blowupMap))
    (B : IsAdmissible S U) :
    ∃ hI : B.I.toModules.IsFiniteType,
      CompactSpace B.I.blowup ∧ QuasiSeparatedSpace B.I.blowup ∧
      IsCompact ((B.I.blowupMap ⁻¹ᵁ U) : Set B.I.blowup) ∧
      (@moduleStrictTransform _ _ f B.I hI F hF).IsQuasicoherent ∧
      (∀ i : ι, CompactSpace (EtaleFlatification.base (e i) B.I) ∧
        QuasiSeparatedSpace (EtaleFlatification.base (e i) B.I) ∧
        QuasiCompact (pullback.snd (e i) B.I.blowupMap) ∧
        Etale (pullback.snd (e i) B.I.blowupMap) ∧
        Etale (EtaleFlatification.sourceMap f (e i) (g i) (j i) (h i) B.I)) ∧
      ((∀ s : S, ∃ i : ι, ∃ t : T i, e i t = s) →
        ∀ s : B.I.blowup, ∃ i : ι, ∃ t : EtaleFlatification.base (e i) B.I,
          pullback.snd (e i) B.I.blowupMap t = s) ∧
      ((∀ x : X, ∃ i : ι, ∃ y : V i, j i y = x) →
        ∀ x : ↥(Limits.pullback (C := Scheme.{u}) f B.I.blowupMap), ∃ i : ι,
          ∃ y : EtaleFlatification.source (e i) (g i) B.I,
            EtaleFlatification.sourceMap f (e i) (g i) (j i) (h i) B.I y = x) ∧
      ∀ i : ι, @EtaleFlatification.ChartConclusion _ _ _ _ U f (e i) (g i) (j i)
        (h i) B.I hI (J i) inferInstance F hF := by
  sorry

end AlgebraicGeometry.Scheme.Modules
