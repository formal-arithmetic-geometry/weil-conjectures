/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FieldCurveCompletionCore
import Sheaf.AlgebraicGeometry.ProjectiveGeonormalComponents
import Sheaf.AlgebraicGeometry.GeonormalProjectiveCurveConstants
import Sheaf.AlgebraicGeometry.NormalizationDenseOpenComponents
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange

/-!
# Smooth projective completions after an inseparable field extension

Source: Stacks Project, Varieties, Tag 0GK5,
`lemma-dim-1-projective-completion-after-insep`, assertions (1)-(5)
(blueprint: lem-weil-pbc-field-curve-completion-insep).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A separated finite type scheme of dimension at most one has, after finite purely
inseparable extension, componentwise normalization with smooth projective geometrically
irreducible completions over finite separable constant fields.
Source: Stacks Project, Varieties, Tag 0GK5
(blueprint: lem-weil-pbc-field-curve-completion-insep).

The integral closed immersions `c i` enumerate the reduced irreducible components of
`X_K`: an integral closed subscheme with a given irreducible-component support is exactly
its reduced induced subscheme, equivalently that of `(X_K)_red`. The isomorphisms `e i`
identify `Y i` with their normalizations. Thus the equation for `ν` specifies the full
componentwise normalization map, including its scheme structure.

Proof:
1. Choose a dense projective completion and a finite purely inseparable extension making its
   componentwise normalization geometrically normal. Purely inseparable base change is a
   homeomorphism, preserving dimension and density of the base-changed open immersion.
2. The normalized projective components are integral, projective and of dimension at most one.
   Geometric normality passes to each component by the open coprojections and their base changes.
   Lift the finite index set when applying the component theorem to match its universe.
3. Geometric normality in dimension at most one implies smoothness and geometric reducedness.
   Global sections give a finite separable constant field; Stein factorization gives geometric
   connectedness over it. Finite separable base refinement preserves smoothness and projectivity.
   A smooth geometrically connected scheme over a field is geometrically irreducible.
4. Pull back each reduced component along the dense open immersion. These integral closed
   subschemes enumerate the open's components, since closure recovers the old component supports.
   Their normalizations identify with nonempty dense opens in the projective normalizations:
   compare the two finite normal schemes over their common dense isomorphism open.
5. The projective components and their open subschemes are Noetherian. Their structure maps and
   the finite constant-field maps are finitely presented, quasi-compact and quasi-separated.
   The finite coproduct has the same properties. Define its normalization map by the coproduct
   of the component normalizations. The pullback and normalization comparison equations give
   both displayed commutativity identities. Density and the purely inseparable homeomorphisms
   identify emptiness of the index set with emptiness of the original scheme.
-/
theorem exists_field_curve_completion_insep
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Module.Finite k K ∧ IsPurelyInseparable k K ∧
      ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
        (c : ∀ i, C i ⟶ pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Y B : Fin n → Scheme.{u})
        (e : ∀ i, Y i ≅ @Scheme.normalization (C i) (hC i))
        (j : ∀ i, Y i ⟶ B i)
        (L : Fin n → Type u) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
        (q : ∀ i, B i ⟶ Spec (.of (L i)))
        (p : ∀ i, Y i ⟶ Spec (.of K))
        (ν : (∐ Y) ⟶ pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        (∀ i, IsClosedImmersion (c i) ∧
          Set.range (c i) ∈ irreducibleComponents
            (pullback (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) ∧
        Function.Injective (fun i ↦ Set.range (c i)) ∧
        (∀ Z ∈ irreducibleComponents
          (pullback (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
          ∃ i, Set.range (c i) = Z) ∧
        ν = Sigma.desc (fun i ↦ (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ∧
        (∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) ∧
          IsOpenImmersion (j i) ∧ DenseRange (j i) ∧ Nonempty (Y i) ∧
          Smooth (q i) ∧ IsHProjective (q i) ∧ GeometricallyIrreducible (q i) ∧
          topologicalKrullDim (B i) ≤ 1 ∧
          (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i ≫
            pullback.snd (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) = p i ∧
          j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) = p i ∧
          LocallyOfFinitePresentation (p i) ∧ QuasiCompact (p i) ∧ QuasiSeparated (p i) ∧
          LocallyOfFinitePresentation
            (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))) ∧
        LocallyOfFinitePresentation (Sigma.desc p) ∧
        QuasiCompact (Sigma.desc p) ∧ QuasiSeparated (Sigma.desc p) ∧
        LocallyOfFinitePresentation (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        QuasiCompact (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        QuasiSeparated (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (n = 0 ↔ IsEmpty X) := by
  classical
  obtain ⟨T, g, a, hg, hdT, ha, hag, hda, K, hK, hkK, hfin, hinsep,
      n, C, hC, c, hc, hi, hcover, hn⟩ :=
    exists_projective_geonormal_core k X hdim
  have : IsHProjective g := hg
  have : IsProjective g := IsHProjective.isProjective g
  have : IsPurelyInseparable k K := hinsep
  let : T.Over (Spec (.of k)) := ⟨g⟩
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let XK := pullback (X ↘ Spec (.of k)) s
  let TK := pullback g s
  let f : TK ⟶ Spec (.of K) := pullback.snd g s
  have : IsHProjective f := (projective_base_change g s).toIsHProjective
  have : IsProper f := IsHProjective.isProper f
  have hTX : IsHomeomorph (pullback.fst g s).base :=
    isHomeomorph_baseChange_of_isPurelyInseparable k K T
  have hXX : IsHomeomorph (pullback.fst (X ↘ Spec (.of k)) s).base :=
    isHomeomorph_baseChange_of_isPurelyInseparable k K X
  have hdTK : topologicalKrullDim TK ≤ 1 :=
    (hTX.topologicalKrullDim_eq _).trans_le hdT
  have : ∀ i, IsIntegral (C i) := hC
  have : ∀ i, IsClosedImmersion (c i) := hc
  obtain ⟨hprops, hempty⟩ :=
    projective_geonormal_components K TK f hdTK n C c hi hcover hn
  let b : XK ⟶ TK :=
    pullback.lift (pullback.fst (X ↘ Spec (.of k)) s ≫ a)
      (pullback.snd (X ↘ Spec (.of k)) s) (by
        rw [Category.assoc, hag, pullback.condition])
  have hsq : IsPullback (pullback.fst (X ↘ Spec (.of k)) s) b a (pullback.fst g s) := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback g s)
    · simpa [b, hag] using IsPullback.of_hasPullback (X ↘ Spec (.of k)) s
    · simp [b]
  have : IsOpenImmersion a := ha
  have : IsOpenImmersion b := MorphismProperty.of_isPullback hsq ha
  have hdb : DenseRange b := by
    let e := hTX.homeomorph (pullback.fst g s).base
    have hb : (b : XK → TK) =
        e.symm ∘ a ∘ (pullback.fst (X ↘ Spec (.of k)) s) := by
      funext x
      apply e.injective
      change (pullback.fst g s) (b x) =
        e (e.symm (a ((pullback.fst (X ↘ Spec (.of k)) s) x)))
      rw [e.apply_symm_apply]
      exact congrArg (fun t : XK ⟶ T ↦ t x) hsq.w.symm
    rw [hb]
    exact e.symm.surjective.denseRange.comp
      (hda.comp hXX.surjective.denseRange a.continuous) e.symm.continuous
  obtain ⟨D, hD, d, j, hd, hdi, hdcover, hj⟩ :=
    exists_normalization_dense_open_components K TK f XK b hdb n C c hi hcover
  have : ∀ i, IsIntegral (D i) := hD
  choose L hL hKL q H using fun i ↦
    @exists_geonormal_projective_curve_constants K _ (C i).normalization (hprops i).1
      ((C i).fromNormalization ≫ c i ≫ f) (hprops i).2.2.1
      (hprops i).2.2.2.1 (hprops i).2.2.2.2
  let : ∀ i, Field (L i) := hL
  let : ∀ i, Algebra K (L i) := hKL
  let B : Fin n → Scheme.{u} := fun i ↦ (C i).normalization
  let Y : Fin n → Scheme.{u} := fun i ↦ (D i).normalization
  let p : ∀ i, Y i ⟶ Spec (.of K) := fun i ↦ j i ≫ (C i).fromNormalization ≫ c i ≫ f
  have hp (i) : (D i).fromNormalization ≫ d i ≫ pullback.snd (X ↘ Spec (.of k)) s = p i := by
    calc
      _ = (D i).fromNormalization ≫ d i ≫ b ≫ f := by simp [b, f]
      _ = _ := by simpa [p, Category.assoc] using congrArg (fun t ↦ t ≫ f) (hj i).2.2.2
  have hq (i) : j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) = p i := by
    rw [(H i).2.2.2.2.2]
  have hfp (i) : LocallyOfFinitePresentation (p i) ∧ QuasiCompact (p i) ∧
      QuasiSeparated (p i) := by
    have : IsOpenImmersion (j i) := (hj i).1
    have : IsHProjective ((C i).fromNormalization ≫ c i ≫ f) := (hprops i).2.2.1
    have : IsProper ((C i).fromNormalization ≫ c i ≫ f) := IsHProjective.isProper _
    have : IsLocallyNoetherian (B i) :=
      LocallyOfFiniteType.isLocallyNoetherian ((C i).fromNormalization ≫ c i ≫ f)
    have : IsLocallyNoetherian (Y i) := isLocallyNoetherian_of_isOpenImmersion (j i)
    have : CompactSpace (B i) :=
      QuasiCompact.compactSpace_of_compactSpace ((C i).fromNormalization ≫ c i ≫ f)
    have : IsNoetherian (B i) := {}
    have : TopologicalSpace.NoetherianSpace (B i) := inferInstance
    have : TopologicalSpace.NoetherianSpace (Y i) :=
      (j i).isOpenEmbedding.isEmbedding.noetherianSpace
    change LocallyOfFinitePresentation (j i ≫ ((C i).fromNormalization ≫ c i ≫ f)) ∧ _
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have : ∀ i, LocallyOfFinitePresentation (p i) := fun i ↦ (hfp i).1
  have : ∀ i, QuasiCompact (p i) := fun i ↦ (hfp i).2.1
  have : ∀ i, QuasiSeparated (p i) := fun i ↦ (hfp i).2.2
  have hfp_sum : LocallyOfFinitePresentation (Sigma.desc p) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) (f := p)
      (fun i ↦ (hfp i).1)
  have : ∀ i, CompactSpace (Y i) := fun i ↦
    QuasiCompact.compactSpace_of_compactSpace (p i)
  have : CompactSpace (∐ Y : Scheme.{u}) := ⟨by
    have he : (⋃ i : Fin n, Set.range (Sigma.ι Y i)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨⟨i⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (Scheme.forgetToTop ⋙ forget TopCat)
          (coproductIsCoproduct Y)) x
      exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
    rw [← he]
    exact isCompact_iUnion (fun i ↦ isCompact_range (Sigma.ι Y i).continuous)⟩
  have : LocallyOfFinitePresentation (Sigma.desc p) := hfp_sum
  have : IsLocallyNoetherian (∐ Y : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (Sigma.desc p)
  have hqc_sum : QuasiCompact (Sigma.desc p) := by infer_instance
  have hqs_sum : QuasiSeparated (Sigma.desc p) := by infer_instance
  refine ⟨K, hK, hkK, hfin, hinsep, n, D, hD, d, Y, B,
    (fun i ↦ Iso.refl _), j, L, hL, hKL, q, p,
    Sigma.desc (fun i ↦ (D i).fromNormalization ≫ d i), hd, hdi, hdcover,
    ?_, ?_, hfp_sum, hqc_sum, hqs_sum, inferInstance, inferInstance, inferInstance, ?_⟩
  · simp
  · intro i
    have : Module.Finite K (L i) := (H i).1
    have : IsOpenImmersion (j i) := (hj i).1
    have : Smooth (q i) := (H i).2.2.1
    have : IsHProjective (q i) := (H i).2.2.2.1
    have : IsProper (q i) := IsHProjective.isProper _
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    refine ⟨(H i).1, (H i).2.1, (hj i).1, (hj i).2.1, (hj i).2.2.1,
      (H i).2.2.1, (H i).2.2.2.1, (H i).2.2.2.2.1, (hprops i).2.2.2.1,
      ?_, hq i, (hfp i).1, (hfp i).2.1, (hfp i).2.2,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
    simpa using hp i
  · constructor
    · intro hz
      have he := hempty.mp hz
      exact ⟨fun x ↦ he.false (b (hXX.surjective x).choose)⟩
    · intro hx
      have : IsEmpty T := ⟨fun t ↦ hx.false (hda.some t)⟩
      have : IsEmpty TK := ⟨fun t ↦ this.false (pullback.fst g s t)⟩
      exact hempty.mpr this

end AlgebraicGeometry
