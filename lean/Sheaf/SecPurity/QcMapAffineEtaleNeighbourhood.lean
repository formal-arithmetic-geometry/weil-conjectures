/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Sheaf.AlgebraicGeometry.SeparatedEtaleChart
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Affine étale neighbourhood of a quasi-compact scheme map

Source: Stacks Project, `spaces-properties.tex`, Tag 0APL (proposition-sheaf-fpqc),
with local quasi-finiteness from `morphisms.tex`, Tag 03WS
(blueprint: lem-a1-qc-map-affine-etale-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem property_of_represented_pullback
    {S : Scheme.{u}} (P : MorphismProperty (Over S)) [P.RespectsIso]
    {F G : (Over S)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsRepresentableWith P f) {T V : Over S}
    {c : yoneda.obj T ⟶ G} {q : yoneda.obj V ⟶ F} {p : V ⟶ T}
    (h : IsPullback q (yoneda.map p) f c) : P p := by
  have hr : P.presheaf f := MorphismProperty.relative.of_exists (fun {T} a ↦ by
    obtain ⟨V, p, q, h, hp⟩ := hf _ a
    exact ⟨V, q, p, h, hp⟩)
  exact hr.property c q p h

private theorem yoneda_isEtale {S : Scheme.{u}} {U W : Over S} (k : U ⟶ W)
    (hk : Etale k.left) : IsEtale (yoneda.map k) := by
  intro T a
  let b : T ⟶ W := yoneda.preimage a
  have ha : yoneda.map b = a := yoneda.map_preimage a
  let Q := Limits.pullback k b
  have hb := (IsPullback.of_hasPullback k b).map (Over.forget S)
  have he : Etale (pullback.snd k b).left :=
    MorphismProperty.of_isPullback hb hk
  refine ⟨Q, pullback.snd k b, yoneda.map (pullback.fst k b), ?_, he⟩
  simpa only [ha] using (IsPullback.of_hasPullback k b).map yoneda

/-- Let `C` be a quasi-compact `S`-scheme and `c : C ⟶ E` an `S`-map to an algebraic
space.  There is an affine `S`-scheme `U` with a representable étale map to `E` such
that the represented pullback over `C` is surjective, étale, separated, and locally
quasi-finite.  The `IsPullback` witness records that `V` is the scheme fibre product
`C ×ₑ U` and that `p` is its projection.

Source: Stacks Project, `spaces-properties.tex`, Tag 0APL, proposition-sheaf-fpqc;
local quasi-finiteness is Tag 03WS (blueprint: lem-a1-qc-map-affine-etale-neighbourhood).

Proof: choose an affine étale atlas of `E`, retain finitely many affine charts covering
`c(C)` by quasi-compactness, and let `U` be their finite affine coproduct.  The induced
map is representable étale and its pullback `V` is surjective.  An affine scheme is
separated, and the étale projection is locally quasi-finite by Tag 03WS.
-/
theorem exists_affine_etale_neighbourhood
    {S : Scheme.{u}} (E : AlgebraicSpace S) (C : Over S)
    [CompactSpace C.left] (c : yoneda.obj C ⟶ E.obj.obj) :
    ∃ (U : Over S) (u : yoneda.obj U ⟶ E.obj.obj),
      IsAffine U.left ∧
        IsEtale u ∧
          ∃ (V : Over S) (p : V ⟶ C) (q : yoneda.obj V ⟶ yoneda.obj U),
            IsPullback q (yoneda.map p) u c ∧
              Surjective p.left ∧
                Etale p.left ∧
                  IsSeparated p.left ∧ Scheme.Hom.IsLocallyQuasiFinite p.left := by
  classical
  obtain ⟨W, w, hw, hs⟩ := E.property.2
  obtain ⟨P, p, q, hp, hps⟩ := hs C c
  have hpe : Etale p.left := property_of_represented_pullback
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) (Over.forget S)) hw hp
  let b : P ⟶ W := yoneda.preimage q
  have hb : yoneda.map b = q := yoneda.map_preimage q
  let A := W.left.affineCover
  let O : A.I₀ → Set C.left := fun i ↦
    p.left '' (b.left ⁻¹' Set.range (A.f i))
  have ho (i : A.I₀) : IsOpen (O i) := by
    exact p.left.isOpenMap _ ((A.f i).isOpenEmbedding.isOpen_range.preimage
      b.left.continuous)
  have hc : Set.univ ⊆ ⋃ i, O i := by
    intro x _
    obtain ⟨z, rfl⟩ := p.left.surjective x
    obtain ⟨i, y, hy⟩ := A.exists_eq (b.left z)
    exact Set.mem_iUnion.mpr ⟨i, z, ⟨y, hy⟩, rfl⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover O ho hc
  let U : Over S := Over.mk (Sigma.desc (fun i : J ↦ A.f i.val ≫ W.hom))
  let k : U ⟶ W := Over.homMk (Sigma.desc (fun i : J ↦ A.f i.val)) (by
    apply Sigma.hom_ext
    intro i
    simp [U])
  have hk : Etale k.left :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ ↦ inferInstance)
  let u := yoneda.map k ≫ w
  have hu : IsEtale u := isEtale_comp _ _ (yoneda_isEtale k hk) hw
  have hUa : IsAffine U.left := by dsimp [U]; infer_instance
  let : IsAffine U.left := hUa
  obtain ⟨V, v, r, hv, hvs⟩ := (separated_etale_chart E U u hu).2 C c
  have hve : Etale v.left := property_of_represented_pullback
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) (Over.forget S)) hu hv
  have hvq : Scheme.Hom.IsLocallyQuasiFinite v.left :=
    Scheme.Hom.isLocallyQuasiFinite_of_unramified v.left ⟨inferInstance, inferInstance⟩
  refine ⟨U, u, hUa, hu, V, v, r, hv, ?_, hve, hvs, hvq⟩
  let Q := Limits.pullback k b
  have hQ₀ := (IsPullback.of_hasPullback k b).map yoneda
  have hQ₁ : IsPullback (yoneda.map (pullback.fst k b))
      (yoneda.map (pullback.snd k b)) (yoneda.map k) q := by
    simpa only [hb] using hQ₀
  have hQ : IsPullback (yoneda.map (pullback.fst k b))
      (yoneda.map (pullback.snd k b ≫ p)) u c := by
    simpa only [Functor.map_comp] using hQ₁.paste_vert hp
  let e : Q ≅ V := yoneda.preimageIso (hQ.isoIsPullback _ _ hv)
  have he : e.hom ≫ v = pullback.snd k b ≫ p := by
    apply yoneda.map_injective
    simp [e]
  constructor
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ (Set.mem_univ x))
  obtain ⟨hij, z, hz, hzx⟩ := Set.mem_iUnion.mp hi
  obtain ⟨y, hy⟩ := hz
  let j : J := ⟨i, hij⟩
  let y' : U.left := Sigma.ι (fun j : J ↦ A.X j.val) j y
  have hky : k.left y' = b.left z := by
    change (Sigma.ι (fun j : J ↦ A.X j.val) j ≫ k.left) y = _
    simpa only [k, Over.homMk_left, Sigma.ι_desc] using hy
  have hQs := (IsPullback.of_hasPullback k b).map (Over.forget S)
  change IsPullback (pullback.fst k b).left (pullback.snd k b).left k.left b.left at hQs
  obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback hQs y' z hky
  refine ⟨e.hom.left t, ?_⟩
  calc
    v.left (e.hom.left t) = (e.hom ≫ v).left t := rfl
    _ = (pullback.snd k b ≫ p).left t := by rw [he]
    _ = p.left z := congrArg p.left ht
    _ = x := hzx

end AlgebraicGeometry.AlgebraicSpace
