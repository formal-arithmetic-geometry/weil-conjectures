/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SheafPullbackCone
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Scheme tests and field-extension lifts for a pulled-back sheaf family

Source: Stacks Project, Topologies on Algebraic Spaces, Tag 041F(3), and Properties
of Spaces, Tags 03BU and 03H4 (blueprint: lem-trf-presheaf-pullback-etale-point-lifting).

The presheaf is the existing `sheafPullbackCone`: literal compatible pairs, with
componentwise restriction. The comparison isomorphism is specified by both projections.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private def explicitPullbackLimit {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) : IsLimit (sheafPullbackCone f g) := by
  apply evaluationJointlyReflectsLimits
  intro T
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
    (Types.pullbackLimitCone (f.app T) (g.app T)).isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cone.ext (Iso.refl _) ?_
    rintro (_ | _ | _)
    all_goals rfl

private theorem explicitPullbackSquare {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback (sheafPullbackCone f g).fst (sheafPullbackCone f g).snd f g :=
  IsPullback.of_isLimit (explicitPullbackLimit f g)

/-- Scheme tests of a pulled-back family are the original scheme tests along the composite;
representable étaleness and field-extension lifting therefore survive base change.
Source: Stacks Project, Tag 041F(3), with the field-point convention of Tag 03BU and
common-extension argument of Tag 03H4
(blueprint: lem-trf-presheaf-pullback-etale-point-lifting).

Proof: (1) The explicit type pullback restricts both coordinates. Construct its universal
lift by pairing cone projections; naturality and uniqueness hold coordinatewise. Mathlib
closure of the sheaf property under limits then makes this presheaf a sheaf, including
for empty covers.
(2) On any scheme test `t : h_T → G`, send `(a,(x,y))` to `(a,y)`. Its inverse sends
`(a,y)` to `(a,(t(a),y))`. The test equality forces `x=t(a)`, so both composites are
identities. Naturality of `t` makes both formulas commute with restriction. These give
the canonical comparison, characterized by its two projection equations.
(3) Apply `IsEtale (h i)` to `t ≫ g`. Its representing scheme is étale over `T`.
Lift its two maps to the explicit compatible-pair pullback. Cancel that pullback square
from the original representing square; this proves `IsEtale` of the first projection.
If `G` is represented, test along the inverse representing isomorphism. In the resulting
pullback square its opposite projection is an isomorphism, giving the representation.
(4) Apply `IsJointlySurjective h` to `g(x)` over `K`, obtaining `i`, `K → M`, and `y`.
Naturality gives `g(x|_M)=g(x)|_M=h_i(y)`. Hence `(x|_M,y)` is a compatible pair and
projects to `x|_M`. This is precisely joint surjectivity of the pulled-back family.
(5) If the index type is empty, a field-valued section of `G` would map to a section
of `H` whose lift supplies an impossible index. Thus there are no such sections.
The only inputs are [def-weil-pbc-sites-and-cohomology], [def-trf-algebraic-space],
and [def-trf-algebraic-space-jointly-surjective-family]. -/
theorem presheafPullback_etale_point_lifting {S : Scheme.{u}} {I : Type w}
    (G H : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (Hᵢ : I → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (g : G.obj ⟶ H.obj) (h : ∀ i : I, (Hᵢ i).obj ⟶ H.obj)
    (he : ∀ i : I, IsEtale (h i)) :
    (∀ i : I,
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) (sheafPullbackCone g (h i)).pt) ∧
    (∀ (i : I) (T : Over S) (t : yoneda.obj T ⟶ G.obj),
      (∃ e : (sheafPullbackCone t (sheafPullbackCone g (h i)).fst).pt ≅
          (sheafPullbackCone (t ≫ g) (h i)).pt,
        e.hom ≫ (sheafPullbackCone (t ≫ g) (h i)).fst =
          (sheafPullbackCone t (sheafPullbackCone g (h i)).fst).fst ∧
        e.hom ≫ (sheafPullbackCone (t ≫ g) (h i)).snd =
          (sheafPullbackCone t (sheafPullbackCone g (h i)).fst).snd ≫
            (sheafPullbackCone g (h i)).snd) ∧
      ∃ (U : Over S) (p : U ⟶ T) (q : yoneda.obj U ⟶ (Hᵢ i).obj),
        IsPullback q (yoneda.map p) (h i) (t ≫ g) ∧ Etale p.left) ∧
    (∀ i : I, IsEtale (sheafPullbackCone g (h i)).fst) ∧
    (∀ (i : I) (T : Over S) (_ : G.obj ≅ yoneda.obj T),
      ∃ U : Over S, Nonempty ((sheafPullbackCone g (h i)).pt ≅ yoneda.obj U)) ∧
    (IsJointlySurjective h →
      (∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
        (x : G.obj.obj (op (Over.mk s))),
        ∃ (i : I) (M : Type u) (_ : Field M) (e : K →+* M)
          (y : (Hᵢ i).obj.obj (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))),
          (h i).app _ y = H.obj.map
            (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op (g.app _ x) ∧
          ∃ p : (sheafPullbackCone g (h i)).pt.obj
              (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s))),
            p.val = (G.obj.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x,
              y) ∧
            (sheafPullbackCone g (h i)).fst.app _ p =
              G.obj.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x) ∧
      IsJointlySurjective (fun i : I ↦ (sheafPullbackCone g (h i)).fst) ∧
      (IsEmpty I → ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
        IsEmpty (G.obj.obj (op (Over.mk s))))) := by
  classical
  have hs (i : I) := explicitPullbackSquare g (h i)
  have het (i : I) : IsEtale (sheafPullbackCone g (h i)).fst := by
    intro T t
    obtain ⟨U, p, q, hq, hp⟩ := he i T (t ≫ g)
    let k := (hs i).lift (yoneda.map p ≫ t) q (by
      simpa only [Category.assoc] using hq.w.symm)
    have hk : IsPullback k (yoneda.map p) (sheafPullbackCone g (h i)).fst t := by
      apply IsPullback.of_right (h₁₂ := (sheafPullbackCone g (h i)).snd)
        (h₂₂ := g) (v₁₃ := h i)
      · simpa only [k, IsPullback.lift_snd] using hq
      · exact (hs i).lift_fst _ _ _
      · exact (hs i).flip
    exact ⟨U, p, k, hk, hp⟩
  refine ⟨?_, ?_, het, ?_, ?_⟩
  · intro i
    apply ObjectProperty.prop_of_isLimit
      (P := fun F ↦ Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
      (explicitPullbackLimit g (h i))
    intro j
    cases j with
    | none => exact H.property
    | some j =>
      cases j with
      | left => exact G.property
      | right => exact (Hᵢ i).property
  · intro i T t
    have hn := (explicitPullbackSquare t (sheafPullbackCone g (h i)).fst).flip
    have hc := hn.paste_horiz (hs i).flip
    refine ⟨⟨hc.isoIsPullback _ _ (explicitPullbackSquare (t ≫ g) (h i)).flip,
      hc.isoIsPullback_hom_snd _ _ _, hc.isoIsPullback_hom_fst _ _ _⟩,
      he i T (t ≫ g)⟩
  · intro i T e
    obtain ⟨U, p, q, hq, _⟩ := het i T e.inv
    have : IsIso q := hq.isIso_fst_of_isIso
    exact ⟨U, ⟨(asIso q).symm⟩⟩
  · intro hj
    have liftPoint (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
        (x : G.obj.obj (op (Over.mk s))) := hj K s (g.app _ x)
    have compatible (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
        (x : G.obj.obj (op (Over.mk s))) (i : I) (M : Type u) [Field M]
        (e : K →+* M)
        (y : (Hᵢ i).obj.obj (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s))))
        (hy : (h i).app _ y = H.obj.map
          (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op (g.app _ x)) :
        g.app _ (G.obj.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x) =
          (h i).app _ y := by
      rw [hy]
      exact ConcreteCategory.congr_hom (g.naturality _) x
    refine ⟨?_, ?_, ?_⟩
    · intro K _ s x
      obtain ⟨i, M, hM, e, y, hy⟩ := liftPoint K s x
      exact ⟨i, M, hM, e, y, hy,
        ⟨⟨(_, y), compatible K s x i M e y hy⟩, rfl, rfl⟩⟩
    · intro K _ s x
      obtain ⟨i, M, hM, e, y, hy⟩ := liftPoint K s x
      exact ⟨i, M, hM, e, ⟨(_, y), compatible K s x i M e y hy⟩, rfl⟩
    · intro hI K _ s
      exact ⟨fun x ↦ hI.false (liftPoint K s x).choose⟩

end AlgebraicGeometry.AlgebraicSpace
