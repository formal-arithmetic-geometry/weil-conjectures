/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Scheme tests for representable étale morphisms of algebraic spaces

Source: Stacks Project, Spaces, Tags 025W, 02WK, 02WL, 02WJ; Properties of Spaces,
Tag 03EC(1),(2) (blueprint: lem-trf-space-representable-etale-scheme-tests).

The conjuncts record scheme-source representability, scheme fibre products, composition,
base change, isomorphisms, the scheme-morphism tests, and the comparison-map assertion.
Surjectivity always uses the scheme-test predicate of `AlgebraicSpace`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

private theorem representable_iff {S : Scheme.{u}} {G F : (Over S)ᵒᵖ ⥤ Type u}
    (f : G ⟶ F) : IsRepresentable f ↔ yoneda.relativelyRepresentable f := by
  constructor
  · intro h T a
    obtain ⟨U, p, q, h, _⟩ := h T a
    exact ⟨U, p, q, h⟩
  · intro h T a
    obtain ⟨U, p, q, h⟩ := h a
    exact ⟨U, p, q, h, trivial⟩

private theorem representableWith_iff {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) [P.RespectsIso]
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    IsRepresentableWith P f ↔ P.relative yoneda f := by
  constructor
  · intro h
    apply MorphismProperty.relative.of_exists
    intro T a
    obtain ⟨U, p, q, h, hp⟩ := h T a
    exact ⟨U, q, p, h, hp⟩
  · intro h T a
    exact ⟨h.rep.pullback a, h.rep.snd a, h.rep.fst a,
      h.rep.isPullback a, h.property_snd a⟩

private instance etaleOver_baseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage @Etale (Over.forget S)) where
  of_isPullback h hp := MorphismProperty.of_isPullback (P := @Etale)
    (h.map (Over.forget S)) hp

private instance surjectiveOver_baseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage @Surjective (Over.forget S)) where
  of_isPullback h hp := MorphismProperty.of_isPullback (P := @Surjective)
    (h.map (Over.forget S)) hp

/-- Scheme tests and comparison maps for representable étale morphisms.
Source: Stacks Project, Spaces, Tags 025W, 02WK, 02WL, 02WJ; Properties of Spaces,
Tag 03EC(1),(2) (blueprint: lem-trf-space-representable-etale-scheme-tests).

Proof: (1) For two scheme-source maps to `F`, pull back its representable diagonal
along the map from `h_(U ×_S T)`. The resulting scheme represents precisely the pairs
with equal image in `F`. This gives both scheme-source assertions, by
[def-pc-fibre-product], [def-trf-algebraic-space], and [lem-pc-yoneda].
(2) Test a composite on `T`, represent the second map's pullback by `Q`, and then
represent the first map's pullback to `Q` by `P`. Pasting the squares makes `P` the
composite's test. The scheme projection `P → Q → T` is étale by
[lem-weil-pbc-etale-composition-cancellation], and is surjective étale in the surjective
case by [lem-weil-pbc-etale-covering-composition].
(3) The sheaf fibre product is an algebraic space by
[lem-trf-space-fibre-products-etale-covers]. Its scheme test over `T → C` identifies
with the original map's test over `T → C → B`, by inserting or forgetting the redundant
`C` coordinate. Thus étaleness, and also scheme-test surjectivity, survive base change.
(4) A test of an isomorphism is represented by the identity of the test scheme: the
inverse sends `t` to `(t, f⁻¹(t))`. This identity is an open immersion by
[def-weil-open-immersion], hence étale by
[lem-weil-pbc-etale-composition-cancellation], and surjective by
[def-weil-surjective-morphism].
(5) A scheme map's test is its scheme fibre product, by [def-pc-fibre-product] and
[lem-pc-yoneda]. Étaleness of its projections follows from
[lem-weil-pbc-etale-base-change-finite-limits]; the converse tests along the identity.
For a surjective étale scheme map, apply [lem-weil-pbc-etale-covering-base-change] to
its singleton covering to get surjectivity as well.
(6) For the last clause, represent `h_U ×_F h_V` by `P`. Its projections `p : P → U`
and `q : P → V` are étale by the two scheme tests. The commutative triangle gives the
graph section `s : U → P`, with `s ≫ p = 1` and `s ≫ q = r`, using [lem-pc-yoneda].
Cancellation for `s ≫ p` gives étaleness of `s`; composition with `q` gives étaleness
of `r`, both by [lem-weil-pbc-etale-composition-cancellation]. Neither chart needs
surjectivity or separatedness. -/
theorem representable_etale_scheme_tests {S : Scheme.{u}} :
    (∀ (F : AlgebraicSpace S) (U : Over S) (a : yoneda.obj U ⟶ F.obj.obj),
      IsRepresentable a) ∧
    (∀ (F : AlgebraicSpace S) (U T : Over S)
      (a : yoneda.obj U ⟶ F.obj.obj) (b : yoneda.obj T ⟶ F.obj.obj),
      ∃ P : Over S, Nonempty (Limits.pullback a b ≅ yoneda.obj P)) ∧
    (∀ (A B C : AlgebraicSpace S) (f : A ⟶ B) (g : B ⟶ C),
      IsEtale f.hom.hom → IsEtale g.hom.hom → IsEtale (f ≫ g).hom.hom) ∧
    (∀ (A B C : AlgebraicSpace S) (f : A ⟶ B) (g : C ⟶ B),
      IsEtale f.hom.hom → IsEtale (Limits.pullback.snd f.hom g.hom).hom) ∧
    (∀ (A B : AlgebraicSpace S) (f : A ⟶ B),
      IsIso f → IsEtale f.hom.hom ∧ IsSurjective f.hom.hom) ∧
    (∀ (A B C : AlgebraicSpace S) (f : A ⟶ B) (g : B ⟶ C),
      IsEtale f.hom.hom → IsSurjective f.hom.hom →
      IsEtale g.hom.hom → IsSurjective g.hom.hom →
      IsEtale (f ≫ g).hom.hom ∧ IsSurjective (f ≫ g).hom.hom) ∧
    (∀ (A B C : AlgebraicSpace S) (f : A ⟶ B) (g : C ⟶ B),
      IsEtale f.hom.hom → IsSurjective f.hom.hom →
      IsEtale (Limits.pullback.snd f.hom g.hom).hom ∧
        IsSurjective (Limits.pullback.snd f.hom g.hom).hom) ∧
    (∀ (U V : Over S) (r : U ⟶ V), IsEtale (yoneda.map r) ↔ Etale r.left) ∧
    (∀ (U V : Over S) (r : U ⟶ V), Etale r.left → Surjective r.left →
      IsEtale (yoneda.map r) ∧ IsSurjective (yoneda.map r)) ∧
    (∀ (F : AlgebraicSpace S) (U V : Over S)
      (a : yoneda.obj U ⟶ F.obj.obj) (b : yoneda.obj V ⟶ F.obj.obj) (r : U ⟶ V),
      IsEtale a → IsEtale b → yoneda.map r ≫ b = a → Etale r.left) := by
  have rep (F : AlgebraicSpace S) (U : Over S) (a : yoneda.obj U ⟶ F.obj.obj) :
      IsRepresentable a := by
    apply (representable_iff a).2
    apply Functor.relativelyRepresentable.of_diag
      ((representable_iff _).1 F.property.1)
  let E : MorphismProperty (Over S) := MorphismProperty.inverseImage @Etale (Over.forget S)
  let R : MorphismProperty (Over S) := MorphismProperty.inverseImage @Surjective (Over.forget S)
  have he {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
      IsEtale f ↔ E.relative yoneda f := representableWith_iff E f
  have hr {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
      IsSurjective f ↔ R.relative yoneda f := representableWith_iff R f
  have := MorphismProperty.relative_isStableUnderBaseChange E (F := yoneda)
  have := MorphismProperty.relative_isStableUnderBaseChange R (F := yoneda)
  have bc {G F H : Sheaf (Scheme.fppfTopology.over S) (Type u)}
      (f : G ⟶ H) (g : F ⟶ H) (hf : IsEtale f.hom) :
      IsEtale (Limits.pullback.snd f g).hom :=
    (he _).2 ((E.relative yoneda).of_isPullback
      ((IsPullback.of_hasPullback f g).map
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u))) ((he f.hom).1 hf))
  have br {G F H : Sheaf (Scheme.fppfTopology.over S) (Type u)}
      (f : G ⟶ H) (g : F ⟶ H) (hf : IsSurjective f.hom) :
      IsSurjective (Limits.pullback.snd f g).hom :=
    (hr _).2 ((R.relative yoneda).of_isPullback
      ((IsPullback.of_hasPullback f g).map
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u))) ((hr f.hom).1 hf))
  refine ⟨rep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F U T a b
    obtain ⟨P, p, q, hp, _⟩ := rep F U a T b
    exact ⟨P, ⟨hp.isoPullback.symm⟩⟩
  · intro A B C f g hf hg
    exact (he _).2 ((E.relative yoneda).comp_mem _ _ ((he _).1 hf) ((he _).1 hg))
  · intro A B C f g hf
    exact bc f.hom g.hom hf
  · intro A B f hf
    have := hf
    exact ⟨(he _).2 ((E.relative yoneda).of_isIso _),
      (hr _).2 ((R.relative yoneda).of_isIso _)⟩
  · intro A B C f g hf hfs hg hgs
    exact ⟨(he _).2 ((E.relative yoneda).comp_mem _ _ ((he _).1 hf) ((he _).1 hg)),
      (hr _).2 ((R.relative yoneda).comp_mem _ _ ((hr _).1 hfs) ((hr _).1 hgs))⟩
  · intro A B C f g hf hs
    exact ⟨bc f.hom g.hom hf, br f.hom g.hom hs⟩
  · intro U V r
    exact (he _).trans MorphismProperty.relative_map_iff
  · intro U V r he' hs
    exact ⟨(he _).2 (MorphismProperty.relative_map he'),
      (hr _).2 (MorphismProperty.relative_map hs)⟩
  · intro F U V a b r ha hb h
    let ha' := (he a).1 ha
    let hb' := (he b).1 hb
    let p := ha'.rep.fst' b
    let q := ha'.rep.snd b
    have hp : E p := hb'.property a (yoneda.map q) p (ha'.rep.isPullback' b).flip
    have hq : E q := ha'.property_snd b
    let s := ha'.rep.lift' (g := b) (𝟙 U) r (by simpa using h.symm)
    have hsp : s ≫ p = 𝟙 U := ha'.rep.lift'_fst _ _ _
    have hsq : s ≫ q = r := ha'.rep.lift'_snd _ _ _
    have hs : E s := MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
      s.left p.left hp (show E (s ≫ p) by rw [hsp]; exact E.id_mem U)
    exact hsq ▸ E.comp_mem s q hs hq

end AlgebraicGeometry.AlgebraicSpace
