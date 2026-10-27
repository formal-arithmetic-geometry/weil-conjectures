/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.EtalePullbackRelationPresheaf
import Sheaf.AlgebraicGeometry.FppfUniversalUnitLocallyInjective
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Restriction of an étale equivalence relation

Source: Stacks Project, Groupoids Tag 045Z and Spaces Tag 02WT
(blueprint: lem-trf-etale-relation-restriction-quotient).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

-- The image-subsheaf argument only needs the specified universal property;
-- it does not assume sheafification for all small-valued presheaves on the big site.
private theorem universal_locally_surjective
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {P : Cᵒᵖ ⥤ Type u} (F : Sheaf J (Type u)) (η : P ⟶ F.obj)
    (hη : ∀ G : Sheaf J (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k)) :
    Presheaf.IsLocallySurjective J η := by
  let R := (Subfunctor.range η).sheafify J
  have hR : Presheaf.IsSheaf J R.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range η).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp F.property))
  obtain ⟨l, hl⟩ := (hη ⟨R.toFunctor, hR⟩).surjective (Subfunctor.toRangeSheafify J η)
  have he : l ≫ R.ι = 𝟙 F.obj := by
    apply (hη F).injective
    change η ≫ l ≫ R.ι = η ≫ 𝟙 F.obj
    dsimp only at hl
    rw [← Category.assoc, hl]
    simp [Subfunctor.toRangeSheafify, R]
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  apply le_antisymm le_top
  intro T z _
  have hz : (l.app T z).val = z := by
    simpa using ConcreteCategory.congr_hom (NatTrans.congr_app he T) z
  exact hz ▸ (l.app T z).property

private theorem etale_cover_locally_surjective
    {S : Scheme.{u}} {U U' : Over S} (g : U' ⟶ U)
    [Etale g.left] [Surjective g.left] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (yoneda.map g) := by
  have hg : Sieve.generate (Presieve.singleton g) ∈ (Scheme.fppfTopology.over S) U := by
    rw [GrothendieckTopology.mem_over_iff]
    change (Sieve.generate (Presieve.singleton g)).functorPushforward (Over.forget S) ∈ _
    rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
    exact Precoverage.generate_mem_toGrothendieck g.left.singleton_mem_fppfPrecoverage
  constructor
  intro T a
  apply (Scheme.fppfTopology.over S).superset_covering ?_
    ((Scheme.fppfTopology.over S).pullback_stable a hg)
  rintro Z b ⟨V, c, _, ⟨⟩, hc⟩
  exact ⟨c, hc⟩

/-- The iterated pullback relation obtained by restricting an étale relation along `g`.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-relation-restriction-quotient). -/
noncomputable def restrictedEtaleRelation {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : Over S :=
  pullback (pullback.snd g s ≫ t) g

/-- The first projection of the restricted relation.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-relation-restriction-quotient). -/
noncomputable def restrictedEtaleRelationSource {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : restrictedEtaleRelation s t g ⟶ U' :=
  pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s

/-- The second projection of the restricted relation.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-relation-restriction-quotient). -/
noncomputable def restrictedEtaleRelationTarget {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : restrictedEtaleRelation s t g ⟶ U' :=
  pullback.snd (pullback.snd g s ≫ t) g

/-- Restricting an étale equivalence relation along an étale morphism preserves the
relation and its quotient sheaf. If the morphism is surjective, the quotient map is an
isomorphism.

Source: Stacks Project, Groupoids Tag 045Z and Spaces Tag 02WT
(blueprint: lem-trf-etale-relation-restriction-quotient).

Proof:
1. A map from a test scheme `T` to the iterated pullback is a triple `(a, r, b)`
   with `r ≫ s = a ≫ g` and `r ≫ t = b ≫ g` (def-pc-fibre-product).
   The induced relation is therefore the inverse image under `g` of the original
   equivalence relation. Reflexivity, symmetry and transitivity follow. Monicity of
   the original relation makes `r` unique for its endpoints, proving monicity of the
   restricted relation.
2. The first restricted projection is the composite of a base change of `g` and a
   base change of `s`. Reassociate the pullbacks for the second projection to express
   it as the composite of a base change of `g` and a base change of `t`. The lemmas
   lem-weil-pbc-etale-scheme-base-change and lem-weil-pbc-etale-composition-cancellation
   make both projections étale.
3. The map `[a] ↦ [a ≫ g]` on presheaf quotients is well defined by step 1. If two
   images agree, an arrow `r` in the original relation joins their endpoints. Then
   `(a, r, b)` joins the original representatives in the restricted relation, proving
   injectivity on every test scheme. The sheafification universal property
   (def-weil-pbc-sheafification) gives the canonical map `α`, with the displayed
   compatibility with the quotient projections. That compatibility determines it
   uniquely, since the presheaf coequalizer projection is epi and `hη'` is injective.
4. For sections with equal images under `α`, take local representatives in the
   restricted quotient using lem-weil-pbc-site-sheafification-sections-local.
   Refine to a common covering using def-weil-pbc-sites-and-cohomology. Local equality
   in the original sheafification gives a further covering where the quotient
   classes agree. Step 3 makes the restricted classes equal there. Sheaf separation
   then proves injectivity of `α` on every test scheme.
5. If `g` is surjective, its flatness and local finite presentation
   (def-weil-etale-morphism) make its singleton family an fppf cover
   (def-pc-fppf-site). Represent any section of `F` locally by a map to `U`, and pull
   back `g` along that map. The lemma lem-weil-pbc-etale-covering-base-change makes
   this another étale surjective cover, on which the representative lifts to `U'`.
   Composing coverings gives local lifts through `α`.
6. On overlaps these lifts have equal images, so step 4 makes them agree. The sheaf
   gluing axiom (def-weil-pbc-sites-and-cohomology) gives a unique global lift.
   Uniqueness makes the inverse natural in the test scheme, proving `IsIso α`.
-/
theorem etale_relation_restriction_quotient {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (g : U' ⟶ U) [Etale s.left] [Etale t.left] [Etale g.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k))
    (F' : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η' : coequalizer (yoneda.map (restrictedEtaleRelationSource s t g))
      (yoneda.map (restrictedEtaleRelationTarget s t g)) ⟶ F'.obj)
    (hη' : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F'.obj ⟶ G.obj ↦ η' ≫ k)) :
    Mono (prod.lift (restrictedEtaleRelationSource s t g)
      (restrictedEtaleRelationTarget s t g)) ∧
    (∀ T : Over S, Equivalence (fun a b : T ⟶ U' ↦
      ∃ r : T ⟶ restrictedEtaleRelation s t g,
        r ≫ restrictedEtaleRelationSource s t g = a ∧
        r ≫ restrictedEtaleRelationTarget s t g = b)) ∧
    Etale (restrictedEtaleRelationSource s t g).left ∧
    Etale (restrictedEtaleRelationTarget s t g).left ∧
    ∃ α : F'.obj ⟶ F.obj,
      (coequalizer.π (yoneda.map (restrictedEtaleRelationSource s t g))
          (yoneda.map (restrictedEtaleRelationTarget s t g)) ≫ η') ≫ α =
        yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      Mono α ∧ (Surjective g.left → IsIso α) := by
  obtain ⟨s', t', r', rfl, rfl, _, _, _, hm, _, hrel', hs', ht',
    hq, _, _, _, v, _, hv, hcompat⟩ := etale_pullback_relation_presheaf s t hrel g
  refine ⟨hm, hrel', hs', ht', ?_⟩
  obtain ⟨α, hα⟩ := (hη' F).surjective (v ≫ η)
  change η' ≫ α = v ≫ η at hα
  change coequalizer.π (yoneda.map (restrictedEtaleRelationSource s t g))
    (yoneda.map (restrictedEtaleRelationTarget s t g)) ≫ v =
      yoneda.map g ≫ coequalizer.π (yoneda.map s) (yoneda.map t) at hcompat
  have hcanonical :
      (coequalizer.π (yoneda.map (restrictedEtaleRelationSource s t g))
        (yoneda.map (restrictedEtaleRelationTarget s t g)) ≫ η') ≫ α =
      yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) := by
    rw [Category.assoc, hα, ← Category.assoc, hcompat, Category.assoc]
  let J := Scheme.fppfTopology.over S
  have : Presheaf.IsLocallySurjective J η' := universal_locally_surjective J F' η' hη'
  have : Presheaf.IsLocallySurjective J η := universal_locally_surjective J F η hη
  have : Presheaf.IsLocallyInjective J η :=
    Scheme.fppf_universal_unit_locally_injective _ F η hη
  have : Presheaf.IsLocallyInjective J v :=
    Presheaf.isLocallyInjective_of_injective J v (fun T ↦ hv T.unop)
  have : Presheaf.IsLocallyInjective J (v ≫ η) := inferInstance
  have : Presheaf.IsLocallyInjective J α :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
      (v ≫ η) hα
  let αs : F' ⟶ F := ⟨α⟩
  have hmono : Mono α := by
    apply (NatTrans.mono_iff_mono_app α).mpr
    intro T
    apply (mono_iff_injective _).mpr
    exact (Sheaf.isLocallyInjective_iff_injective αs).mp inferInstance T
  refine ⟨α, hcanonical, hmono, ?_⟩
  intro hg
  have : Surjective g.left := hg
  have : Presheaf.IsLocallySurjective J (yoneda.map g) :=
    etale_cover_locally_surjective g
  have : Presheaf.IsLocallySurjective J
      (coequalizer.π (yoneda.map s) (yoneda.map t)) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun T ↦ hq T.unop)
  have : Presheaf.IsLocallySurjective J
      (yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) :=
    inferInstance
  have : Presheaf.IsLocallySurjective J α :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hcanonical
  have : IsIso αs := (Sheaf.isLocallyBijective_iff_isIso αs).mp
    ⟨inferInstance, inferInstance⟩
  exact (sheafToPresheaf J (Type u)).map_isIso αs

end AlgebraicGeometry.AlgebraicSpace
