/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Rigidity of sections of pulled back étale sheaves

Let `t : T ⟶ R` be a morphism of schemes and `G` an abelian étale sheaf on `R`.

If `t` factors through the spectrum of a separably closed field `Ω`, then the vanishing locus
of every section of `t^* G` is closed (and open): étale locally such a section is the pullback
of a section of the pullback of `G` to `Spec Ω`, and the latter vanishes as soon as it vanishes
at the unique point of `Spec Ω`
(`AlgebraicGeometry.Etale.isClosed_vanishingLocus_of_eq_comp`).

As a consequence, for a geometrically connected `q : T ⟶ X` with a section `σ`, a section of
`q^* G` over the base change of `X` which vanishes along `σ` vanishes, since its restriction
to every geometric fibre of `q` is a section with clopen and nonempty vanishing locus on a
connected scheme (`AlgebraicGeometry.Etale.eq_zero_of_restrictAlong_eq_zero_of_section`).
Hence the pullback map on sections along `q` is surjective
(`AlgebraicGeometry.Etale.surjective_unit_app_of_section`); it is injective as soon as `q`
is surjective (`AlgebraicGeometry.Etale.injective_unit_app_of_surjective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section RestrictAlong

variable {R T T' : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  (f : T' ⟶ T) (t' : T' ⟶ R) (ht' : t' = f ≫ t)

/-- The vanishing locus of the restriction of `s` along `m` is contained in the preimage of
the vanishing locus of `s`. -/
lemma vanishingLocus_restrictAlong_subset {V : T.Etale} {V' : T'.Etale}
    (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f)
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    vanishingLocus _ (restrictAlong t G f t' ht' m hm s) ⊆
      m ⁻¹' vanishingLocus ((t)^*[AddCommGrpCat.{u + 1}].obj G) s := by
  rintro _ ⟨W, b, ⟨w, rfl⟩, hb⟩
  rw [map_restrictAlong] at hb
  have := range_subset_vanishingLocus_of_restrictAlong_eq_zero t G f t' ht' _ _ s hb ⟨w, rfl⟩
  simpa using this

/-- `restrictAlong` only depends on the morphism `f`, not on its presentation. -/
lemma restrictAlong_congr_left {f₁ f₂ : T' ⟶ T} (hf : f₁ = f₂) (ht₁ : t' = f₁ ≫ t)
    {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f₁) :
    restrictAlong t G f₁ t' ht₁ m hm = restrictAlong t G f₂ t' (hf ▸ ht₁) m (hf ▸ hm) := by
  subst hf
  rfl

end RestrictAlong

section SepClosed

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : T ⟶ Spec (.of Ω)) (h : Spec (.of Ω) ⟶ R)
  (hgh : t = g ≫ h)

set_option backward.isDefEq.respectTransparency false in
include hgh in
/-- **Vanishing loci over a geometric point are closed.** If `t : T ⟶ R` factors through the
spectrum of a separably closed field, then the vanishing locus of every section of `t^* G`
is closed. Étale locally around a point, such a section is the restriction of a section of
the pullback of `G` to `Spec Ω`, which vanishes as soon as it vanishes somewhere. -/
lemma isClosed_vanishingLocus_of_eq_comp {V : T.Etale}
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    IsClosed (vanishingLocus _ s) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  obtain ⟨V₁, e, U, φ, hφ, c, ⟨v₀, hv₀⟩, hs⟩ := exists_pullSection_eq t G s z
  have : AlgebraicGeometry.Etale U.hom := U.prop
  let φ' : V₁.left ⟶ pullback U.hom h :=
    pullback.lift φ (V₁.hom ≫ g) (by rw [hφ, hgh, Category.assoc])
  obtain ⟨l, hl, hlv⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (pullback.snd U.hom h)
    (𝟙 _) (φ' v₀) (Subsingleton.elim _ _)
  -- the étale `Spec Ω`-schemes `U ×_R Spec Ω` and `Spec Ω`
  let P : (Spec (.of Ω)).Etale := Scheme.Etale.mk (pullback.snd U.hom h)
  let O : (Spec (.of Ω)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let la : O ⟶ P := MorphismProperty.Over.homMk l hl
  let lam : Spec (.of Ω) ⟶ U.left := l ≫ pullback.fst U.hom h
  have hlam : lam ≫ U.hom = O.hom ≫ h := by
    simp only [lam, Category.assoc, pullback.condition, O]
    rw [reassoc_of% hl]
    exact (Category.id_comp h).symm
  let c' := pullSection h G (V := O) lam hlam c
  let V₂ : T.Etale := pullbackObj (V := P) φ' la
  let b : V₂ ⟶ V := pullbackObjFst (V := P) φ' la ≫ e
  have hm : pullback.snd φ' la.left ≫ O.hom = V₂.hom ≫ g := by
    change pullback.snd φ' l ≫ 𝟙 _ = (pullback.fst φ' l ≫ V₁.hom) ≫ g
    rw [Category.comp_id, Category.assoc, ← pullback.lift_snd φ (V₁.hom ≫ g)
      (by rw [hφ, hgh, Category.assoc]), ← Category.assoc]
    change _ = (pullback.fst φ' l ≫ φ') ≫ _
    rw [pullback.condition, Category.assoc, hl, Category.comp_id]
  -- the restriction of `s` to `V₂` is the restriction of `c'`
  have hs₂ : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op s =
      restrictAlong h G g t hgh (V := O) (V' := V₂) (pullback.snd φ' la.left) hm c' := by
    rw [restrictAlong_pullSection, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs,
      map_pullSection]
    apply pullSection_congr
    change pullback.fst φ' l ≫ φ = pullback.snd φ' l ≫ l ≫ pullback.fst U.hom h
    rw [← pullback.condition_assoc]
    simp [φ']
  -- `c'` vanishes as soon as the restriction of `s` to `V₂` vanishes somewhere
  have key : (vanishingLocus _ (((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op s)).Nonempty →
      ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op s = 0 := by
    rintro ⟨w, hw⟩
    rw [hs₂] at hw ⊢
    have hc : c' = 0 := by
      refine eq_zero_of_forall_mem_vanishingLocus fun x ↦ ?_
      have := vanishingLocus_restrictAlong_subset h G g t hgh _ hm c' hw
      rwa [show x = pullback.snd φ' la.left w from Subsingleton.elim (α := Spec (.of Ω)) _ _]
    rw [hc, map_zero]
  -- a point of `V₂` over `z`
  obtain ⟨w₀, hw₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ') (g := la.left) v₀
    (default : Spec (.of Ω)) hlv.symm
  have hz' : z = b.left w₀ := by
    change z = e.left (pullback.fst φ' la.left w₀)
    rw [hw₀, hv₀]
  -- the image of `V₂` is an open neighbourhood of `z` meeting the vanishing locus of `s`
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := mem_closure_iff.1 hz _ b.left.isOpenMap.isOpen_range ⟨w₀, hz'.symm⟩
  have h₀ := key ⟨w, by rw [vanishingLocus_map]; exact hw⟩
  rw [hz']
  exact mem_vanishingLocus_of_map_eq_zero b h₀ w₀

end SepClosed

end AlgebraicGeometry.Etale
