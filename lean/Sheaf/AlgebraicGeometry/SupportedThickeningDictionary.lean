/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.CategoryTheory.Whiskering

/-! # Supported thickening systems and completion isomorphisms
Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-supported-thickening-dictionary).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem extend_pullback_automorphism
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (hε : ∀ H : D, IsIso (adj.counit.app H)) (t : L ≅ L) :
    ∃ s : 𝟭 D ≅ 𝟭 D, ∀ (G : C) (H : D) (ψ : L.obj G ≅ H),
      ψ.hom ≫ s.inv.app H = t.inv.app G ≫ ψ.hom := by
  let := hε
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  let ε := asIso adj.counit
  let s : 𝟭 D ≅ 𝟭 D := ε.symm ≪≫ Functor.isoWhiskerLeft R t ≪≫ ε
  have hs (G : C) : s.inv.app (L.obj G) = t.inv.app G := by
    have htri := adj.left_triangle_components G
    have hunit : L.map (adj.unit.app G) = inv (adj.counit.app (L.obj G)) :=
      (asIso (adj.counit.app (L.obj G))).comp_hom_eq_id.mp htri
    simp only [s, ε, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, asIso_hom, asIso_inv,
      NatIso.isIso_inv_app]
    change (inv (adj.counit.app (L.obj G)) ≫ t.inv.app (R.obj (L.obj G))) ≫
      adj.counit.app (L.obj G) = _
    have hn := t.inv.naturality (adj.unit.app G)
    dsimp only [Functor.comp_obj, Functor.id_obj] at hn
    rw [← hunit, hn, Category.assoc, htri, Category.comp_id]
  refine ⟨s, fun G H ψ ↦ ?_⟩
  simpa only [Functor.id_map, hs G] using s.inv.naturality ψ.hom

private theorem restriction_iso_equation
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {G₁ L₁ F₁ : C} {G₀ L₀ F₀ : D}
    (a : G₁ ≅ L₁) (b : G₀ ≅ L₀) (e₁ : G₁ ⟶ F₁) (e₀ : G₀ ⟶ F₀)
    (q : P.obj G₁ ≅ G₀) (φ : P.obj F₁ ≅ F₀) (σ : F₀ ≅ F₀)
    (d : P.obj L₁ ≅ L₀)
    (hr : q.hom ≫ b.hom = P.map a.hom ≫ d.hom)
    (he : q.hom ≫ e₀ = P.map e₁ ≫ φ.hom ≫ σ.inv) :
    P.map (a.inv ≫ e₁) ≫ φ.hom ≫ σ.inv = d.hom ≫ b.inv ≫ e₀ := by
  apply (cancel_epi (P.map a.hom)).1
  simp only [P.map_comp, Category.assoc]
  rw [← P.map_comp_assoc, a.hom_inv_id, P.map_id, Category.id_comp]
  calc
    _ = q.hom ≫ e₀ := he.symm
    _ = _ := by
      simpa only [Category.assoc, b.hom_inv_id_assoc] using
        congrArg (fun z ↦ z ≫ b.inv ≫ e₀) hr

private theorem remove_normalization
    {C : Type*} [Category C] {L G H : C}
    (d c : L ≅ G) (σ : H ≅ H) (ψ : G ⟶ H) (q : L ⟶ H)
    (hq : q ≫ σ.inv = d.hom ≫ ψ)
    (hψ : ψ ≫ σ.inv = c.inv ≫ d.hom ≫ ψ) : q = c.hom ≫ ψ := by
  apply (cancel_mono σ.inv).1
  rw [Category.assoc, hψ, ← Category.assoc, ← Category.assoc,
    c.hom_inv_id, Category.id_comp]
  exact hq

/-- The annihilation and isomorphism portions of the thickening dictionary.
Source: Stacks Project, Remark 088F, Lemma 087T, and equation 0880.
(blueprint: lem-weil-pbc-supported-thickening-dictionary).
Proof: Apply the thickening-systems dictionary using the canonical tensor-pullback adjunction
choices. At level zero, its kernel formula and the closed-immersion kernel identity identify the
 displayed ideal with the kernel used by the dictionary. For each level, normalize the dictionary
comparison by transporting the automorphism d⁻¹ ≫ c along the invertible counit of the closed
immersion pushforward; the triangle identity proves the required naturality. Apply the dictionary
to the normalized coherent system. Evaluation isomorphisms transport the given sectionwise
annihilation to the formal terms. The affine-cover product-zero criterion at exponent one then
proves SupportedOn. Finally, invert the dictionary's completion comparison and use its evaluation
compatibility; categorical cancellation removes the normalization and yields the requested
transition equation with the original comparison c. -/
theorem supportedThickening_dictionary
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 +
      1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n)))
    (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n)
    (hF : ∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).toRingedSpace (F n))
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hkill : ∀ (n : ℕ) (V : X.Opens) (a : Γ(X, V)),
        a ∈ j.ker.idealOfOpens V →
        ∀ t : Γ((Scheme.Modules.pushforward (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n), V),
          a • t = 0) :
    ∃ hX : IsNoetherian X,
      ∃ M : @CoherentFormalModule X hX
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f),
        @SupportedOn X Z hX
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f) M j _ ∧
        ∀ G : CoherentModules X,
          Nonempty ((@completion X hX
            ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).obj G ≅ M) →
          ∃ ψ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G.obj ≅ F n,
            ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
              (φ n).hom = (c n).hom.app G.obj ≫ (ψ n).hom := by
  classical
  -- The normalization works for every comparison c, including the specified one.
  have _canonicalComparison := hc
  let T (n : ℕ) := pullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let jn (n : ℕ) : T n ⟶ X := pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let ai n := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction (i n))
  let aj n := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction (jn n))
  obtain ⟨hX, hclosed, Φ, β, _, _, d, R, r, _, _, hr, _, _, _, hiso, _, _⟩ :=
    thickeningSystems_dictionary f I i hi hp ai aj
  let : IsNoetherian X := hX
  have hJ : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f) =
      (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f := by
    have hh := (hclosed 0).2
    simp only [Nat.reduceAdd] at hh
    simp only [_root_.pow_one] at hh
    have (K : Ideal A) :
        IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion] at hh
    rw [show I ^ 1 = I from _root_.pow_one I] at hh
    exact hh
  rw [hJ]
  have hnormalize (n : ℕ) : ∃ s : 𝟭 (T n).Modules ≅ 𝟭 (T n).Modules,
      ∀ (G : X.Modules) (H : (T n).Modules)
        (ψ : (Scheme.Modules.tensorPullback (jn n)).obj G ≅ H),
        ψ.hom ≫ s.inv.app H = ((d n).symm ≪≫ c n).inv.app G ≫ ψ.hom := by
    have : IsClosedImmersion (jn n) := (hclosed n).1
    exact extend_pullback_automorphism (aj n)
      (closedImmersion_pushforward_fullyFaithful (jn n)).1 ((d n).symm ≪≫ c n)
  choose s hs using hnormalize
  let S : CoherentThickeningSystem T i :=
    ⟨F, hF, fun n ↦ φ n ≪≫ ((s n).app (F n)).symm⟩
  refine ⟨hX, Φ.obj S, ?_, ?_⟩
  · change ∀ n : ℕ, IsZero (Scheme.idealModuleProduct j.ker.toModulesι
      ((Φ.obj S).obj.obj (Opposite.op n)))
    intro n
    let M := (Φ.obj S).obj.obj (Opposite.op n)
    have : M.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X M).mp
        ((Φ.obj S).property.1 n)).1
    have hcover : ∀ x : X, ∃ U ∈ (Set.univ : Set X.affineOpens), x ∈ U.1 := by
      intro x
      obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨⟨U, hU⟩, Set.mem_univ _, hxU⟩
    have hzero := (Scheme.idealPowerProduct_isZero_iff_affine_cover X M j.ker
      Set.univ hcover 1).mpr
    apply hzero
    intro U _ a ha
    apply Module.mem_annihilator.mpr
    intro t
    have hmem : a ∈ j.ker.idealOfOpens U.1 := by
      simpa only [_root_.pow_one, Scheme.IdealSheafData.idealOfOpens_eq_ideal] using ha
    let e : M ≅ (Scheme.Modules.pushforward (jn n)).obj (F n) := (β n).app S
    have hkill' := hkill n U.1 a hmem ((e.hom.app U.1) t)
    have hinj : Function.Injective (e.hom.app U.1) :=
      (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)).1
    apply hinj
    rw [Scheme.Modules.Hom.app_smul, map_zero]
    exact hkill'
  · intro G he
    obtain ⟨ecomp⟩ := he
    obtain ⟨b, _⟩ := hiso G S
    let e : R.obj G ≅ S := b.symm ecomp
    let ψ (n : ℕ) : (Scheme.Modules.tensorPullback (jn n)).obj G.obj ≅ F n :=
      ((r n).app G).symm ≪≫ (CoherentThickeningSystem.evaluation T i n).mapIso e
    refine ⟨ψ, fun n ↦ ?_⟩
    have heq := e.hom.compatibility n
    have hres := hr G n
    have hnorm := hs n G.obj (F n) (ψ n)
    change (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
      (φ n).hom = (c n).hom.app G.obj ≫ (ψ n).hom
    have hbase : (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (φ n).hom ≫ (s n).inv.app (F n) = (d n).hom.app G.obj ≫ (ψ n).hom :=
      restriction_iso_equation (Scheme.Modules.tensorPullback (i n))
        ((r (n + 1)).app G) ((r n).app G) (e.hom.app (n + 1)) (e.hom.app n)
        ((R.obj G).comparison n) (φ n) ((s n).app (F n)) ((d n).app G.obj)
        hres heq
    exact remove_normalization ((d n).app G.obj) ((c n).app G.obj)
      ((s n).app (F n)) (ψ n).hom
      ((Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫ (φ n).hom)
      hbase hnorm

end AlgebraicGeometry
