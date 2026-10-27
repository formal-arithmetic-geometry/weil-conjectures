module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Saturation of the supported-section quotient

Source: Stacks Project, Properties, Tag 07ZP, proof of (3), and Divisors, Tag 080D (1).
The residual-support assertion follows by affine lifting and sheaf uniqueness.
(blueprint: lem-trf-supported-quotient-saturation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Quotienting by all sections vanishing on an open leaves no such sections.

Source: Stacks Project, Properties, Tag 07ZP, restriction-kernel sequence in the proof
of (3); Divisors, Tag 080D (1), strict-transform quotient.
(blueprint: lem-trf-supported-quotient-saturation).

The subsheaf is represented by the monomorphism `i`; `hK` identifies its sections
inside `H` with the kernel of restriction to `W ⊓ V`. No compactness is assumed.

Proof:
1. Apply lem-weil-pbc-quasi-coherent-module-cokernel-image to `i`. Both inputs are
quasi-coherent, so the cokernel is quasi-coherent, its projection is epi and is
surjective on every affine open, and its kernel consists of sections locally in
`i`'s image.
2. By `hK`, a section locally in this image restricts locally to zero on `W ⊓ V`.
Sheaf uniqueness makes that restriction zero everywhere, and `hK` puts the section
in the image of `i` on `W`. Conversely every section in this image is killed by
the cokernel projection. This gives the asserted sectionwise kernel equivalence.
3. On any open contained in `V`, the supported subsheaf is zero. The projection is
therefore injective on its sections. Lift a quotient section over an affine cover;
the lifts agree on overlaps by this injectivity and glue uniquely. These inverses
commute with restriction and are linear, making the restricted projection an isomorphism.
4. If a quotient section vanishes on `W ⊓ V`, lift it over each affine open in `W`.
The lift vanishes on its intersection with `V` by step 3, hence belongs to `K` by
`hK`, and its image is zero by step 2. Sheaf uniqueness gives zero on `W`.
Applying this to differences makes every component of the canonical restriction
unit injective, so the unit to the pushforward of the restriction is a monomorphism. -/
theorem supportedQuotientSaturation {Y : Scheme.{u}} (V : Y.Opens)
    {H K : Y.Modules} (i : K ⟶ H) [Mono i]
    [H.IsQuasicoherent] [K.IsQuasicoherent]
    (hK : ∀ (W : Y.Opens) (s : Γ(H, W)),
      s ∈ Set.range (i.app W) ↔
        H.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s = 0) :
    (cokernel i).IsQuasicoherent ∧
    Epi (cokernel.π i) ∧
    (∀ (W : Y.Opens) (s : Γ(H, W)),
      (cokernel.π i).app W s = 0 ↔ s ∈ Set.range (i.app W)) ∧
    (∀ W : Y.affineOpens, Function.Surjective ((cokernel.π i).app W.1)) ∧
    IsIso ((restrictFunctor V.ι).map (cokernel.π i)) ∧
    (∀ (W : Y.Opens) (t : Γ(cokernel i, W)),
      (cokernel i).presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op t = 0 →
        t = 0) ∧
    Mono ((restrictAdjunction V.ι).unit.app (cokernel i)) := by
  classical
  let Q : Y.Modules := cokernel i
  let q : H ⟶ Q := cokernel.π i
  obtain ⟨_, hr, _, _, hepi, _, hqc, _, haff⟩ := quasiCoherent_cokernel_image i
  have hker (W : Y.Opens) (s : Γ(H, W)) :
      q.app W s = 0 ↔ s ∈ Set.range (i.app W) := by
    have hf := ConcreteCategory.bijective_of_isIso ((Abelian.factorThruImage i).app W)
    constructor
    · intro hs
      have hs' : s ∈ LinearMap.ker (q.val.app (op W)).hom := hs
      rw [← hr W] at hs'
      obtain ⟨t, ht⟩ := hs'
      obtain ⟨a, rfl⟩ := hf.2 t
      refine ⟨a, ?_⟩
      rw [← Abelian.image.fac i, Hom.comp_app, ConcreteCategory.comp_apply]
      exact ht
    · rintro ⟨a, rfl⟩
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, cokernel.condition, Hom.zero_app]
      rfl
  have hzero (W : Y.Opens) (hW : W ≤ V) (s : Γ(H, W))
      (hs : q.app W s = 0) : s = 0 := by
    have h := (hK W s).mp ((hker W s).mp hs)
    let r : W ⟶ W ⊓ V := homOfLE (le_inf le_rfl hW)
    have hh := congrArg (H.presheaf.map r.op) h
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (r ≫ homOfLE inf_le_left) (𝟙 W), op_id, CategoryTheory.Functor.map_id] at hh
    simpa using hh
  have hinj (W : Y.Opens) (hW : W ≤ V) :
      Function.Injective (q.app W) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hzero W hW
    rw [map_sub, hab, sub_self]
  have hresmono : Mono ((restrictFunctor V.ι).map q) := by
    constructor
    intro Z a b hab
    apply hom_ext
    intro W
    ext s
    apply hinj (V.ι ''ᵁ W) (V.ι_image_le W)
    exact congrArg (fun f ↦ f.app W s) hab
  have hres : IsIso ((restrictFunctor V.ι).map q) := by
    let := hepi
    let := hresmono
    exact isIso_of_mono_of_epi _
  have res_comp {A B C : Y.Opens} (f : A ⟶ B) (g : B ⟶ C) (s : Γ(Q, C)) :
      Q.presheaf.map f.op (Q.presheaf.map g.op s) = Q.presheaf.map (f ≫ g).op s := by
    rw [op_comp, Functor.map_comp]
    rfl
  have hsat (W : Y.Opens) (t : Γ(Q, W))
      (ht : Q.presheaf.map
        (homOfLE (inf_le_left : W ⊓ V ≤ W)).op t = 0) : t = 0 := by
    have key (x : W) : ∃ U : Y.affineOpens, x.1 ∈ U.1 ∧ U.1 ≤ W := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.2
      exact ⟨⟨U, hU⟩, hxU, hUW⟩
    choose U hxU hUW using key
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨Q.presheaf,
      Q.isSheaf⟩ (fun x ↦ (U x).1) W (fun x ↦ homOfLE (hUW x))
      (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU _⟩) _ _ ?_
    intro x
    obtain ⟨s, hs⟩ := (haff (U x)).2.1
      (Q.presheaf.map (homOfLE (hUW x)).op t)
    have hsz : H.presheaf.map
        (homOfLE (inf_le_left : (U x).1 ⊓ V ≤ (U x).1)).op s = 0 := by
      apply hzero _ inf_le_right
      rw [show q.app ((U x).1 ⊓ V)
          (H.presheaf.map (homOfLE inf_le_left).op s) =
          Q.presheaf.map (homOfLE inf_le_left).op
            (q.app (U x).1 s) from
        PresheafOfModules.naturality_apply q.val _ s, hs]
      have hc := congrArg (Q.presheaf.map
        (homOfLE (inf_le_inf (hUW x) le_rfl)).op) ht
      rw [res_comp]
      rw [res_comp, map_zero] at hc
      exact hc
    have hz := (hker (U x).1 s).mpr ((hK (U x).1 s).mpr hsz)
    rw [hs] at hz
    simpa using hz
  have hunitzero (W : Y.Opens) (t : Γ(Q, W))
      (ht : (((restrictAdjunction V.ι).unit.app Q).app W) t = 0) : t = 0 := by
    apply hsat W t
    have he : W ⊓ V ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact le_inf inf_le_right inf_le_left
    change Q.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op t = 0 at ht
    have hh := congrArg (Q.presheaf.map (homOfLE he).op) ht
    rw [res_comp, map_zero] at hh
    exact hh
  refine ⟨hqc, hepi, hker, fun W ↦ (haff W).2.1, hres, hsat, ?_⟩
  constructor
  intro Z a b hab
  apply hom_ext
  intro W
  ext s
  apply sub_eq_zero.mp
  apply hunitzero W
  rw [map_sub]
  have hh := congrArg (fun f ↦ f.app W s) hab
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, sub_eq_zero] using hh

end AlgebraicGeometry.Scheme.Modules
