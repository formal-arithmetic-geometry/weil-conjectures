/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# The unsharpened spectrum universal property with point and stalk formulas

Source: ILO, Travaux de Gabber, Exposé VIII, Lemma 3.1.8(i), printed p.99,
with 3.1.2--3.1.6, pp.98--99 (blueprint: lem-trf-monoid-spectrum-hom-universal).

Multiplicative notation renders the source's additive notation: `p / a` means `p - a`.
The fraction germ is constructed from the actual local-fraction presheaf and its
sheafification, without choosing a stalk identification or an inverse map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite TopologicalSpace

namespace AlgebraicGeometry.Monoscheme


/-- The ordinary fraction `p / a` as a section of the local-fraction presheaf over `D(a)`.
Source: ILO VIII 3.1.2--3.1.3, p.98
(blueprint: lem-trf-monoid-spectrum-hom-universal). -/
def fractionSection {P : Type u} [CommMonoid P] (p a : P) :
    FineFan.spectrumSections (FineFan.basicOpen a) :=
  ⟨fun _ ↦ Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a)⁻¹,
    ⟨fun x ↦ ⟨p, ⟨a, Submonoid.subset_closure x.2⟩, rfl⟩, fun _ _ ↦ rfl⟩⟩

/-- The canonical germ of `p / a` at a prime outside `a`, using the sheafification unit
and the actual germ map. Source: ILO VIII 3.1.2--3.1.6, pp.98--99
(blueprint: lem-trf-monoid-spectrum-hom-universal). -/
noncomputable def fractionGerm {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) (p a : P) (ha : a ∉ x.carrier) :
    FineFan.stalk (affine P).presheaf x :=
  FineFan.germ (affine P).presheaf (FineFan.basicOpen a) x ha
    (((toSheafify (Opens.grothendieckTopology (FineFan.MonoidPrime P))
      (FineFan.spectrumPresheaf P)).app (op (FineFan.basicOpen a))) (fractionSection p a))

private theorem germ_restrict {X : TopCat.{u}}
    (M : TopCat.Presheaf CommMonCat.{u} X) {U V : Opens X} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) (s : M.obj (op V)) :
    FineFan.germ M U x hx (M.map i.op s) = FineFan.germ M V x (i.le hx) s := by
  exact ConcreteCategory.congr_hom
    (colimit.w (FineFan.stalkDiagram M x)
      (show (op (⟨V, i.le hx⟩ : OpenNhds x)) ⟶ op ⟨U, hx⟩ from i.op)) s

private theorem stalkMap_germ {X Y : SheafedSpace CommMonCat.{u}}
    (f : X ⟶ Y) (U : Opens Y) (x : X) (hx : f.hom.base x ∈ U)
    (s : Y.presheaf.obj (op U)) :
    FineFan.stalkMap f x (FineFan.germ Y.presheaf U (f.hom.base x) hx s) =
      FineFan.germ X.presheaf ((Opens.map f.hom.base).obj U) x hx
        (f.hom.c.app (op U) s) := by
  change (FineFan.germ Y.presheaf U (f.hom.base x) hx ≫ FineFan.stalkMap f x) s =
    (f.hom.c.app (op U) ≫
      FineFan.germ X.presheaf ((Opens.map f.hom.base).obj U) x hx) s
  apply ConcreteCategory.congr_hom
  simp only [FineFan.stalkMap, FineFan.germ, FineFan.stalkDiagram,
    colimit.ι_map_assoc, OpenNhds.inclusionMapIso_inv, NatTrans.op_id]
  change f.hom.c.app (op U) ≫ X.presheaf.map (𝟙 _) ≫
    colimit.ι ((OpenNhds.map f.hom.base x ⋙ OpenNhds.inclusion x).op ⋙ X.presheaf)
      (op (⟨U, hx⟩ : OpenNhds (f.hom.base x))) ≫
    colimit.pre (FineFan.stalkDiagram X.presheaf x) (OpenNhds.map f.hom.base x).op = _
  rw [X.presheaf.map_id]
  erw [Category.id_comp]
  exact congrArg (fun k ↦ f.hom.c.app (op U) ≫ k)
    (colimit.ι_pre (FineFan.stalkDiagram X.presheaf x)
      (OpenNhds.map f.hom.base x).op (op (⟨U, hx⟩ : OpenNhds (f.hom.base x))))

private theorem stalkMap_numerator {P : Type u} [CommMonoid P]
    {T : SheafedSpace CommMonCat.{u}} (f : T ⟶ affine P) (t : T) (p : P) :
    FineFan.stalkMap f t (affineGerm (f.hom.base t) p) =
      FineFan.germ T.presheaf ⊤ t (by trivial) (affinePullback f p) := by
  rw [affineGerm, MonoidHom.comp_apply, stalkMap_germ]
  rfl

private theorem fraction_mul_denominator {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) (p a : P) (ha : a ∉ x.carrier) :
    fractionGerm x p a ha * affineGerm x a = affineGerm x p := by
  let U := FineFan.basicOpen a
  let i : U ⟶ ⊤ := homOfLE le_top
  let η := toSheafify (Opens.grothendieckTopology (FineFan.MonoidPrime P))
    (FineFan.spectrumPresheaf P)
  have hn (q : P) :
      FineFan.germ (affine P).presheaf U x ha
        (η.app (op U) ((FineFan.spectrumPresheaf P).map i.op (FineFan.numerator P q))) =
      affineGerm x q := by
    have h := ConcreteCategory.congr_hom (η.naturality i.op) (FineFan.numerator P q)
    exact (congrArg (FineFan.germ (affine P).presheaf U x ha) h).trans
      (germ_restrict (affine P).presheaf i x ha (affineSection P q))
  let z : (FineFan.spectrumPresheaf P).obj (op U) := fractionSection p a
  have he : z *
      (FineFan.spectrumPresheaf P).map i.op (FineFan.numerator P a) =
      (FineFan.spectrumPresheaf P).map i.op (FineFan.numerator P p) := by
    apply Subtype.ext
    funext y
    change (Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a)⁻¹) *
      Algebra.GrothendieckGroup.of a = Algebra.GrothendieckGroup.of p
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  calc
    fractionGerm x p a ha * affineGerm x a =
        FineFan.germ (affine P).presheaf U x ha
          (η.app (op U) (z *
            (FineFan.spectrumPresheaf P).map i.op (FineFan.numerator P a))) := by
      rw [(η.app (op U)).hom.map_mul, (FineFan.germ (affine P).presheaf U x ha).hom.map_mul]
      rw [hn a]
      rfl
    _ = affineGerm x p := by rw [he]; exact hn p

private def localizationNumerator {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) (p : P) :
    Algebra.faceLocalization P (Submonoid.closure {a : P | a ∉ x.carrier}) :=
  ⟨Algebra.GrothendieckGroup.of p, ⟨p, ⟨1, Submonoid.one_mem _⟩, by simp⟩⟩

private def sectionEvaluation {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) (U : Opens (FineFan.MonoidPrime P)) (hx : x ∈ U) :
    FineFan.spectrumSections U →*
      Algebra.faceLocalization P (Submonoid.closure {a : P | a ∉ x.carrier}) where
  toFun s := ⟨s.1 ⟨x, hx⟩, s.2.1 ⟨x, hx⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

open Classical in
private noncomputable def spectrumEvaluation {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) :
    FineFan.spectrumPresheaf P ⟶
      skyscraperPresheaf (X := TopCat.of (FineFan.MonoidPrime P)) x
        (CommMonCat.of (Algebra.faceLocalization P
          (Submonoid.closure {a : P | a ∉ x.carrier}))) := by
  classical
  refine { app := fun U ↦ ?_, naturality := ?_ }
  · exact if hx : x ∈ U.unop then
      CommMonCat.ofHom (sectionEvaluation x U.unop hx) ≫ eqToHom (if_pos hx).symm
    else ((if_neg hx).symm.ndrec terminalIsTerminal).from _
  · intro U V i
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := i.unop.le hV
      change (FineFan.spectrumPresheaf P).map i ≫ _ = _
      dsimp only [FineFan.spectrumPresheaf, Functor.const_obj_map]
      rw [dif_pos hV, dif_pos hU, skyscraperPresheaf_map, dif_pos hV]
      simp only [Category.assoc, eqToHom_trans]
      rw [← Category.assoc]
      apply (cancel_mono _).2
      rfl
    · exact ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext _ _

open Classical in
private noncomputable def sheafEvaluation {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) :
    (affine P).presheaf ⟶
      skyscraperPresheaf (X := TopCat.of (FineFan.MonoidPrime P)) x
        (CommMonCat.of (Algebra.faceLocalization P
          (Submonoid.closure {a : P | a ∉ x.carrier}))) := by
  classical
  exact sheafifyLift (Opens.grothendieckTopology (FineFan.MonoidPrime P))
    (spectrumEvaluation x)
    (skyscraperPresheaf_isSheaf (X := TopCat.of (FineFan.MonoidPrime P)) x
      (CommMonCat.of (Algebra.faceLocalization P
        (Submonoid.closure {a : P | a ∉ x.carrier}))))

open Classical in
private noncomputable def stalkToSkyscraper {X : TopCat.{u}}
    (M : TopCat.Presheaf CommMonCat.{u} X) (x : X) (A : CommMonCat.{u})
    (α : M ⟶ skyscraperPresheaf x A) : FineFan.stalk M x ⟶ A :=
  colimit.desc _ (Cocone.mk A
    { app := fun U ↦ α.app ((OpenNhds.inclusion x).op.obj U) ≫
        eqToHom (if_pos U.unop.2)
      naturality := fun U V i ↦ by
        dsimp only [FineFan.stalkDiagram, Functor.const_obj_map, Functor.const_obj_obj,
          Functor.comp_map, Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj]
        rw [Category.comp_id, ← Category.assoc, comp_eqToHom_iff, Category.assoc,
          eqToHom_trans, α.naturality, skyscraperPresheaf_map]
        have hV : x ∈ (OpenNhds.inclusion x).obj V.unop := V.unop.2
        simp only [dif_pos hV] })

open Classical in
private theorem germ_stalkToSkyscraper {X : TopCat.{u}}
    (M : TopCat.Presheaf CommMonCat.{u} X) (x : X) (A : CommMonCat.{u})
    (α : M ⟶ skyscraperPresheaf x A) (U : Opens X) (hx : x ∈ U) :
    FineFan.germ M U x hx ≫ stalkToSkyscraper M x A α =
      α.app (op U) ≫ eqToHom (if_pos hx) :=
  colimit.ι_desc _ _

private noncomputable def stalkEvaluation {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) :
    FineFan.stalk (affine P).presheaf x ⟶
      CommMonCat.of (Algebra.faceLocalization P
        (Submonoid.closure {a : P | a ∉ x.carrier})) := by
  classical
  exact stalkToSkyscraper (affine P).presheaf x _ (sheafEvaluation x)

private theorem stalkEvaluation_numerator {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) (p : P) :
    stalkEvaluation x (affineGerm x p) = localizationNumerator x p := by
  classical
  change (FineFan.germ (affine P).presheaf ⊤ x (by trivial) ≫ stalkEvaluation x)
    (affineSection P p) = _
  rw [stalkEvaluation, germ_stalkToSkyscraper]
  change ((toSheafify (Opens.grothendieckTopology (FineFan.MonoidPrime P))
    (FineFan.spectrumPresheaf P)).app (op ⊤) ≫
      (sheafEvaluation x).app (op ⊤) ≫ eqToHom (if_pos (show x ∈ (⊤ : Opens _) by trivial)))
        (FineFan.numerator P p) = _
  rw [← Category.assoc]
  have h := congrArg (fun α ↦ α.app (op (⊤ : Opens (FineFan.MonoidPrime P))))
    (toSheafify_sheafifyLift (Opens.grothendieckTopology (FineFan.MonoidPrime P))
      (spectrumEvaluation x)
      (skyscraperPresheaf_isSheaf (X := TopCat.of (FineFan.MonoidPrime P)) x
      (CommMonCat.of (Algebra.faceLocalization P
        (Submonoid.closure {a : P | a ∉ x.carrier})))))
  change (toSheafify (Opens.grothendieckTopology (FineFan.MonoidPrime P))
    (FineFan.spectrumPresheaf P)).app (op ⊤) ≫
    (sheafEvaluation x).app (op ⊤) = (spectrumEvaluation x).app (op ⊤) at h
  dsimp only [affine] at *
  rw [h]
  simp only [spectrumEvaluation, dif_pos (show x ∈ (⊤ : Opens _) by trivial),
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

private theorem numerator_isUnit_iff {P : Type u} [CommMonoid P]
    (hP : FineFan.IsFine P) (x : FineFan.MonoidPrime P) (p : P) :
    IsUnit (affineGerm x p) ↔ p ∉ x.carrier := by
  constructor
  · intro hp
    have hl : IsUnit (localizationNumerator x p) := by
      rw [← stalkEvaluation_numerator]
      exact hp.map (stalkEvaluation x).hom
    obtain ⟨v, hv⟩ := hl
    obtain ⟨q, f, hf⟩ := (v⁻¹).val.property
    have he : Algebra.GrothendieckGroup.of (p * q) = Algebra.GrothendieckGroup.of f.1 := by
      have hm := congrArg Subtype.val v.val_inv
      rw [hv] at hm
      change Algebra.GrothendieckGroup.of p * ((v⁻¹).val :
        Algebra.faceLocalization P (Submonoid.closure {a : P | a ∉ x.carrier})).val = 1 at hm
      rw [hf] at hm
      rw [← mul_assoc, mul_inv_eq_one] at hm
      simpa only [map_mul] using hm
    have heq : p * q = f.1 := hP.2 he
    have h1 : (1 : P) ∉ x.carrier := by
      intro h
      apply x.proper
      apply Set.eq_univ_of_forall
      intro a
      have ha := SemigroupIdeal.mul_mem x.toSubMulAction a h
      change a * 1 ∈ x.carrier at ha
      simpa only [mul_one] using ha
    have hface : ∀ a ∈ Submonoid.closure {b : P | b ∉ x.carrier}, a ∉ x.carrier := by
      intro a ha
      induction ha using Submonoid.closure_induction with
      | mem a ha => exact ha
      | one => exact h1
      | mul a b _ _ ha hb => exact x.complement_mul a b ha hb
    intro hp'
    apply hface f.1 f.2
    rw [← heq, mul_comm]
    exact SemigroupIdeal.mul_mem x.toSubMulAction q hp'
  · intro hp
    have he := fraction_mul_denominator x 1 p hp
    rw [map_one] at he
    exact isUnit_iff_exists_inv.mpr ⟨fractionGerm x 1 p hp, by rwa [mul_comm]⟩

/-- Pullback of canonical sections is a bijection, natural in both variables, with
its explicit nonunit-prime and localized stalk formulas. In the last clause `v` is
any unit whose value is the denominator germ; its inverse is uniquely determined.
Thus this states the fraction formula even when the target stalk is not integral.

Source: ILO VIII Lemma 3.1.8(i), p.99, with 3.1.2--3.1.6, pp.98--99
(blueprint: lem-trf-monoid-spectrum-hom-universal).

Proof: (1) Apply lem-trf-affine-monoscheme-hom-universal to obtain the bijection by
canonical numerator pullback and both naturalities, for the unsharpened monoid sheaf.
(2) For a prime q, lem-trf-monoid-prime-minimal-neighborhood identifies the smallest
neighborhood D(b) and its sections with P localized at the complementary face. Germs
are therefore those fractions, and a numerator is a unit precisely outside q.
(3) Compatibility with germs sends each canonical p to the germ of rho(p). Locality
then says that rho(p) has nonunit germ at t exactly when p belongs to the image prime.
This recovers the displayed point map, including the empty prime.
(4) For a denominator outside that prime, its germ is a unit. The stalk homomorphism
preserves multiplication and inverses, hence sends the canonical fraction p/a to the
germ of rho(p) multiplied by the inverse of the germ of rho(a). This gives the last
formula for every representing unit v. No sharpness or torsion-freeness is used. -/
theorem spectrum_hom_universal (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P) :
    (∀ T : SheafedSpace CommMonCat.{u},
      Function.Bijective
        (fun f : {f : T ⟶ affine P // FineFan.IsLocalMorphism f} ↦
          (SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P))) ∧
    (∀ (T T' : SheafedSpace CommMonCat.{u})
      (k : {k : T' ⟶ T // FineFan.IsLocalMorphism k})
      (f : {f : T ⟶ affine P // FineFan.IsLocalMorphism f}),
      (SheafedSpace.Γ.map (k.val ≫ f.val).op).hom.comp (affineSection P) =
        (SheafedSpace.Γ.map k.val.op).hom.comp
          ((SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P))) ∧
    (∀ (Q : Type u) [CommMonoid Q], FineFan.IsFine Q → ∀ w : P →* Q,
      ∃! g : {g : affine Q ⟶ affine P // FineFan.IsLocalMorphism g},
        (SheafedSpace.Γ.map g.val.op).hom.comp (affineSection P) =
          (affineSection Q).comp w ∧
        ∀ (T : SheafedSpace CommMonCat.{u})
          (f : {f : T ⟶ affine Q // FineFan.IsLocalMorphism f}),
          (SheafedSpace.Γ.map (f.val ≫ g.val).op).hom.comp (affineSection P) =
            ((SheafedSpace.Γ.map f.val.op).hom.comp (affineSection Q)).comp w) ∧
    (∀ (T : SheafedSpace CommMonCat.{u}) (ρ : P →* T.presheaf.obj (op ⊤))
      (f : {f : T ⟶ affine P // FineFan.IsLocalMorphism f}),
      (SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P) = ρ →
      (∀ (t : T) (p : P), p ∈ (f.val.hom.base t).carrier ↔
        ¬ IsUnit (FineFan.germ T.presheaf ⊤ t (by trivial) (ρ p))) ∧
      (∀ (t : T) (p a : P) (ha : a ∉ (f.val.hom.base t).carrier)
        (v : (FineFan.stalk T.presheaf t)ˣ),
        (v : FineFan.stalk T.presheaf t) =
          FineFan.germ T.presheaf ⊤ t (by trivial) (ρ a) →
        FineFan.stalkMap f.val t (fractionGerm (f.val.hom.base t) p a ha) =
          FineFan.germ T.presheaf ⊤ t (by trivial) (ρ p) *
            ((v⁻¹ : (FineFan.stalk T.presheaf t)ˣ) : FineFan.stalk T.presheaf t))) := by
  obtain ⟨hb, hs, ht⟩ := affine_hom_universal P hP
  refine ⟨hb, hs, ht, ?_⟩
  intro T ρ f hf
  have hn (t : T) (p : P) :
      FineFan.stalkMap f.val t (affineGerm (f.val.hom.base t) p) =
        FineFan.germ T.presheaf ⊤ t (by trivial) (ρ p) := by
    rw [stalkMap_numerator]
    exact congrArg (fun r ↦ FineFan.germ T.presheaf ⊤ t (by trivial) (r p)) hf
  constructor
  · intro t p
    have := f.property t
    rw [← hn t p, isUnit_map_iff (FineFan.stalkMap f.val t).hom,
      numerator_isUnit_iff hP]
    exact not_not.symm
  · intro t p a ha v hv
    have he := congrArg (FineFan.stalkMap f.val t)
      (fraction_mul_denominator (f.val.hom.base t) p a ha)
    rw [(FineFan.stalkMap f.val t).hom.map_mul, hn t a, hn t p, ← hv] at he
    calc
      FineFan.stalkMap f.val t (fractionGerm (f.val.hom.base t) p a ha) =
          (FineFan.stalkMap f.val t (fractionGerm (f.val.hom.base t) p a ha) *
            (v : FineFan.stalk T.presheaf t)) * ↑(v⁻¹) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := congrArg (fun z ↦ z * ↑(v⁻¹)) he

end AlgebraicGeometry.Monoscheme
