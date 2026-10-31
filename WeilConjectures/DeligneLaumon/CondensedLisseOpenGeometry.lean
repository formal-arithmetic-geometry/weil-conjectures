/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
import WeilConjectures.DeligneLaumon.CondensedLinePullCoherence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-! # Dimensions and empty opens in condensed lisse duality

Source: Step 2 of thm-a1-curve-perverse-heart, smooth opens.
(blueprint: lem-per-condensed-lisse-open-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual

private theorem comp_eqToHom_heq {C : Type*} [Category* C] {X Y Z : C}
    (h : Y = Z) (f : X ⟶ Y) : HEq (f ≫ eqToHom h) f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

private theorem isZero_hom_heq {C : Type*} [Category* C] {X Y Z : C}
    (hX : IsZero X) (h : Y = Z) (f : X ⟶ Y) (g : X ⟶ Z) : HEq f g := by
  cases h
  exact (hX.eq_of_src f g).heq

/-- An open map compatible with a base-field automorphism preserves the dimension
unless its source is empty. Source: smooth-open clause of Step 2
(blueprint: lem-per-condensed-lisse-open-geometry).

Proof: an open immersion is smooth of relative dimension zero. Its composite
with the target structure map has the target dimension. A base isomorphism does
not alter smooth relative dimension. Thus both claimed dimensions are relative
dimensions of the same map from a nonempty scheme to a field spectrum, so the
uniqueness theorem for smooth relative dimension makes them equal.
-/
theorem open_dimensions_eq {k : Type u} [Field k] {V T : Space k}
    [Nonempty V.scheme] (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
    (h : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom) :
    V.dim = T.dim := by
  obtain ⟨b, hb⟩ := h
  have hs : SmoothOfRelativeDimension T.dim.val (j ≫ T.map) := by
    have : SmoothOfRelativeDimension (0 + T.dim.val) (j ≫ T.map) := inferInstance
    simpa only [zero_add] using this
  rw [hb] at hs
  have hs' : SmoothOfRelativeDimension T.dim.val V.map :=
    (MorphismProperty.cancel_right_of_respectsIso
      (P := @SmoothOfRelativeDimension T.dim.val) V.map b.hom).mp hs
  exact Fin.ext (SmoothOfRelativeDimension.eq_of_field V.map inferInstance hs')

/-- Every ordinary derived condensed module on an empty scheme is zero.
Source: empty-open case of Step 2
(blueprint: lem-per-condensed-lisse-open-geometry).

Proof: every object of the small pro-etale site maps to the empty scheme and is
empty, so the empty-cover sheaf condition makes each module zero. The derived
category of a zero abelian category is zero, by homology detection.
-/
theorem isZero_empty (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)
    (T : Scheme.{u}) [IsEmpty T] (K : D ell c T) : IsZero K :=
  CondensedRing.isZero_derivedCategory_of_isEmpty' (c.obj ell) K

/-- Existence of individual root-normalized shifted line comparisons on compatible opens.
Source: Step 2, root-normalized restriction of smooth orientation
(blueprint: lem-per-condensed-lisse-open-geometry).

Proof: invertibility of ell descends from the field to every residue field.
Choose the normalized root coordinate and use its shifted derived line map after
inverse total-versus-exact pullback. A nonempty open has the same relative
dimension as its target, so transport the endpoint along that equality. Every
other coordinate equals the chosen one by uniqueness. On an empty source both
objects are zero and every map between them is equal; this also covers different
dimension labels on empty schemes. No composition assertion is used here.
-/
theorem open_line_normalized_exists (ell : ℕ) [Fact ell.Prime]
    (c : PurityTransport.Coefficient ell) (k : Type u) [Field k]
    (hEll : IsUnit (ell : k)) :
    ∃ rho : ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j],
      (∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom) →
        ((pull ell c j).obj (c.derivedLine ell T.scheme T.dim.val) ≅
          c.derivedLine ell V.scheme V.dim.val),
      ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
        (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
        (q : PurityTransport.LinePullCoordinates ell c j), V.dim = T.dim →
        HEq (rho V T j hj).hom
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (q.derived ell T.dim.val).hom) := by
  classical
  have hInv (S : Space k) : ∀ x : S.scheme, Invertible (ell : S.scheme.residueField x) :=
    fun x ↦ (by simpa using hEll.map (S.map.residueFieldAlgebraMap x) :
      IsUnit (ell : S.scheme.residueField x)).invertible
  have hQ (V T : Space k) (j : V.scheme ⟶ T.scheme) :
      Nonempty (PurityTransport.LinePullCoordinates ell c j) := by
    let := hInv V
    let := hInv T
    exact PurityTransport.linePullCoordinates_nonempty ell c j
  have hR (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
      (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom) :
      ∃ r : ((pull ell c j).obj (c.derivedLine ell T.scheme T.dim.val) ≅
          c.derivedLine ell V.scheme V.dim.val),
        ∀ q : PurityTransport.LinePullCoordinates ell c j, V.dim = T.dim →
          HEq r.hom ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (q.derived ell T.dim.val).hom) := by
    by_cases hV : Nonempty V.scheme
    · let := hV
      have hd := open_dimensions_eq j hj
      obtain ⟨q⟩ := hQ V T j
      let e : c.derivedLine ell V.scheme T.dim.val ≅
          c.derivedLine ell V.scheme V.dim.val :=
        eqToIso (congrArg (fun d : Fin 2 ↦ c.derivedLine ell V.scheme d.val) hd.symm)
      refine ⟨(CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (c.obj ell) j).symm.app _ ≪≫ q.derived ell T.dim.val ≪≫ e, ?_⟩
      intro q' hd'
      have hq : q' = q :=
        (PurityTransport.linePullCoordinates_subsingleton ell c j).elim q' q
      subst q'
      simpa only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
        eqToIso.hom, Category.assoc] using
        comp_eqToHom_heq
          (congrArg (fun d : Fin 2 ↦ c.derivedLine ell V.scheme d.val) hd.symm)
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (q.derived ell T.dim.val).hom)
    · have : IsEmpty V.scheme := not_nonempty_iff.mp hV
      refine ⟨IsZero.iso (isZero_empty ell c V.scheme _) (isZero_empty ell c V.scheme _), ?_⟩
      intro q hd
      exact isZero_hom_heq (isZero_empty ell c V.scheme _)
        (congrArg (fun d : Fin 2 ↦ c.derivedLine ell V.scheme d.val) hd) _ _
  choose rho hrho using hR
  exact ⟨rho, hrho⟩

end AlgebraicGeometry.ProEtale.CondensedLisseDual
