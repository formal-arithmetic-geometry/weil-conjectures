/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Dévissage of the rank-one Thom map

A natural transformation between the two functors in the rank-one Thom statement is an
isomorphism on every Weil sheaf placed in degree zero if and only if it is an isomorphism on all
bounded constructible Weil complexes.  The proof uses the induced standard t-structure,
truncation triangles, and the two-out-of-three property for distinguished triangles.

Source: latest blueprint `thm-pur-rank-one-thom`, Step 3 after the integral reduction.
(blueprint: lem-pur-rank-one-native-devissage)
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- Extend componentwise invertibility from sheaf objects to every bounded Weil complex.

Proof in words.  The standard t-structure on bounded constructible Weil complexes has
truncations with Weil sheaves as its cohomology objects.  A complex with one nonzero
cohomology sheaf is a shift of `toComplex.obj P`, so shift compatibility gives invertibility
of the corresponding component.  For a general finite cohomological interval, apply the
transformation to the truncation triangle; the induction hypothesis gives isomorphisms on the
outer terms, and the two-out-of-three theorem for morphisms of distinguished triangles gives
one on the middle term.  Induction terminates at the zero complex.
(blueprint: lem-pur-rank-one-native-devissage)
-/
theorem WeilComplex.isIso_app_of_isIso_toComplex
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (F G : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ P : WeilSheaf k₀ l X,
      IsIso (τ.app ((WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).obj P))) :
    ∀ K : WeilComplex k₀ l X, IsIso (τ.app K) := by
  let _ : (WeilComplex.objectProperty k₀ l X).HasInducedTStructure
      _root_.DerivedCategory.TStructure.t := .mk' fun K hK n ↦ by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncLE hc n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncGE hc n⟩⟩
  let t := (WeilComplex.objectProperty k₀ l X).tStructure
    _root_.DerivedCategory.TStructure.t
  have hsingle (K : WeilComplex k₀ l X) (b : ℤ)
      (hge : t.IsGE K b) (hle : t.IsLE K b) : IsIso (τ.app K) := by
    have : K.obj.IsGE b := (ObjectProperty.tStructure_isGE_iff _ _ K b).1 hge
    have : K.obj.IsLE b := (ObjectProperty.tStructure_isLE_iff _ _ K b).1 hle
    obtain ⟨A, ⟨e⟩⟩ :=
      _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj b
    let eA : A ≅ ((WeilComplex.homologySheaf b).obj K).obj :=
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app A).symm ≪≫
        (_root_.DerivedCategory.homologyFunctor _ b).mapIso e.symm
    let eK : K ≅ (WeilSheaf.toComplex.obj ((WeilComplex.homologySheaf b).obj K))⟦-b⟧ :=
      ObjectProperty.isoMk _ (e ≪≫ (_root_.DerivedCategory.singleFunctor _ b).mapIso eA ≪≫
        ((_root_.DerivedCategory.singleFunctors _).shiftIso (-b) b 0 (by omega)).symm.app _ ≪≫
        (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (-b)).app
          (WeilSheaf.toComplex.obj ((WeilComplex.homologySheaf b).obj K))).symm)
    apply (NatTrans.isIso_app_iff_of_iso τ eK).2
    rw [NatTrans.app_shift]
    have := hτ ((WeilComplex.homologySheaf b).obj K)
    infer_instance
  have hbounded : ∀ (n : ℕ) (a : ℤ) (K : WeilComplex k₀ l X),
      t.IsGE K a → t.IsLE K (a + n - 1) → IsIso (τ.app K) := by
    intro n
    induction n with
    | zero =>
      intro a K hge hle
      have hz := t.isZero K (a + (0 : ℕ) - 1) a (by omega)
      exact (F.map_isZero hz).isIso (G.map_isZero hz) _
    | succ n ih =>
      intro a K hge hle
      have : t.IsGE K a := hge
      have : t.IsLE K (a + n) := t.isLE_of_le K (a + (n + 1 : ℕ) - 1) _ (by omega)
      let T := (t.triangleLEGE (a + n - 1) (a + n) (by omega)).obj K
      have hT : T ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ K
      have h₁ : t.IsGE T.obj₁ a :=
        inferInstanceAs (t.IsGE ((t.truncLE (a + n - 1)).obj K) a)
      have h₁' : t.IsLE T.obj₁ (a + n - 1) :=
        inferInstanceAs (t.IsLE ((t.truncLE (a + n - 1)).obj K) (a + n - 1))
      have hi₁ := ih a T.obj₁ h₁ h₁'
      have h₃ : t.IsGE T.obj₃ (a + n) :=
        inferInstanceAs (t.IsGE ((t.truncGE (a + n)).obj K) (a + n))
      have h₃' : t.IsLE T.obj₃ (a + n) :=
        inferInstanceAs (t.IsLE ((t.truncGE (a + n)).obj K) (a + n))
      exact NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ τ hT hi₁
        (hsingle T.obj₃ (a + n) h₃ h₃')
  intro K
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  have hge : t.IsGE K a := (ObjectProperty.tStructure_isGE_iff _ _ K a).2 ha
  have hle : t.IsLE K b := (ObjectProperty.tStructure_isLE_iff _ _ K b).2 hb
  exact hbounded (b - a + 1).toNat a K hge (t.isLE_of_le K b _ (by omega))

end AlgebraicGeometry
