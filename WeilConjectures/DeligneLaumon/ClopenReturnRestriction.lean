/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstantFieldRestriction
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.DeligneLaumon.ClopenReturnData
import WeilConjectures.DeligneLaumon.ClopenReturnStalk
import WeilConjectures.DeligneLaumon.ClopenReturnSubobject

/-! # Return restriction to a specified clopen geometric component

Source: the geometric-socle and Frobenius-return step of `sk-i-dl-general-real`.
(blueprint: lem-zl-clopen-return-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

/-- Return restriction for a supplied clopen component over its constant field.
This constructs no support scheme and requires no positive dimension.

Source: blueprint `sk-i-dl-general-real`, first proof step (Frobenius orbit), and
`thm-zl-real-mixed-by-curves`, paragraphs 1--3 (local return powers).
(blueprint: lem-zl-clopen-return-restriction).

Proof: Write r = [k₁:k₀]. The geometric fiber of the clopen image of C, considered
as a k₀-scheme, is the disjoint union of r copies of the geometric fiber of C.
Geometric q-Frobenius permutes these cyclically. Restrict the carrier to the sheet
specified by the embedding k₁ into its algebraic closure, using an identification
of the closures over k₀. Give it the r-fold iterate of the original Weil map.
Pullback preserves constructibility and lissity and is exact, so this defines R
on the whole source constructible category. A lisse subobject of R(V) induces,
by its r Frobenius translates and extension by zero outside the clopen image, a
lisse subobject of V. A nonzero stalk in this image ensures R(V) is nonzero.
Simplicity of V therefore says every such subobject is zero or all of R(V).
For a closed z put z₀=c(z). Because c is an open immersion its residue field map
is an isomorphism, so the residue sizes agree (the transport exponent is one).
The r-fold return at z has exactly as many original Frobenius steps as the return
at z₀. Pullback composition and naturality of point transport identify them.
Changing the compatible geometric stalk choices conjugates the operators and
produces the required Frobenius-module equivalence, for every constructible F.
For r=1 this is ordinary restriction to a clopen subset; no semisimplicity is used. -/
theorem exists_clopen_return_restriction
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₁))]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₁))]
    (c : C ⟶ X) [IsOpenImmersion c] [IsClosedImmersion c]
    (hc : c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
      (C ↘ Spec (CommRingCat.of k₁)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) :
    ∃ (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C)
      (_ : PreservesFiniteLimits R) (_ : PreservesFiniteColimits R),
      (∀ F : WeilSheaf k₀ l X, F.IsLisse → (R.obj F).IsLisse) ∧
      HasPointwisePowerTransport R c ∧
      ∀ (V : WeilSheaf k₀ l X), V.IsIrreducibleLisse →
        ∀ z : C.finitePoints,
          Nontrivial (V.stalk ⟨c z.1, Scheme.Hom.map_mem_finitePoints c z.2⟩).carrier →
          (R.obj V).IsIrreducibleLisse := by
  classical
  let : Algebra.IsAlgebraic k₀ k₁ := Algebra.IsAlgebraic.of_finite k₀ k₁
  let r := Module.finrank k₀ k₁
  have hcard : Nat.card k₁ = Nat.card k₀ ^ r := Module.natCard_eq_pow_finrank
  obtain ⟨v, hp, hb, hv⟩ := exists_clopen_return_geometric_map c hc r hcard
  let R := poweredGeometricPullback (l := l) v r hv
  have hR : HasPointwisePowerTransport R c := by
    intro z
    exact poweredGeometricPullback_stalkEquiv r hcard
      (algebraicClosureAlgEquiv k₀ k₁).symm.toRingEquiv c v hp hv z
  refine ⟨R, inferInstance, inferInstance,
    (fun F hF ↦ poweredGeometricPullback_isLisse v r hv hF), hR, ?_⟩
  intro V hV z hz
  have hRV : (R.obj V).IsLisse := poweredGeometricPullback_isLisse v r hv hV.1
  have hnRV : ¬ IsZero (R.obj V) := by
    intro hzero
    obtain ⟨x, e, hx, _, _, hE⟩ := hR z
    have hxp : x = ⟨c z.1, Scheme.Hom.map_mem_finitePoints c z.2⟩ :=
      Subtype.ext hx.symm
    subst x
    obtain ⟨E⟩ := hE V
    have hst : IsZero ((R.obj V).stalkObj
        ((C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint z)) :=
      (stalkFunctor k₁ l _).map_isZero hzero
    have hsub : Subsingleton ((R.obj V).stalk z).carrier :=
      ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero hst)
    let := hz
    obtain ⟨a, b, hab⟩ := exists_pair_ne
      (V.stalk ⟨c z.1, Scheme.Hom.map_mem_finitePoints c z.2⟩).carrier
    exact hab (E.toLinearEquiv.injective (hsub.elim _ _))
  refine ⟨hRV, hnRV, fun G i hi hG ↦ ?_⟩
  let := hi
  obtain ⟨U, j, hj, hU, e, he⟩ :=
    exists_lisse_subobject_clopen_return c hc r hcard v hp hb hv V hV.1 G hG i
  obtain hzero | hiso := hV.2.2 U j hj hU
  · exact Or.inl ((R.map_isZero hzero).of_iso e.symm)
  · let := hiso
    have hmap : IsIso (R.map j) := inferInstance
    have : IsIso (e.hom ≫ i) := he ▸ hmap
    exact Or.inr (IsIso.of_isIso_comp_left e.hom i)

end AlgebraicGeometry.WeilSheaf
