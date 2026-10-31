/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageWeilIsoPart
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageWeilEqPart

/-! Weil equivariance of the condensed open-image maps.

Source: latest blueprint, p-dl-a1-exact, Step 8
(blueprint: new-dl-a1-weil).

Proof: the model Frobenius maps are automorphisms, so the ordinary base change and the
canonical derived exchange of the Frobenius square are invertible, and every Weil map is
an isomorphism (`condensedOpenImage_weil_isoPart`). The two ordinary squares are the
naturality of the ordinary base change together with the given compatibilities of the
degree-zero Weil isomorphisms. The connecting-map square transports these isomorphisms
through the single short-exact triangle and applies the homology ladder
(`condensedOpenImage_weil_eqPart`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ordinary Weil maps intertwine the direct images of a morphism compatible with
the given Weil structures: naturality of the ordinary base change. -/
private theorem dlOpenImageWeilMap_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    (j : U ⟶ C) (sq : CommSq gU j j gC)
    {M N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)}
    (f : M ⟶ N) (φM : (upperStar Λ gU).obj M ≅ M) (φN : (upperStar Λ gU).obj N ≅ N)
    (hf : (upperStar Λ gU).map f ≫ φN.hom = φM.hom ≫ f) :
    (upperStar Λ gC).map ((lowerStar Λ j).map f) ≫ dlOpenImageWeilMap Λ j sq N φN =
      dlOpenImageWeilMap Λ j sq M φM ≫ (lowerStar Λ j).map f := by
  have h := (lowerStarBaseChange Λ sq).naturality_assoc f ((lowerStar Λ j).map φN.hom)
  simp only [Functor.comp_map] at h
  simp only [dlOpenImageWeilMap, Category.assoc, h, ← Functor.map_comp, hf]

/-- For a specified Frobenius square, all ordinary, derived and connecting maps in a
constructible short exact sequence satisfy the Weil assertions. -/
theorem condensedOpenImage_weil
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left]
    (sq : CommSq (StrictWeil.modelFrobenius D U₀).hom (dlGeometricOpen D j₀)
      (dlGeometricOpen D j₀) (StrictWeil.modelFrobenius D C₀).hom) :
    DlOpenImageWeilAssertions (Profinite.padicAlgClRingObj ell)
      (dlGeometricOpen D j₀) sq := by
  intro S hS h1 h2 h3 φ1 φ2 φ3 hf hg
  have hi := condensedOpenImage_weil_isoPart D ell _hEll _iota U₀ C₀ j₀ sq
    S hS h1 h2 h3 φ1 φ2 φ3 hf hg
  have hδ := condensedOpenImage_weil_eqPart D ell _hEll _iota U₀ C₀ j₀ sq
    S hS h1 h2 h3 φ1 φ2 φ3 hf hg
  have hfs := dlOpenImageWeilMap_naturality (Profinite.padicAlgClRingObj ell)
    (dlGeometricOpen D j₀) sq S.f φ1 φ2 hf
  have hgs := dlOpenImageWeilMap_naturality (Profinite.padicAlgClRingObj ell)
    (dlGeometricOpen D j₀) sq S.g φ2 φ3 hg
  exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, hfs, hgs, hδ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
