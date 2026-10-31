/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedComparisonCoordinates

/-! # The locally closed comparison: a single assembly step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison is the transpose of the inverse named direct-image/open
comparison followed by the image of the pasted etale counit. It is constructed as a
morphism before any invertibility assertion is used.
Source: blueprint locally closed comparison, Steps 4--6
(blueprint: lem-sf-locally-closed-counit-comparison). -/
def locallyClosedCounitMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : LocallyClosedComparisonAdjoints A c)
    (hb : ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
      _root_.DerivedCategory.TStructure.t.plus ((a.etaleRight v).obj M.obj)) :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ a.etaleRight v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⟶
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        a.proetaleRight v where
  app M := (a.proetalePasted v).homEquiv _ _
    ((locallyClosedExtensionComparison A c v).inv.app
        ⟨(a.etaleRight v).obj M.obj, hb M⟩ ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((a.etalePasted v).counit.app M.obj))
  naturality M N f := by
    let CS := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
    let CT := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
    let Fe := locallyClosedEtaleExtension A c v
    let Fp := locallyClosedProEtaleExtension A c v
    let ae := a.etalePasted v
    let ap := a.proetalePasted v
    let delta := locallyClosedExtensionComparison A c v
    let Mf : (⟨(a.etaleRight v).obj M.obj, hb M⟩ : DerivedCategory.Plus _) ⟶
        ⟨(a.etaleRight v).obj N.obj, hb N⟩ :=
      ObjectProperty.homMk ((a.etaleRight v).map f.hom)
    have hn := delta.inv.naturality Mf
    change Fp.map (CS.map ((a.etaleRight v).map f.hom)) ≫ _ =
      _ ≫ CT.map (Fe.map ((a.etaleRight v).map f.hom)) at hn
    change CS.map ((a.etaleRight v).map f.hom) ≫
      ap.homEquiv _ _ (delta.inv.app ⟨(a.etaleRight v).obj N.obj, hb N⟩ ≫
        CT.map (ae.counit.app N.obj)) =
        ap.homEquiv _ _ (delta.inv.app ⟨(a.etaleRight v).obj M.obj, hb M⟩ ≫
          CT.map (ae.counit.app M.obj)) ≫
          (a.proetaleRight v).map (CT.map f.hom)
    rw [← ap.homEquiv_naturality_left, ← ap.homEquiv_naturality_right]
    congr 1
    have he := ae.counit.naturality f.hom
    change Fe.map ((a.etaleRight v).map f.hom) ≫ ae.counit.app N.obj =
      ae.counit.app M.obj ≫ f.hom at he
    rw [← Category.assoc, hn, Category.assoc, ← CT.map_comp]
    erw [he]
    rw [CT.map_comp, Category.assoc]

/-- The canonical counit mate is invertible on bounded constructible inputs.
This assertion supplies no comparison data and no relative Hom or unit equation.
Source: blueprint site-comparison proof, paragraph 2, locally closed sentence;
parent locally closed comparison proof, Steps 1--6
(blueprint: lem-sf-locally-closed-counit-comparison).

Proof: open restriction preserves bounded constructibility by exact inverse image
and constructible pullback. The finite-type hypotheses make S, V and T Noetherian;
choose the quasi-compact complementary open to c in V. Apply finiteDualityClosedComparison
to v^* M, and transport its closed adjoints to a by the unique counit-compatible
adjoint isomorphisms. Use a bounded-below lift of the closed etale exceptional value
in the named Plus direct-image mate; its inclusion isomorphisms and naturality give
precisely the component of fixedDirectImageComparisonIso at that value.
Compose this invertible closed exceptional comparison with the derived open restriction
comparison. Its counit equation follows by the closed counit equation, naturality of
the open extension comparison and derivedImmersionOpen_normalization. Expand the
pasted counit using Adjunction.comp_counit_app. Uniqueness of the pro-etale adjunction
transpose identifies that composite with locallyClosedCounitMate.app M. Both factors
are invertible, proving the assertion. The chosen adjoints enter only through their
specified adjunctions, so adjoint uniqueness also covers nonstandard choices of a.
Empty schemes and identity, pure open and pure closed factors require no changes. -/
theorem locallyClosedCounitMate_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {S V T : Scheme.{u}}
    (aS : S ⟶ Spec (.of D.k)) (aT : T ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (hs : (c ≫ v) ≫ aT = aS) [IsNoetherian T] [QuasiCompact (c ≫ v)] :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    ∀ (adjoints : LocallyClosedComparisonAdjoints A c)
      (hb : ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
        _root_.DerivedCategory.TStructure.t.plus ((adjoints.etaleRight v).obj M.obj)),
      ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
        IsIso ((locallyClosedCounitMate A c v adjoints hb).app M) := by sorry

end AlgebraicGeometry.ProEtale
