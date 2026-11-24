/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.EtaleComplexCohomologyPresentationData
import WeilConjectures.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso
import WeilConjectures.AlgebraicGeometry.EtaleComplexCohomologyLimit

/-! # Presenting raw module cohomology by abelian etale complexes

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The precise hypotheses of complex continuity, as an existential proposition.
No object or map is chosen by this definition, and no continuity conclusion is a field.
(Stacks, Tag 0EZM) -/
abbrev EtaleComplexCohomologyPresentation
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H) : Prop :=
  EtaleComplexCohomologyPresentationData H B

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Complex continuity applied to a presentation. -/
theorem EtaleComplexCohomologyPresentation.isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    {H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {B : Cocone H}
    (s : EtaleComplexCohomologyPresentation H B) : Nonempty (IsColimit B) := by
  rcases s with ⟨D, c, hc, compact, quasiSeparated, affine, F, φ,
    hidentity, hcomposition, a, hbelow, G,
    eG, hG, p, P, hP, eH, hH, L, hL, eB, hB, _⟩
  exact @nonempty_isColimit_etale_complex_cohomology I _ _ D c hc compact
    quasiSeparated affine F @φ hidentity hcomposition a hbelow G eG hG
    p @P @hP H eH hH L hL B eB hB

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Raw module derived-Hom cohomology, including its fixed transition maps, has a
presentation by abelian etale complexes on the base-changed inverse system.
This theorem identifies the input to continuity; it does not assert cohomology
continuity or any eventual equality of classes.
(Stacks, Tags 09Z1, 0EZM and 03FD) -/
theorem nonempty_higherDirectImageRaw_complex_presentation
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left] :
    EtaleComplexCohomologyPresentation
      (higherDirectImageRawDiagram Λ k G q D U)
      (higherDirectImageRawCocone Λ k G q D c U) := by
  obtain ⟨e, he⟩ := exists_rawModule_restrictedAbelian_natural_iso Λ k G q U
  let F₀ := (sheafCompose W.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  unfold EtaleComplexCohomologyPresentation
  refine restrictedOverAbelianCocone_complex_data k F₀ q D c hc U
    (higherDirectImageRawDiagram Λ k G q D U)
    (higherDirectImageRawCocone Λ k G q D c U)
    (fun i ↦ e (D.obj i)) (e c.pt) ?_ ?_
  · intro i j f
    dsimp only [higherDirectImageRawDiagram, Functor.comp_map, Functor.op_map]
    exact he _ _ (D.map f)
  · intro i
    dsimp only [higherDirectImageRawCocone, Functor.mapCocone, Cone.op,
      Functor.op_obj, NatTrans.op_app, Functor.mapCocone_ι_app]
    exact he _ _ (c.π.app i)

end AlgebraicGeometry.Etale
