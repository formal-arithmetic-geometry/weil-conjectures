/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationField
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Higher direct image stalks over a field

Source: Stacks Project, Tags 03Q9 and 03SI, and blueprint
`lem-sc-cd-ground-field`, proof steps 2--4.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private lemma isUniversalHomeomorphism_field_strictHenselizationEval
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosure K L] [IsAlgClosed L] :
    IsUniversalHomeomorphism
      (Spec.map (strictHenselizationEval
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))) := by
  exact AlgebraicGeometry.Scheme.isUniversalHomeomorphism_spec_strictHenselizationEval

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma strictHenselizationComparison_over
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (smallStrictHenselizationColimitIso s).hom ≫
      strictHenselizationStructuralMap s = strictLocalizationToBase s := by
  rw [← smallStrictHenselizationColimitIso_toBase s, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma nonempty_addEquiv_strictLocalization_toBase
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ) :
    Nonempty ((((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)) ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (strictLocalizationToBase s))).obj F) q) := by
  let A := AddCommGrpCat.{u + 1}
  let Y := pullback f (strictLocalizationToBase s)
  let G := (upperStar A (pullback.fst f (strictLocalizationToBase s))).obj F
  let e₁ := ((pointSmallEtale s).sheafFiber (A := A)).mapIso
    (((lowerStar A f).homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm)
  obtain ⟨r, _, hr⟩ := (strictHenselizationStalkFormula f s F hF q).1
  have := hr
  let e₂ := asIso (r ≫ strictHenselizationCohomologyComparison s f F q)
  let e₃ := (Sheaf.Γ Y.smallEtaleTopology A).homologyRightDerivedFunctorObjSingleFunctorIso G q
  have : ((sheafSections Y.smallEtaleTopology A).obj
      (Opposite.op (⊤_ Y.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ A).obj _).Additive
  let e₄ := (NatIso.rightDerived
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A terminalIsTerminal) q).app G
  obtain ⟨e₅⟩ := Sheaf.nonempty_rightDerived_sections_obj_iso_functorH Y.smallEtaleTopology
    terminalIsTerminal q G
  exact ⟨(e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).addCommGroupIsoToAddEquiv⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same stalk formula over the representative model `strictHenselizationScheme s`:
transport along the colimit comparison isomorphism between the two strict-local models. -/
private lemma nonempty_addEquiv_strictLocalization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ) :
    Nonempty ((((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)) ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) q) := by
  let A := AddCommGrpCat.{u + 1}
  let σ₀ := strictHenselizationStructuralMap s
  let σ := strictLocalizationToBase s
  let ι : strictHenselizationScheme s ⟶ strictLocalization s :=
    Spec.map (smallStrictHenselizationColimitIso s).inv
  have hι : ι ≫ σ = σ₀ := smallStrictHenselizationColimitIso_toBase s
  let g : pullback f σ₀ ⟶ pullback f σ :=
    pullback.lift (pullback.fst f σ₀) (pullback.snd f σ₀ ≫ ι) (by
      rw [Category.assoc, hι, pullback.condition])
  let g' : pullback f σ ⟶ pullback f σ₀ :=
    pullback.lift (pullback.fst f σ) (pullback.snd f σ ≫ inv ι) (by
      rw [Category.assoc, ← hι, IsIso.inv_hom_id_assoc, pullback.condition])
  have : IsIso g := ⟨g', by apply pullback.hom_ext <;> simp [g, g'],
    by apply pullback.hom_ext <;> simp [g, g']⟩
  obtain ⟨e₁⟩ := nonempty_addEquiv_strictLocalization_toBase f L s F hF q
  let e₂ := cohomologyEquiv g ((upperStar A (pullback.fst f σ)).obj F) q
  let e₃ := (Sheaf.functorH (pullback f σ₀).smallEtaleTopology q).mapIso
    ((upperStarComp A g (pullback.fst f σ) (pullback.fst f σ₀) (by simp [g])).symm.app F)
  exact ⟨e₁.trans (e₂.trans e₃.addCommGroupIsoToAddEquiv)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Over a field, the geometric stalk of a higher direct image is the cohomology
of the base change to the chosen algebraic closure.

Source: Stacks Project, Tag 03Q9 (higher direct images), Tag 03SI (topological
invariance), and blueprint `lem-sc-cd-ground-field`, proof steps 2--4.
(blueprint: lem-sc-field-higher-direct-image-stalk)

Proof: finite type over a field makes the source locally Noetherian, so the morphism
is quasi-separated. In the identity affine chart the maximal ideal of the strict
henselization C is the extension of the zero prime of K, hence zero. Thus C is a
field; its separably closed residue field identifies with C. The evaluation C → L
is compatible with K → L, making L algebraic over C. An algebraic extension of a
separably closed field is purely inseparable, so Spec L → Spec C and its base change
are universal homeomorphisms. Apply the strict-henselization stalk formula, convert
between ordinary and bounded-below right derived functors and Ext cohomology, and
compose with topological invariance and the composition isomorphism for pullback.
The explicit algebraically-closed instance is redundant with IsAlgClosure and
keeps instance search in the statement independent of the choice of ground field. -/
theorem nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosure K L] [IsAlgClosed L] {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) :
    Nonempty
      ((((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K L)))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj
          (((lowerStar AddCommGrpCat.{u + 1} a).rightDerived q).obj F)) ≃+
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj F) q) := by
  let A := AddCommGrpCat.{u + 1}
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let σ := strictLocalizationToBase s
  let h := Spec.map (strictHenselizationEval s)
  have hh : h ≫ σ = s := by
    exact spec_map_strictHenselizationEval_comp_strictLocalizationToBase s
  have : IsUniversalHomeomorphism h :=
    isUniversalHomeomorphism_field_strictHenselizationEval (K := K) L
  let g : pullback a s ⟶ pullback a σ :=
    pullback.lift (pullback.fst a s) (pullback.snd a s ≫ h) (by
      rw [Category.assoc, hh, pullback.condition])
  have hg : IsPullback g (pullback.snd a s) (pullback.snd a σ) h := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback a σ)
    · simpa only [g, pullback.lift_fst, hh] using IsPullback.of_hasPullback a s
    · exact pullback.lift_snd _ _ _
  have : IsUniversalHomeomorphism g := MorphismProperty.of_isPullback hg.flip inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : QuasiSeparated a := inferInstance
  obtain ⟨e₁⟩ := nonempty_addEquiv_strictLocalization_toBase a L s F hF q
  let e₂ := cohomologyEquiv g ((upperStar A (pullback.fst a σ)).obj F) q
  let e₃ := (Sheaf.functorH (pullback a s).smallEtaleTopology q).mapIso
    ((upperStarComp A g (pullback.fst a σ) (pullback.fst a s)
      (by simp [g])).symm.app F)
  exact ⟨e₁.trans (e₂.trans e₃.addCommGroupIsoToAddEquiv)⟩

end AlgebraicGeometry.Etale
