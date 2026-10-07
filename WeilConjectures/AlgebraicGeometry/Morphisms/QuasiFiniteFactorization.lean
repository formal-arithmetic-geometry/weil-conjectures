/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Zariski's Main Theorem for morphisms of finite presentation

A separated, quasi-compact, locally quasi-finite morphism `f : X ⟶ S` locally of finite
presentation to a quasi-compact quasi-separated scheme factors as a quasi-compact open
immersion followed by a finite morphism of finite presentation (Stacks Project Tag 0F2N):
`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation`.

This is the finite-presentation clause of statement (i) of blueprint
`sk-prop-nagata-sketch-zmt`; the finite factorization without the finite-presentation clause is
`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Zariski's Main Theorem, finitely presented finite factorization** (Stacks Project
Tag 0F2N; the finite-presentation clause of statement (i) of blueprint
`sk-prop-nagata-sketch-zmt`). A separated, quasi-compact, locally quasi-finite morphism
`f : X ⟶ S` locally of finite presentation to a quasi-compact quasi-separated scheme factors as
a quasi-compact open immersion `j : X ⟶ T` followed by a finite morphism `p : T ⟶ S` of finite
presentation.

Present the relative normalization of `S` in `X` as a limit of finite `S`-schemes of finite
presentation (Stacks Project Tag 09YZ). At some stage `T_λ`, `X` is a closed subscheme of a
quasi-compact open `U ⊆ T_λ`, cut out by an ideal sheaf of finite type since `X` is of finite
presentation over `S`. Extending this ideal sheaf to a finite-type ideal sheaf `J` on `T_λ`
(Stacks Project Tag 01PF), `X` is an open subscheme of the finite, finitely presented
`S`-scheme `V(J)`. -/
@[stacks 0F2N]
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsFinite p ∧ LocallyOfFinitePresentation p ∧ j ≫ p = f := by
  obtain ⟨F, hF⟩ := f.fromNormalization.exists_finiteApproximation_of_isIntegralHom
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have (i : F.I) : LocallyOfFiniteType
      (f.toNormalization ≫ (Cone.mk _ F.π).π.app i ≫ F.p i) := by
    change LocallyOfFiniteType (f.toNormalization ≫ F.π.app i ≫ F.p i)
    rw [F.π_p, f.toNormalization_fromNormalization]; infer_instance
  obtain ⟨i, U, g, hU, hg, hgU⟩ :=
    Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit F.isLimit F.p f.toNormalization
  have hgf : g ≫ U.ι ≫ F.p i = f := by
    rw [reassoc_of% hgU, F.π_p, f.toNormalization_fromNormalization]
  have : LocallyOfFinitePresentation (g ≫ U.ι ≫ F.p i) := by rw [hgf]; infer_instance
  have := locallyOfFinitePresentation_of_comp g (U.ι ≫ F.p i)
  obtain ⟨J, hJ, hJU⟩ := Scheme.IdealSheafData.exists_finiteType_comap_eq U hU g.ker
    (fun V _ ↦ g.fg_ideal_ker V)
  have := hF i
  have : LocallyOfFinitePresentation J.subschemeι :=
    Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι fun V ↦ hJ V le_top
  have hker : (pullback.fst U.ι J.subschemeι).ker = g.ker := hJU
  have := IsClosedImmersion.isIso_lift (pullback.fst U.ι J.subschemeι) g hker
  let e := IsClosedImmersion.lift (pullback.fst U.ι J.subschemeι) g hker.le
  refine ⟨J.subscheme, e ≫ pullback.snd U.ι J.subschemeι, J.subschemeι ≫ F.p i,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, ← pullback.condition_assoc, IsClosedImmersion.lift_fac_assoc, hgf]

end AlgebraicGeometry
