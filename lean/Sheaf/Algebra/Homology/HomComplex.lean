/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Ring.NegOnePow
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Hom complexes of sheaves of modules

Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).

The chosen bifunctor has product terms, differential `d_M f - (-1)^n f d_L`,
and componentwise pre- and post-composition. Its existence proof is postponed;
its data are selected from that named theorem, never supplied by `sorry`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

/-- Existence of the Hom-complex bifunctor with its product projections and exact sign.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).

Proof: take in degree `n` the product of the internal sheaf Homs from `L^p` to
`M^(p+n)`. Products are computed sectionwise, so sections are families of maps
on the localized site. Define the differential on these families by
`d_M f - (-1)^n f d_L`. Both composition maps are linear and commute with
restriction. Expanding its square gives the two zero terms `d_M^2 f` and
`f d_L^2`, while the mixed terms cancel because the signs in consecutive
integer degrees are opposite. Thus these products form a cochain complex.
Pre- and post-compose each component with chain maps. Their chain-map
identities show this commutes with the differential; associativity and identity
of composition give the bifunctor laws. Use the product universal property
for the projections and their formulas below. No extra boundedness is used. -/
theorem homComplex_exists :
    ∃ F : (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)ᵒᵖ ⥤ CochainComplex
        (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex
        (SheafOfModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ,
      ∃ π : ∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n p q : ℤ), p + n = q →
        (((F.obj (op L)).obj M).X n ⟶ SheafOfModules.homObj (L.X p) (M.X q)),
        (∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
            (fun p : ℤ ↦ π L M n p (p + n) rfl)))) ∧
        (∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m p q q' p' : ℤ)
          (_hnm : n + 1 = m) (hpq : p + m = q)
          (hq' : p + n = q') (hp' : p' + n = q),
          ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
            π L M n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (M.d q' q) -
              n.negOnePow • (π L M n p' q hp' ≫
                SheafOfModules.homObjMap (L.d p p') (𝟙 (M.X q)))) ∧
        (∀ (L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (f : L' ⟶ L) (g : M ⟶ M')
          (n p q : ℤ) (hpq : p + n = q),
          (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
            π L M n p q hpq ≫ SheafOfModules.homObjMap (f.f p) (g.f q)) := by
  sorry

/-- The sheaf-valued Hom-complex bifunctor, contravariant in the first complex.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).
Its projections, differential and componentwise action are specified together
by `homComplex_exists`, from which this definition selects its data. -/
noncomputable def homComplexFunctor :
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)ᵒᵖ ⥤ CochainComplex
        (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex
        (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ :=
  Classical.choose (homComplex_exists (C := C) (J := J) (R := R))

/-- The Hom complex of two cochain complexes of sheaves of modules.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).
In degree `n` its product projections identify sections with families of
localized linear maps `L^p → M^(p+n)`, and its differential is
`d_M f - (-1)^n f d_L`. Functoriality is supplied by `homComplexFunctor`. -/
noncomputable def homComplex
    (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) : CochainComplex
        (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ :=
  (homComplexFunctor.obj (op L)).obj M

end CategoryTheory
