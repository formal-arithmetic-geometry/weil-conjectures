module

public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturality

/-! The shifted local derived comparison and its naturality. -/

@[expose] public section

universe u v w
open CategoryTheory Opposite
namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- Elaborating both shifted sheaf Hom comparisons and localization equivalences needs extra fuel.
/-- The shifted comparison is natural for arbitrary maps of the two arguments.
The maps `s` and `t` need not be quasi-isomorphisms.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1), and Tag 0A94.
(blueprint: lem-pur-hom-complex-sections-derived-naturality).

Proof: a section of degree `n` is a family of localized maps `L^p → I^(p+n)`.
The equation `d_I f - (-1)^n f d_L = 0` identifies cocycles with chain maps
`L|U → (I|U)[n]`, since the differential of the shift is `(-1)^n d_I`.
For a degree `n-1` family `h`, its differential is
`d_I h + (-1)^n h d_L`; multiplying `h` by `(-1)^n` identifies this with
null-homotopies into `(I|U)[n]`. The two quotients therefore identify homology
with the homotopy-category Hom set. Restriction preserves K-injectivity and
shifting does too, so the K-injective localization comparison is bijective.
Compose these bijections to obtain `a` and `b`. On cocycle representatives the
product-projection formula for the Hom bifunctor sends `f` to `s f t`.
The shifted map has components `s^(p+n)`, so this agrees exactly with derived
precomposition by `t|U` and postcomposition by `(s|U)[n]`. Homology projections
are surjective, hence this equality on representatives proves the displayed
naturality for every class. At `n = 0` this is the unshifted local comparison;
for zero complexes all involved Hom sets are singleton. -/
theorem homComplex_sections_derived_naturality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective] (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := DerivedCategory.Q.{w} (C := SheafOfModules.{max u v} (R₀.over U))
    let f := E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)
    ∃ a : (E.obj (homComplex (R := R) L I')).homology n ≃
        (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)),
      ∃ b : (E.obj (homComplex (R := R) L' I)).homology n ≃
          (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)),
        ∀ x, b (HomologicalComplex.homologyMap f n x) =
          Q.map (res.map t) ≫ a x ≫ Q.map ((shiftFunctor _ n).map (res.map s)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let hzero := module_overFunctor_preservesZero R₀ U
  let _ := hzero
  let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient (SheafOfModules.{max u v} (R₀.over U))
    (ComplexShape.up ℤ)
  let F := DerivedCategory.Qh.{w} (C := SheafOfModules.{max u v} (R₀.over U))
  let Q := DerivedCategory.Q.{w} (C := SheafOfModules.{max u v} (R₀.over U))
  let c := DerivedCategory.quotientCompQhIso.{w} (SheafOfModules.{max u v} (R₀.over U))
  have : CochainComplex.IsKInjective (res.obj I') :=
    isKInjective_restrict_localized R₀ U hzero I'
  have : CochainComplex.IsKInjective (res.obj I) :=
    isKInjective_restrict_localized R₀ U hzero I
  let e (A B : CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ)
      [B.IsKInjective] : (q.obj A ⟶ q.obj B) ≃ (Q.obj A ⟶ Q.obj B) :=
    (Equiv.ofBijective (F.map : (q.obj A ⟶ q.obj B) → _)
      (CochainComplex.IsKInjective.Qh_map_bijective (q.obj A) B)).trans
      (Iso.homCongr (c.app A) (c.app B))
  obtain ⟨a, b, hab⟩ := homComplex_sections_homotopy_naturality R U s t n
  refine ⟨a.trans (e (res.obj L) ((res.obj I')⟦n⟧)),
    b.trans (e (res.obj L') ((res.obj I)⟦n⟧)), ?_⟩
  intro x
  change e _ _ (b _) = Q.map (res.map t) ≫ e _ _ (a x) ≫
    Q.map ((shiftFunctor _ n).map (res.map s))
  rw [hab]
  change c.inv.app _ ≫ F.map (q.map (res.map t) ≫ a x ≫
      q.map ((shiftFunctor _ n).map (res.map s))) ≫ c.hom.app _ =
    Q.map (res.map t) ≫ (c.inv.app _ ≫ F.map (a x) ≫ c.hom.app _) ≫
      Q.map ((shiftFunctor _ n).map (res.map s))
  simp only [Functor.map_comp, Category.assoc]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]

end CategoryTheory
