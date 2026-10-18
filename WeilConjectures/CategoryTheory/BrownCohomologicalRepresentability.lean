/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Basic
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Brown representability for cohomological functors

We compare the notions of compactness and compact generation of
`WeilConjectures.CategoryTheory.CompactlyGenerated` with those of
`CategoryTheory.BrownRepresentability`, and deduce Brown representability in the form
`H ≅ preadditiveYoneda.obj G` from `BrownRepresentability.exists_bijective`.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`
(blueprint: lem-pc-brown-cohomological-representability).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite DirectSum
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

section Compact

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]

open scoped Classical in
/-- The projection `∐ E ⟶ E j`, the identity on the summand `E j` and zero on the others. -/
private noncomputable def sigmaProj {I : Type v} (E : I → C) (j : I) : ∐ E ⟶ E j :=
  Sigma.desc (Pi.single (M := fun k : I ↦ E k ⟶ E j) j (𝟙 (E j)))

/-- The canonical map `⨁ Hom(K, E i) ⟶ Hom(K, ∐ E)` is injective in any preadditive category:
composing with the projection to `E j` recovers the `j`-th component. -/
private lemma toAddMonoid_comp_sigmaProj {I : Type v} [DecidableEq I] (E : I → C) (K : C)
    (d : ⨁ i : I, (K ⟶ E i)) (j : I) :
    DirectSum.toAddMonoid (fun i : I ↦ Preadditive.rightComp K (Sigma.ι E i)) d ≫
      sigmaProj E j = d j := by
  classical
  induction d using DirectSum.induction_on with
  | zero => simp
  | of k x =>
    rw [DirectSum.toAddMonoid_of]
    by_cases h : k = j
    · subst h
      simp [sigmaProj, Preadditive.rightComp]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      simp only [sigmaProj, Preadditive.rightComp, AddMonoidHom.mk'_apply, Category.assoc,
        Sigma.ι_desc]
      convert comp_zero
      convert Pi.single_eq_of_ne h _
  | add d₁ d₂ h₁ h₂ => simp [Preadditive.add_comp, h₁, h₂]

/-- Compactness in the sense of `IsCompactObject` (bijectivity of
`⨁ Hom(K, E i) ⟶ Hom(K, ∐ E)`) agrees with `BrownRepresentability.IsCompactObj` (every
morphism to a coproduct is a finite sum of morphisms through the summands):
injectivity is automatic. -/
theorem isCompactObject_iff_isCompactObj (K : C) :
    IsCompactObject.{v} K ↔ BrownRepresentability.IsCompactObj K := by
  classical
  constructor
  · intro hK J X c hc f
    let e : c.pt ≅ ∐ X := hc.coconePointUniqueUpToIso (colimit.isColimit _)
    have he (j : J) : Sigma.ι X j ≫ e.inv = c.inj j :=
      hc.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) ⟨j⟩
    obtain ⟨d, hd⟩ := (hK J X).2 (f ≫ e.hom)
    refine ⟨d.support, fun j ↦ d j, ?_⟩
    rw [← cancel_mono e.hom, ← hd, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply]
    erw [DFinsupp.sumAddHom_apply]
    rw [DFinsupp.sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Preadditive.rightComp, ← he]
  · intro hK I E
    refine ⟨(injective_iff_map_eq_zero _).2 fun d hd ↦ ?_, fun f ↦ ?_⟩
    · ext j
      rw [← toAddMonoid_comp_sigmaProj E K d j, hd, zero_comp]
      rfl
    · obtain ⟨S, g, hg⟩ := hK _ (coproductIsCoproduct E) f
      refine ⟨∑ j ∈ S, DirectSum.of (fun i ↦ K ⟶ E i) j (g j), ?_⟩
      simp [hg, Preadditive.rightComp]

end Compact

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{v} C]

omit [HasZeroObject C] [Pretriangulated C] [IsTriangulated C] in
/-- A compactly generated triangulated category has a family of compact generators in the sense
of `BrownRepresentability.CompactGenerators`, namely all shifts of a compact generating family. -/
theorem IsCompactlyGeneratedTriangulated.exists_compactGenerators
    (hC : IsCompactlyGeneratedTriangulated.{v} C) :
    ∃ (ι : Type v) (S : ι → C), BrownRepresentability.CompactGenerators S := by
  obtain ⟨I, E, hcompact, hgenerate⟩ := hC
  refine ⟨I × ℤ, fun p ↦ (E p.1)⟦p.2⟧, ⟨fun p n ↦ ⟨(p.1, p.2 + n),
    ⟨(shiftFunctorAdd' C p.2 n (p.2 + n) rfl).app (E p.1)⟩⟩,
    fun p ↦ ((isCompactObject_iff_isCompactObj _).1 (hcompact p.1)).shift p.2, ?_⟩⟩
  intro X hX
  by_contra hX₀
  obtain ⟨n, f, hf⟩ := hgenerate X hX₀
  refine hf (Sigma.hom_ext _ _ fun i ↦ ?_)
  let adj : shiftFunctor C (-n) ⊣ shiftFunctor C n :=
    (shiftEquiv' C (-n) n (by simp)).toAdjunction
  rw [comp_zero, ← (adj.homEquiv _ _).apply_symm_apply (Sigma.ι E i ≫ f),
    hX (i, -n) ((adj.homEquiv _ _).symm (Sigma.ι E i ≫ f)), Adjunction.homEquiv_unit,
    Functor.map_zero, comp_zero]

/-- (blueprint: lem-pc-brown-cohomological-representability) Every cohomological
functor on a compactly generated triangulated category that
converts coproducts to products is represented by an object. Set-indexed means
indexed by `Type v`, the universe of the morphism sets of `C`.

This is Brown representability (Stacks Project, Tag 0A8F, Lemma `lemma-brown`;
blueprint: lem-pc-brown-cohomological-representability). The hypotheses say that
`C` is compactly generated, that `H` is homological on `Cᵒᵖ` (the contravariant
cohomological condition), and that `H` preserves all discrete limits, which are
the products corresponding to set-indexed coproducts in `C`. The conclusion is
the natural additive Yoneda isomorphism `H ≅ preadditiveYoneda.obj G`. It is deduced from
`BrownRepresentability.exists_bijective`.
-/
theorem brownCohomologicalRepresentability (C : Type u) [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{v} C]
    (hC : IsCompactlyGeneratedTriangulated.{v} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (I : Type v), PreservesLimitsOfShape (Discrete I) H) :
    ∃ G : C, Nonempty (H ≅ preadditiveYoneda.obj G) := by
  obtain ⟨ι, S, hS⟩ := hC.exists_compactGenerators
  have hcoh : BrownRepresentability.IsCohomological H := by
    intro T hT x hx
    exact (ShortComplex.ab_exact_iff _).1
      (H.map_distinguished_exact _ (op_distinguished T hT)) x hx
  have hprod : BrownRepresentability.SendsCoproductsToProducts H := by
    intro J X c hc x
    have := hH J
    let F := H ⋙ forget AddCommGrpCat
    have hc' : IsLimit (F.mapCone c.op) := isLimitOfPreserves F (Cofan.IsColimit.op hc)
    let s : ∀ j : Discrete J, (Discrete.functor (fun j ↦ op (X j)) ⋙ F).obj j :=
      fun j ↦ x j.as
    have hs : s ∈ (Discrete.functor (fun j ↦ op (X j)) ⋙ F).sections := by
      rintro ⟨j⟩ ⟨k⟩ f
      obtain rfl := Discrete.eq_of_hom f
      simp
    obtain ⟨y, hy, hy'⟩ := (Types.isLimit_iff _).1 ⟨hc'⟩ s hs
    exact ⟨y, fun j ↦ hy ⟨j⟩, fun z hz ↦ hy' z fun j ↦ hz j.as⟩
  obtain ⟨G, u, hu⟩ := BrownRepresentability.exists_bijective hS H hcoh hprod
  let α : preadditiveYoneda.obj G ⟶ H :=
    { app Y := AddCommGrpCat.ofHom
        { toFun f := H.map f.op u
          map_zero' := by simp
          map_add' f g := by
            exact congrArg (fun t : H.obj (op G) ⟶ H.obj Y ↦ t u)
              (H.map_add (f := f.op) (g := g.op)) }
      naturality Y Y' f := by
        ext g
        change H.map (f.unop ≫ g).op u = H.map f (H.map g.op u)
        rw [op_comp, H.map_comp]
        rfl }
  have (Y : Cᵒᵖ) : IsIso (α.app Y) := (ConcreteCategory.isIso_iff_bijective _).2 (hu Y.unop)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨G, ⟨(asIso α).symm⟩⟩

end CategoryTheory
