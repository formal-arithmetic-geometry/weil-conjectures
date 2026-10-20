/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

import all Sheaf.Paper.IntegralIndHeartRealization
import all Sheaf.Paper.IntegralWindowCoproductComparison
import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact

/-! Integral compactness: an intermediate argument from blueprint main-20261015,
sec-six-functors-basics/sk-prop-int-compactness/sk-prop-int-compactness-compact.proof.md. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

private theorem factors_of_preserves_single
    {A : Type*} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [HasColimitsOfSize.{v, v} A] (S : DerivedCategory A)
    (hpres : ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (F : J ⥤ A) (q : ℤ),
      PreservesColimit F (DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj (op S))) :
    DerivedCategory.HomFactorsThroughFilteredColimits.{v} S := by
  classical
  let Y := preadditiveCoyoneda.obj (op S)
  intro J _ _ F c hc n f
  let G := DerivedCategory.singleFunctor A n ⋙ Y
  have : PreservesColimit F (DerivedCategory.singleFunctor A 0 ⋙
      shiftFunctor _ (-n) ⋙ Y) :=
    hpres J F (-n)
  have : PreservesColimit F ((DerivedCategory.singleFunctor A 0 ⋙
      shiftFunctor _ (-n)) ⋙ Y) :=
    preservesColimit_of_natIso F (Functor.associator _ _ _).symm
  have : PreservesColimit F G := preservesColimit_of_natIso F
    (Functor.isoWhiskerRight ((DerivedCategory.singleFunctors A).shiftIso (-n) n 0
      (by omega)) Y)
  let hcG := isColimitOfPreserves G hc
  let φ := colimit.desc _ (G.mapCocone c)
  have : IsIso φ :=
    ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp ⟨hcG⟩
  obtain ⟨j, g, hg⟩ := Concrete.colimit_exists_rep (F ⋙ G) (inv φ f)
  refine ⟨j, g, ?_⟩
  have he : φ (colimit.ι (F ⋙ G) j g) = f := by
    rw [hg]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id φ) f
  have he' : (G.map (c.ι.app j)) g = f := by
    calc
      _ = φ (colimit.ι (F ⋙ G) j g) :=
        (ConcreteCategory.congr_hom (colimit.ι_desc (G.mapCocone c) j) g).symm
      _ = _ := he
  exact he'.symm

private theorem lower_tail_of_factors
    {A : Type*} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [Abelian.HasKInjectiveResolutions A]
    [HasLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) A]
    (H : ObjectProperty A) [H.IsClosedUnderIsomorphisms] [H.ind.{v}.ContainsZero]
    (S : DerivedCategory A)
    (hcont : DerivedCategory.HomFactorsThroughFilteredColimits.{v} S) (N : ℤ)
    (hvan : ∀ B, H B → ∀ n ≤ N,
      ∀ f : S ⟶ (DerivedCategory.singleFunctor A n).obj B, f = 0)
    (L : DerivedCategory A) (hL : DerivedCategory.homologyProperty H.ind.{v} L)
    (hLE : L.IsLE N) : Subsingleton (S ⟶ L) := by
  have hInd := DerivedCategory.eq_zero_of_ind H hcont N hvan
  let T := (DerivedCategory.TStructure.t.triangleLTGE N).obj L
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished N L
  have hlow : DerivedCategory.homologyProperty H.ind.{v} T.obj₁ :=
    (DerivedCategory.homologyProperty H.ind.{v}).prop_of_iso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (N - 1) N (by omega)).app L)
      (DerivedCategory.homologyProperty_truncLE hL (N - 1))
  have hhigh := DerivedCategory.homologyProperty_truncGE hL N
  have : T.obj₁.IsLE (N - 1) := inferInstanceAs
    (DerivedCategory.TStructure.t.IsLE T.obj₁ (N - 1))
  have : DerivedCategory.TStructure.t.IsLE L N := hLE
  have : T.obj₃.IsGE N := inferInstanceAs (DerivedCategory.TStructure.t.IsGE T.obj₃ N)
  have : T.obj₃.IsLE N := by
    change DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncGE N).obj L) N
    infer_instance
  have hz (f : S ⟶ L) : f = 0 := by
    obtain ⟨g, hg⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂ T hT f
      (DerivedCategory.eq_zero_of_isGE_of_isLE_self N hInd N T.obj₃ hhigh le_rfl _)
    rw [hg, DerivedCategory.eq_zero_of_isLE N hInd T.obj₁ hlow g, zero_comp]
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

open Classical in
/-- Vanishing of Hom into the entire lower tail, including unbounded complexes.
Source: blueprint main-20261015, sk-prop-int-compactness-compact.proof.md,
paragraph (2), steps 8, 10--11 (blueprint: lem-integral-ind-lower-tail).

Proof: Integral Ext continuity first extends hd from constructible targets to their
filtered colimits. A bounded complex in degrees at most -d_C-1 has zero Hom from C:
induct on its finite cohomological amplitude using truncation triangles and these Ext
bounds. For an unbounded lower tail, pro-etale left completeness expresses it as the
homotopy limit of its lower truncations, with termwise derived products. The Hom
Milnor sequence has zero inverse-limit term by the bounded argument. The degree-minus-
one Hom tower is eventually a tower of isomorphisms, since the intervening layers are
Ext groups in degrees above d_C. Its 1-minus-transition map on the product is surjective:
choose one term and solve the recurrence successively along the isomorphisms; fill the
finitely many preceding coordinates recursively. Thus its cokernel vanishes as well.
Both terms in the Milnor sequence are zero, proving the assertion. No boundedness or
completeness condition is imposed on L beyond its cohomology and the stated upper bound. -/
theorem integralIndLowerTail
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X → ℕ)
    (hd : ∀ (C N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (q : ℤ), (d C : ℤ) < q →
        Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧)) :
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
    let H : ObjectProperty A := IsConstantModelConstructible
      (Profinite.padicIntegersRingObj ℓ E) X
    ∀ (C : H.FullSubcategory) (L : DerivedCategory A),
      DerivedCategory.homologyProperty H.ind.{u + 1} L →
      L.IsLE (-(d C : ℤ) - 1) →
      Subsingleton (((DerivedCategory.singleFunctor A 0).obj C.obj) ⟶ L) := by
  classical
  dsimp only
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let H : ObjectProperty A := IsConstantModelConstructible Λ X
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj Λ X))
  let e : A ≌ SheafOfModules.{u + 1} R :=
    InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u + 1} R) :=
    Scheme.ProEt.products_exact.{u, u + 1, 0} X R ℕ
  have : HasLimitsOfShape (Discrete ℕ) A :=
    Adjunction.hasLimitsOfShape_of_equivalence e.functor
  have : HasExactLimitsOfShape (Discrete ℕ) A :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) e.symm
  have : H.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constant_model_iso Λ X e h⟩
  have : H.ind.{u + 1}.ContainsZero := ⟨0, isZero_zero A,
    H.le_ind _ (constantModelConstructible_of_isZero Λ X _ (isZero_zero A))⟩
  intro C L hL hLE
  let S := (DerivedCategory.singleFunctor A 0).obj C.obj
  let Y := preadditiveCoyoneda.obj (op S)
  have hcont : DerivedCategory.HomFactorsThroughFilteredColimits.{u + 1} S :=
    factors_of_preserves_single S (fun J _ _ F q ↦
      integral_single_preserves_filtered ℓ E k p hp hpℓ X C J F q)
  let N : ℤ := -(d C : ℤ) - 1
  have hvan (B : A) (hB : H B) (n : ℤ) (hn : n ≤ N)
      (f : S ⟶ (DerivedCategory.singleFunctor A n).obj B) : f = 0 := by
    let j := ((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app B
    have hsub : Subsingleton (S ⟶ ((DerivedCategory.singleFunctor A 0).obj B)⟦-n⟧) :=
      hd C ⟨B, hB⟩ (-n) (by dsimp [N] at hn; omega)
    have hf : f ≫ j.inv = 0 := by
      change f ≫ j.inv = (0 : S ⟶ ((DerivedCategory.singleFunctor A 0).obj B)⟦-n⟧)
      exact hsub.elim _ _
    exact (cancel_mono j.inv).mp (by simpa using hf)
  exact lower_tail_of_factors H S hcont N hvan L hL hLE

end AlgebraicGeometry.ProEtale
