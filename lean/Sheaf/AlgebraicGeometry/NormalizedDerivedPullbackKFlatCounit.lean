/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison
import Sheaf.CategoryTheory.NatTransFromResolvingClass
import Sheaf.Algebra.Homology.KFlatResolution

/-! # A normalized counit on K-flat representatives

Source: Stacks Project, Tag 06YJ, K-flat computation; the supplied-tensorator
normalization of the parent cone node, expanded by the agent.
(blueprint: lem-sc-derived-pullback-kflat-counit-shift-adjustment-normalized).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

-- The construction supplies its own counit, independently of the supplied ε₀.
set_option linter.unusedVariables false in
/-- A K-flat counit can be normalized so that its translation square on K-flat
representatives has the supplied translated-unit tensorator form.

Source: Stacks Project, Tag 06YJ, K-flat computation; the additional coherence
normalization is the translated-unit step of the parent node's proof, expanded
by the agent, rather than a literal assertion of Tag 06YJ.

Proof. Compute derived pullback on the resolving class of K-flat complexes.
Represent the unit by the structure sheaf in degree zero and the shifted unit
by its translate. These are K-flat, and termwise pullback carries them to the
corresponding complexes on Z. The comparison with derived pullback and the
supplied monoidal unit map identify the unshifted units. Translate this
comparison, using the chosen K-flat comparison for the shifted representative,
to obtain e. For a K-flat P, write P[1] as O_Y[1] tensor P by the first-variable
Koszul comparison followed by the translated left unitor. Transport this
rewrite through the supplied inverse tensorator, then e tensor identity, and
undo the rewrite over Z. Choose the representative comparison jointly with
this rewrite. Tensorator associativity and its two unit identities identify
the translated comparison with precisely this composite followed by the
translation of the comparison at P. This is the asserted square on P.
The Koszul maps, unitors and tensorator are natural, so the comparisons respect
maps of K-flat representatives and replacement maps. Resolving-class descent
therefore gives the natural counit ε on the homotopy category. Its components
on K-flat representatives are composites of the representative isomorphisms
and hence are invertible. The square asserted here is only on K-flat P; its
extension to other homotopy objects is proved in the parent module. On the zero
complex every map is the unique zero-object map, so the construction also
covers the empty scheme. No factorization against ε₀ is asserted here.
(blueprint: lem-sc-derived-pullback-kflat-counit-shift-adjustment-normalized). -/
theorem exists_normalized_derivedPullback_kFlat_counit
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε₀ : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε₀ : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      IsIso (ε₀.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z),
        (∀ P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
        ∀ P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        ε.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (ε.app X)⟦(1 : ℤ)⟧' := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let H := HomotopyCategory A (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let F := Q ⋙ derivedPullback f
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have : W.HasRightCalculusOfFractions :=
    by infer_instance
  have hres : ∀ X : H, ∃ (R : H) (s : R ⟶ X),
      kFlatShiftRepresentative Y R ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := Y.sheaf) K
    exact ⟨q.obj P, q.map s, ⟨P, hP, Or.inl rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : W.IsInvertedBy F := by
    intro X X' s hs
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    exact inferInstanceAs (IsIso ((derivedPullback f).map (Q.map s)))
  obtain ⟨e, α, hα, hsquare⟩ := exists_normalized_kFlat_representative_comparison f
  obtain ⟨ε, hε⟩ := exists_natTrans_from_resolvingClass W
    (kFlatShiftRepresentative Y) hres F G hinv (fun X hX ↦ (α X hX).hom) hα
  refine ⟨e, ε, ?_, ?_⟩
  · intro P hP
    rw [hε (q.obj P) ⟨P, hP, Or.inl rfl⟩]
    infer_instance
  · intro P hP
    dsimp only
    rw [hε (q.obj P⟦(1 : ℤ)⟧) ⟨P, hP, Or.inr rfl⟩,
      hε (q.obj P) ⟨P, hP, Or.inl rfl⟩]
    exact hsquare P hP

end AlgebraicGeometry
