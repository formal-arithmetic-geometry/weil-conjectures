/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Natural proper base change in the native derived Weil categories

Source: blueprint sec-six-functors-basics/sk-thm-sfb-proper-base-change,
thm-weil-pbc-qbar.proof.md, "Forgetting the Weil structure" and
"Constructibility and the isomorphism".
(blueprint: lem-sf-native-weil-proper-natural-base-change)

The source is the full bounded constructible subcategory of the ordinary derived
category of native Weil modules. The target is the ambient native equivariant
derived category. All operations are the recorded actual equivariant operations.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Natural proper base change for the native ordinary derived Weil categories.

Source: blueprint part-six-operations/sec-reduction-finite-coefficients/
sec-proper-direct-image/sk-thm-sfb-proper-base-change, thm-weil-pbc-qbar.proof.md,
"Forgetting the Weil structure" and
"Constructibility and the isomorphism".
(blueprint: lem-sf-native-weil-proper-natural-base-change)

Proof: use the canonical adjunction mate already constructed in the comparison module.
Exact forgetting preserves boundedness and commutes with every cohomology functor,
so a bounded constructible Weil input has bounded constructible underlying complex.
The geometric proper-base-change theorem makes its specified exchange invertible.
The equality `NativeBaseChange.forget_mate` identifies the forgotten Weil mate with
that exchange conjugated by the source and target comparison isomorphisms.

For conservativity, use the cohomology criterion directly, as in the last paragraph
of "Constructibility and the isomorphism" in the source. If the forgotten image of
a derived morphism f is invertible, all its cohomology maps are invertible. Naturality
of the exact-forgetting cohomology comparison identifies these maps, up to its
isomorphisms, with the underlying maps of the Weil cohomology morphisms of f.
Forgetting on the abelian category reflects isomorphisms, so those Weil cohomology
morphisms are invertible. `DerivedCategory.isIso_iff` now makes f invertible.
This argument does not use faithfulness of the derived forgetful functor.

Restrict the natural mate to the full bounded constructible source subcategory.
All its components are invertible by the preceding argument, hence it is an
invertible natural transformation. Taking `asIso` gives the stated isomorphism,
including its natural inverse. The argument includes the zero complex, empty
schemes and nonseparated bases; it adds no hypothesis on the base-change map.
-/
theorem nativeWeil_proper_natural_baseChange
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {Z' Z T' T : Scheme.{u}}
    [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
    (v : Z' ⟶ Z) (p' : Z' ⟶ T') (p : Z ⟶ T) (u : T' ⟶ T)
    [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [p.IsOver (Spec (CommRingCat.of k₀))] [u.IsOver (Spec (CommRingCat.of k₀))]
    (_sq : ChosenCartesianSquare v p' p u) [IsProper p]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))] :
    Nonempty
      (((WeilComplex.objectProperty k₀ l Z).ι ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory) ≅
        ((WeilComplex.objectProperty k₀ l Z).ι ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor)) := by
  let F := CategoryTheory.Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l T')
  let : F.mapDerivedCategory.ReflectsIsomorphisms := ⟨fun f _ ↦ by
    rw [_root_.DerivedCategory.isIso_iff]
    intro n
    have : IsIso (F.map ((_root_.DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F⟩
  have component_iso (K : WeilComplex k₀ l Z) :
      IsIso ((NativeBaseChange.mate k₀ l _sq.toCommSq).app K.obj) := by
    have hbounded := Functor.bounded_mapDerivedCategory_obj
      (CategoryTheory.Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l Z)) K.property.1
    have hc (n : ℤ) : ProEtale.IsAdicConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ n).obj
          ((NativeBaseChange.forget k₀ l Z).obj K.obj)) := by
      exact (ProEtale.adicConstructibleSheaf l _).prop_of_iso
        (((CategoryTheory.Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategoryHomologyFunctorIso n).app
            K.obj) (K.property.2 n)
    have := NativeBaseChange.geometric_proper_baseChange_isIso k₀ l _sq
      ((NativeBaseChange.forget k₀ l Z).obj K.obj) hbounded hc
    have : IsIso ((NativeBaseChange.forget k₀ l T').map
        ((NativeBaseChange.mate k₀ l _sq.toCommSq).app K.obj)) := by
      rw [NativeBaseChange.forget_mate]
      infer_instance
    exact isIso_of_reflects_iso _ (NativeBaseChange.forget k₀ l T')
  let β := Functor.whiskerLeft (WeilComplex.objectProperty k₀ l Z).ι
    (NativeBaseChange.mate k₀ l _sq.toCommSq)
  have : ∀ K, IsIso (β.app K) := fun K ↦ component_iso K
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact ⟨asIso β⟩

end AlgebraicGeometry
