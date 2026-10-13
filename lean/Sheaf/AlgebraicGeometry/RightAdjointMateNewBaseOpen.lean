/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Arrow
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # One-open compatibility of right-adjoint mates

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Compatibility of the canonical mate with an open in the new base alone.
There is no open in the old base and no second local right adjoint.
Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S),
Lemma 48.5.2 (Tag 0ATR), and Tag 0E4J.
(blueprint: lem-sc-right-adjoint-mate-new-base-open)

Proof: Paste the square for W -> Y' with X' = X times_Y Y'. The projection
identities characterize the supplied isomorphism r from f' inverse(W) to
X times_Y W. Exact open restriction agrees with derived pullback. Identify
restriction of a' with the supplied c: apply proper-flat open-unit invertibility
to f', then use direct-image composition, the open counit and uniqueness of
right adjoints. The source comparison is pullback composition; the target
comparison is this restriction identification followed by pullback composition.
Expand the mate as the unit, inverse conjugate of ordinary base change, and
counit. Horizontally paste the W square. Composition of units and counits and
the triangle identities identify its mate with the mate of the pasted square;
ordinary base change and its inverse conjugate respect the same comparisons.
Thus the two endpoint isomorphisms commute with the mates. They yield an arrow
isomorphism, without assuming either mate is invertible. For an empty W all
comparisons lie in the zero derived category, so the same argument applies.
-/
theorem rightAdjoint_mate_newBase_open
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    (W : Y'.Opens) [IsAffine W.toScheme]
    (c : schemeDerivedQCohCategory W.toScheme ⥤
      schemeDerivedQCohCategory (pullback f (W.ι ≫ g)))
    (adjc : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f (W.ι ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (W.ι ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (W.ι ≫ g))) _ _ _ _
          (pullback.snd f (W.ι ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβW : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (W.ι ≫ g)) (W.ι ≫ g)
        (pullback.fst f (W.ι ≫ g)) pullback.condition E.obj))
    (r : ((pullback.snd f g) ⁻¹ᵁ W).toScheme ⟶ pullback f (W.ι ≫ g))
    [IsIso r]
    (hr₁ : r ≫ pullback.fst f (W.ι ≫ g) =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.fst f g)
    (hr₂ : r ≫ pullback.snd f (W.ι ≫ g) ≫ W.ι =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.snd f g) :
    Nonempty (Arrow.mk
      ((schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory.map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map
          (@dualityEquationBaseChangeMap _ X Y Y'
            (QuasiCompact.compactSpace_of_compactSpace f)
            (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
            f g a a' adjf adjf' hβ K))) ≅
      Arrow.mk ((derivedPullback r).map
        ((schemeDerivedQCohProperty (pullback f (W.ι ≫ g))).ι.map
          (@dualityEquationBaseChangeMap _ X Y W.toScheme
            (QuasiCompact.compactSpace_of_compactSpace f)
            (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
            f (W.ι ≫ g) a c adjf adjc hβW K)))) := by sorry

end AlgebraicGeometry
