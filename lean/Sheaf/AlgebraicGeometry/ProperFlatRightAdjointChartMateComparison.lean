/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Arrow
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen

/-! # Comparison of the global right-adjoint mate with an open-chart mate

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
(blueprint: lem-sc-proper-flat-right-adjoint-chart-mate-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restriction of the global mate and pullback of the chart mate are isomorphic as
arrows. This is a comparison statement, with no invertibility assumption on the chart
mate and no affine-case base-change theorem as a hypothesis.
Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S), using Tag 0E4J.
(blueprint: lem-sc-proper-flat-right-adjoint-chart-mate-comparison)

Proof: The two equations on q identify it with the canonical isomorphism from the
open f' inverse(W) to U times_V W, where U = f inverse(V). Indeed, paste the
pullback square defining X' with the two open restriction squares and use the
universal property of the pullback. Restriction agrees with derived pullback of
an open immersion. Restriction preserves quasi-coherent cohomology, and the
qcqs derived direct images of the restricted maps have right adjoints.
Apply proper_flat_rightAdjoint_restriction_open to f and its base change f'.
The open-unit arrows are invertible. Right-adjoint uniqueness and the open counit
identify the restrictions of a and a' with b and b', respectively. These give
isomorphisms on both endpoints of the displayed arrows, also using the canonical
composition comparisons for pullback and the pullback along q.
To check that they form an arrow isomorphism, expand the canonical mate as the
pullback of a applied to the unit, followed by the inverse conjugate of ordinary
base change, followed by the pullback counit. Paste the two open squares
horizontally with the given square. The composite units and counits give the
unit and counit of the pasted adjunctions by the triangle identities. Ordinary
base change restricts to the chart's base-change map. Its invertible conjugate
commutes with these comparisons, as does its inverse. Thus the endpoint
isomorphisms intertwine the two mate morphisms. This is precisely Remark 48.6.1.
The proof does not assume that either mate is invertible. Empty opens cause no
exception: their derived categories are zero and all comparisons are unique.
-/
theorem proper_flat_rightAdjoint_chart_mate_comparison
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
    (V : Y.Opens) (W : Y'.Opens) (hWV : W ≤ g ⁻¹ᵁ V)
    [IsAffine V.toScheme] [IsAffine W.toScheme]
    [CompactSpace (f ⁻¹ᵁ V).toScheme] [QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme]
    (b : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme)
    (b' : schemeDerivedQCohCategory W.toScheme ⥤
      schemeDerivedQCohCategory (pullback (f ∣_ V) (g.resLE V W hWV)))
    (adjb : (schemeDerivedQCohProperty V.toScheme).lift
      ((schemeDerivedQCohProperty (f ⁻¹ᵁ V).toScheme).ι ⋙
        schemeDerivedDirectImage (f ∣_ V))
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ (f ∣_ V)).fst
        E.obj E.property) ⊣ b)
    (adjb' : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback (f ∣_ V) (g.resLE V W hWV))).ι ⋙
        schemeDerivedDirectImage (pullback.snd (f ∣_ V) (g.resLE V W hWV)))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated
          (pullback.snd (f ∣_ V) (g.resLE V W hWV))) _ _ _ _
        (pullback.snd (f ∣_ V) (g.resLE V W hWV)) _ _).fst E.obj E.property) ⊣ b')
    (hβV : ∀ E : schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme,
      IsIso (schemeDerivedBaseChangeMap (f ∣_ V)
        (pullback.snd (f ∣_ V) (g.resLE V W hWV)) (g.resLE V W hWV)
        (pullback.fst (f ∣_ V) (g.resLE V W hWV)) pullback.condition E.obj))
    (q : ((pullback.snd f g) ⁻¹ᵁ W).toScheme ⟶
      pullback (f ∣_ V) (g.resLE V W hWV))
    (hq₁ : q ≫ pullback.fst (f ∣_ V) (g.resLE V W hWV) ≫ (f ⁻¹ᵁ V).ι =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.fst f g)
    (hq₂ : q ≫ pullback.snd (f ∣_ V) (g.resLE V W hWV) ≫ W.ι =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.snd f g) :
    Nonempty (Arrow.mk
      ((schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory.map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map
          (@dualityEquationBaseChangeMap _ X Y Y'
            (QuasiCompact.compactSpace_of_compactSpace f)
            (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
            f g a a' adjf adjf' hβ K))) ≅
      Arrow.mk ((derivedPullback q).map
        ((schemeDerivedQCohProperty (pullback (f ∣_ V) (g.resLE V W hWV))).ι.map
          (dualityEquationBaseChangeMap (f ∣_ V) (g.resLE V W hWV) b b' adjb adjb' hβV
            ⟨(derivedPullback V.ι).obj K.obj,
              (derivedPullback_tensor_preserve_QCoh V.ι).1 K.obj K.property⟩)))) := by sorry

end AlgebraicGeometry
