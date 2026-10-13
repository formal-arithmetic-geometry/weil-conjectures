/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
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

/-- Compatibility with an open in the old base, after any further pullback.
The new base already maps to V. There is no new-base open or exact restriction.
Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S),
Lemma 48.5.2 (Tag 0ATR), and Tag 0E4J.
(blueprint: lem-sc-right-adjoint-mate-old-base-open)

Proof: The square U -> X over V -> Y is cartesian. Since T maps to V, its
base change identifies X times_Y T with U times_V T, by the pullback universal
property. The two equations for r and q identify their composites under this
isomorphism (cancel the open inclusion U -> X). First work before pulling back
to Z. Proper-flat open-unit invertibility for f identifies a restricted to U
with b on V, using the open counit, direct-image composition and right-adjoint
uniqueness. The two direct images over T are identified by the scheme
isomorphism; right-adjoint uniqueness identifies c with b' under that transport.
These comparisons give source and target isomorphisms. Expand the global mate
at K using its unit, inverse conjugate of ordinary base change and counit.
Pasting with U -> X over V -> Y replaces each of these by the chart factor:
the unit and counit equations follow from composite adjunctions and the triangle
identities; ordinary base change uses the same pullback composition comparisons,
so conjugation and inversion respect them. Hence the square of mates commutes.
Apply derived pullback along r to this arrow isomorphism and use pullback
composition and the equality of r and q after transport to obtain the asserted
comparison over Z. This needs neither r nor q nor either mate to be invertible.
Empty V or T gives the same comparison in the zero category; arbitrary Z causes
no exception because every functor preserves isomorphisms.
-/
theorem rightAdjoint_mate_oldBase_open
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y T Z : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (V : Y.Opens) [IsAffine V.toScheme]
    [CompactSpace (f ⁻¹ᵁ V).toScheme] [QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme]
    (g0 : T ⟶ Y) (gV : T ⟶ V.toScheme) (hg : gV ≫ V.ι = g0)
    (c : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback f g0))
    (adjc : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f g0)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g0)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g0)) _ _ _ _
          (pullback.snd f g0) _ _).fst E.obj E.property) ⊣ c)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g0) g0
        (pullback.fst f g0) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    (b : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme)
    (b' : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback (f ∣_ V) gV))
    (adjb : (schemeDerivedQCohProperty V.toScheme).lift
      ((schemeDerivedQCohProperty (f ⁻¹ᵁ V).toScheme).ι ⋙
        schemeDerivedDirectImage (f ∣_ V))
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ (f ∣_ V)).fst
        E.obj E.property) ⊣ b)
    (adjb' : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback (f ∣_ V) gV)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (f ∣_ V) gV))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated
          (pullback.snd (f ∣_ V) gV)) _ _ _ _
        (pullback.snd (f ∣_ V) gV) _ _).fst E.obj E.property) ⊣ b')
    (hβV : ∀ E : schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme,
      IsIso (schemeDerivedBaseChangeMap (f ∣_ V)
        (pullback.snd (f ∣_ V) gV) gV
        (pullback.fst (f ∣_ V) gV) pullback.condition E.obj))
    (r : Z ⟶ pullback f g0)
    (q : Z ⟶ pullback (f ∣_ V) gV)
    (hrq₁ : r ≫ pullback.fst f g0 =
      q ≫ pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι)
    (hrq₂ : r ≫ pullback.snd f g0 = q ≫ pullback.snd (f ∣_ V) gV) :
    Nonempty (Arrow.mk ((derivedPullback r).map
      ((schemeDerivedQCohProperty (pullback f g0)).ι.map
        (@dualityEquationBaseChangeMap _ X Y T
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f g0 a c adjf adjc hβ K))) ≅
      Arrow.mk ((derivedPullback q).map
        ((schemeDerivedQCohProperty (pullback (f ∣_ V) gV)).ι.map
          (dualityEquationBaseChangeMap (f ∣_ V) gV b b' adjb adjb' hβV
            ⟨(derivedPullback V.ι).obj K.obj,
              (derivedPullback_tensor_preserve_QCoh V.ι).1 K.obj K.property⟩)))) := by sorry

end AlgebraicGeometry
