/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
import Sheaf.AlgebraicGeometry.DerivedBaseChangePasting
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Factorization of a right-adjoint mate through an old-base open

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Pasting through the old-base open factors the global mate through the open mate.
The open mate is retained as a morphism and is not assumed invertible.
Only quasi-compactness and quasi-separatedness are needed for f; properness,
flatness, and finite presentation play no role in this categorical factorization.
Source: Stacks Project, duality.tex, Lemma 48.5.2 (Tag 0ATR) and
Remark 48.6.1 (Tag 0E9S).
(blueprint: lem-sc-right-adjoint-mate-old-base-open-factorization)

Proof: The restriction square is cartesian. Its pullback along gV identifies
U times_V T with the iterated pullback of X along V and then T. The supplied
projection equations uniquely specify s and t under this identification.
Pullback composition supplies e₀. The isomorphism between U and X times_Y V,
direct-image composition, and uniqueness of right adjoints identify aV with b;
pulling this identification along the projection to U supplies e₁.
Likewise the scheme isomorphism U times_V T to X times_Y T, direct-image
composition, and right-adjoint uniqueness supply e₂ comparing c and b'.
Expand each mate as pullback of the right adjoint applied to the pullback unit,
followed by the inverse conjugate of ordinary base change, followed by the
pullback counit. Composite adjunction units and counits are the pasted units
and counits. Pasting ordinary base change follows by applying the adjunction
Hom equivalence and the associative derived-pullback composition comparisons.
ConjugateEquiv respects composition; conjugation takes the inverses to inverses.
Substituting these three identities in the global mate and cancelling the
adjunction unit/counit pairs with the triangle identities gives the displayed
factorization, with the open mate O.hom remaining in the middle. No inversion
of O.hom is used here. The argument remains valid on empty schemes and for
noninvertible local mates; it is an equality of morphisms, not a claim that
base change for the right adjoints is universally invertible.
-/
theorem rightAdjoint_mate_oldBase_open_factorization
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y T : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
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
    (aV : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (pullback f V.ι))
    (adjV : (schemeDerivedQCohProperty V.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f V.ι)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f V.ι)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f V.ι)) _ _ _ _
          (pullback.snd f V.ι) _ _).fst E.obj E.property) ⊣ aV)
    (hβ₀ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f V.ι) V.ι
        (pullback.fst f V.ι) pullback.condition E.obj))
    (s : pullback (f ∣_ V) gV ⟶ pullback f g0)
    (t : pullback (f ∣_ V) gV ⟶ pullback f V.ι)
    (hs₁ : s ≫ pullback.fst f g0 =
      pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι)
    (hs₂ : s ≫ pullback.snd f g0 = pullback.snd (f ∣_ V) gV)
    (ht₁ : t ≫ pullback.fst f V.ι =
      pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι)
    (ht₂ : t ≫ pullback.snd f V.ι = pullback.snd (f ∣_ V) gV ≫ gV) :
    let G := Arrow.mk ((derivedPullback s).map
      ((schemeDerivedQCohProperty (pullback f g0)).ι.map
        (@dualityEquationBaseChangeMap _ X Y T
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f g0 a c adjf adjc hβ K)))
    let O := Arrow.mk ((derivedPullback t).map
      ((schemeDerivedQCohProperty (pullback f V.ι)).ι.map
        (@dualityEquationBaseChangeMap _ X Y V.toScheme
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f V.ι a aV adjf adjV hβ₀ K)))
    let L := Arrow.mk ((schemeDerivedQCohProperty (pullback (f ∣_ V) gV)).ι.map
      (dualityEquationBaseChangeMap (f ∣_ V) gV b b' adjb adjb' hβV
        ⟨(derivedPullback V.ι).obj K.obj,
          (derivedPullback_tensor_preserve_QCoh V.ι).1 K.obj K.property⟩))
    ∃ (e₀ : G.left ≅ O.left) (e₁ : O.right ≅ L.left) (e₂ : G.right ≅ L.right),
      G.hom ≫ e₂.hom = e₀.hom ≫ O.hom ≫ e₁.hom ≫ L.hom := by sorry

end AlgebraicGeometry
