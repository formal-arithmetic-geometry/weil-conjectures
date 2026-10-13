/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeIsoRightAdjointNormalized
public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
import Sheaf.AlgebraicGeometry.DerivedBaseChangePasting

/-! # Commutation of normalized source-isomorphism transport with the second mate

Source: Stacks Project, Tags 0ATR and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- The source comparison uses only pullback composition and the supplied comparison of
right adjoints. All its data are explicit; no witness of existence is chosen.
Source: Stacks Project, Tags 0ATR and 0D5S. -/
def schemeIsoMateSourceIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    (f : P ⟶ S) (f' : U ⟶ S) (e : U ≅ P) (g : T ⟶ S)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (K : schemeDerivedQCohCategory S) (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
      b ⋙ (schemeDerivedQCohProperty U).ι) :
    (derivedPullback r).obj
        ((derivedPullback (pullback.fst f g)).obj (a.obj K).obj) ≅
      (derivedPullback (pullback.fst f' g)).obj (b.obj K).obj :=
  let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  (comp r (pullback.fst f g)).app (a.obj K).obj ≪≫
    eqToIso (congrArg (fun k ↦ (derivedPullback k).obj (a.obj K).obj) hr₁) ≪≫
    ((comp (pullback.fst f' g) e.hom).app (a.obj K).obj).symm ≪≫
    (derivedPullback (pullback.fst f' g)).mapIso (φ.app K)

/-- The normalized endpoint comparisons commute with the fixed second-mate formula.
Unlike the transport theorem, this asserts an equality of specified morphisms;
it neither supplies endpoint isomorphisms nor constructs an arrow isomorphism.
Source: Stacks Project, Tag 0ATR, composite adjunction and conjugate calculation.
(blueprint: lem-sc-scheme-iso-second-mate-normalized-square)

Proof: Expand the fixed second mate into pullback of the base unit, pullback of the
inverse conjugate of ordinary base change, and the upper counit. The normalization
of φ and ψ is the counit identity for the transported vertical adjunctions; by
adjunction transposition it gives their unit identities too. Transpose the ordinary
base-change maps under the canonical pullback/direct-image adjunctions. Use he,
hr₁ and hr₂ and associativity of the fixed pullback composition comparisons to
identify these transposes. Injectivity of the Hom equivalences identifies ordinary
base change after transport. ConjugateEquiv respects this equality and the endpoint
comparisons; as ordinary base change is invertible, its conjugate inverse respects
it as well. Substitute in the expanded second-mate formulas. Move the normalized
comparisons past the units and counits by the preceding identities, and cancel
the inverse comparison pairs. The remaining equation is the stated square, with
its source comparison the explicit pullback-composition expression above. No
second mate is inverted. Zero objects and empty schemes require no extra cases. -/
theorem schemeIso_secondMate_normalized_square
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f') (g : T ⟶ S)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (d : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f g))
    (b' : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f' g))
    (adja : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
        f _ _).fst E.obj E.property) ⊣ a)
    (adjb : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty U).ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _
        f' _ _).fst E.obj E.property) ⊣ b)
    (adjd : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙ schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ d)
    (adjb' : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f' g)).ι ⋙ schemeDerivedDirectImage (pullback.snd f' g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f' g)) _ _ _ _
        (pullback.snd f' g) _ _).fst E.obj E.property) ⊣ b')
    (hβ : ∀ E : schemeDerivedQCohCategory U,
      IsIso (schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
        (pullback.fst f' g) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory S)
    (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f' g)
    [IsIso r]
    [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (pullback f' g : Scheme.{u})]
    (hβf : ∀ E : schemeDerivedQCohCategory P,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
      b ⋙ (schemeDerivedQCohProperty U).ι)
    (ψ : (d ⋙ (schemeDerivedQCohProperty (pullback f g)).ι) ⋙ derivedPullback r ≅
      b' ⋙ (schemeDerivedQCohProperty (pullback f' g)).ι)
    (hφ : SchemeIsoRightAdjointNormalized f f' e he a b adja adjb φ)
    (hψ : SchemeIsoRightAdjointNormalized (pullback.snd f g) (pullback.snd f' g)
      (asIso r) hr₂ d b' adjd adjb' ψ) :
    (schemeIsoMateSourceIso f f' e g a b K r hr₁ φ).hom ≫
        (dualityEquationBaseChangeMap f' g b b' adjb adjb' hβ K).hom =
      (derivedPullback r).map
          (dualityEquationBaseChangeMap f g a d adja adjd hβf K).hom ≫
        ψ.hom.app (((schemeDerivedQCohProperty T).lift
          ((schemeDerivedQCohProperty S).ι ⋙ derivedPullback g)
          (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)).obj K)
    := by sorry

end
end AlgebraicGeometry
