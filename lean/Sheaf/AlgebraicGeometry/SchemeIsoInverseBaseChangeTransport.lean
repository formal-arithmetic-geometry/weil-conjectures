/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate
import Sheaf.AlgebraicGeometry.DerivedBaseChangePasting

/-! # The ordinary inverse square under source-isomorphism transport

Source: Stacks Project, Tags 0ATR and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

/-- Transport of the inverse ordinary base-change square along a source isomorphism.
The component formulas determine all three comparisons uniquely.
This theorem has no exceptional right adjoints and no second mates.
Source: Stacks Project, Tag 0ATR, composite adjunction calculation; Tag 0D5S.
(blueprint: lem-sc-scheme-iso-inverse-base-change-transport)

Proof: The pinned pullback adjunction of each source isomorphism is an equivalence:
pullback along its inverse is an inverse functor by the canonical composition and
identity comparisons. Thus its unit, and hence the explicitly constructed unit
comparison q, is invertible. Transpose ordinary base change under the pinned
pullback/direct-image adjunctions. Apply derived base-change pasting to r and use
hr₂ for the upper direct-image comparison. Apply pullback composition to the other
projection and use hr₁ and he. The associativity law for the fixed composition
comparisons identifies these transposes. Injectivity of the Hom equivalences gives
the ordinary-square equation with the specified k, q and σ. Invert the two ordinary
base-change transformations, which are isomorphisms by hβ and hβf; cancel them on
the two sides. Naturality moves k and q through the composites and gives exactly
the displayed inverse-square equation. The component identity for q is recorded
after two arbitrary postcompositions, using associativity; identity arrows recover
the unpostcomposed component. It holds for every quasi-coherent object,
including the zero object, and on empty schemes: only naturality, composition and
triangle identities are used. Restriction to quasi-coherent objects is legitimate
by pullback and qcqs direct-image preservation; full faithfulness gives the same
equality in the full subcategories. -/
theorem schemeIso_inverseBaseChange_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f') (g : T ⟶ S)
    (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f' g)
    [IsIso r]
    [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (pullback f' g : Scheme.{u})]
    (hβ : ∀ E : schemeDerivedQCohCategory U,
      IsIso (schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
        (pullback.fst f' g) pullback.condition E.obj))
    (hβf : ∀ E : schemeDerivedQCohCategory P,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj)) :
    let adj := fun {X Y : Scheme.{u}} (v : X ⟶ Y) ↦
      Classical.choose (exists_schemeDerivedAdjunction v
        (hAdd := (Classical.choose exists_derivedPullbackComposition) v)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) v)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) v))
    let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let ce := comp e.hom f ≪≫ eqToIso (congrArg (fun v ↦ derivedPullback v) he)
    let cr := comp (asIso r).hom (pullback.snd f g) ≪≫
      eqToIso (congrArg (fun v ↦ derivedPullback v) hr₂)
    let δe := conjugateIsoEquiv (adj f') ((adj f).comp (adj e.hom)) ce
    let δr := conjugateIsoEquiv (adj (pullback.snd f' g))
      ((adj (pullback.snd f g)).comp (adj (asIso r).hom)) cr
    ∃ (k : qcDirectImage f ⟶ qcPullback e.hom ⋙ qcDirectImage f')
      (q : qcDirectImage (pullback.snd f g) ⟶
        qcPullback r ⋙ qcDirectImage (pullback.snd f' g))
      (σ : qcPullback (pullback.fst f g) ⋙ qcPullback r ≅
        qcPullback e.hom ⋙ qcPullback (pullback.fst f' g)),
      IsIso q ∧
      (∀ E : schemeDerivedQCohCategory P,
        q.app ((qcPullback (pullback.fst f g)).obj E) ≫
          (qcDirectImage (pullback.snd f' g)).map (σ.hom.app E) ≫
          (qcInverseBaseChange f' g hβ).app ((qcPullback e.hom).obj E) =
        (qcInverseBaseChange f g hβf).app E ≫ (qcPullback g).map (k.app E)) ∧
      (∀ E : schemeDerivedQCohCategory P,
        (k.app E).hom = (schemeDerivedDirectImage f).map
          ((adj e.hom).unit.app E.obj) ≫
            δe.inv.app ((derivedPullback e.hom).obj E.obj)) ∧
      (∀ (E : schemeDerivedQCohCategory (pullback f g))
          (A B : schemeDerivedCategory T)
          (t : ((qcPullback r ⋙ qcDirectImage (pullback.snd f' g)).obj E).obj ⟶ A)
          (v : A ⟶ B),
        (q.app E).hom ≫ t ≫ v =
          (schemeDerivedDirectImage (pullback.snd f g)).map
            ((adj (asIso r).hom).unit.app E.obj) ≫
          δr.inv.app ((derivedPullback (asIso r).hom).obj E.obj) ≫ t ≫ v) ∧
      (∀ E : schemeDerivedQCohCategory P,
        (σ.hom.app E).hom =
          (comp r (pullback.fst f g)).hom.app E.obj ≫
            eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hr₁) ≫
            (comp (pullback.fst f' g) e.hom).inv.app E.obj) := by sorry

end
end AlgebraicGeometry
