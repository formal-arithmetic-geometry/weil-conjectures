/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap

/-! # Unit compatibility of the sheaf direct-image square mate

Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-pc-derived-pushforward-square-mate-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The sheaf-level unit equation for the square conjugate.
Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-pc-derived-pushforward-square-mate-unit).
Proof: take the underived comparison obtained from pushforwardComp along p,f,
the equality p ≫ f = q ≫ g, and the inverse pushforwardComp along q,g.
It acts as the identity on sections of the whole open. Transpose the defining
left-derived composition factorization using the normalized Hom equations of
exists_schemeDerivedAdjunction for each of the four morphisms.
For each morphism h write ε_h for the shared left-derived counit and β_h
for its right-derived unit. Substitute the ordinary adjunction unit into
its normalized Hom equation. This gives η_h at QN followed by Rh(ε_h at N)
equal to the localized ordinary unit followed by β_h at the ordinary
pullback of N. Substitute the ordinary counit instead and transpose back;
this gives Lh(β_h at K) followed by the derived adjunction counit equal to
ε_h at the ordinary pushforward of K followed by the localized ordinary
counit. These identities hold for every homotopy object N and K.
Paste each identity twice using the composite adjunction unit and counit
formulas. Naturality of ε and β moves the inner factor across the outer
one. The defining left-derived composition factorization replaces the
pasted ε for g,q and for f,p by the common composite ε and the ordinary
pullback comparison. The ordinary comparison is the conjugate of e by
construction. Expand the derived conjugate as its unit, the image of k,
and its counit. The pasted factorization identities just obtained replace
these three factors by the localization of the ordinary conjugate and the
pasted β for q,g. The ordinary adjunction triangle identities remove the
remaining ordinary unit/counit pairs. This leaves precisely the localized
e followed by the q,g units on one side and the p,f units followed by δ
on the other. No ε or β is cancelled: only their factorization equations,
naturality and adjunction triangle identities are used. The equations
therefore hold on every J, without a K-injectivity hypothesis on J.
For identity squares it is the unit identity; on zero complexes both sides vanish. -/
theorem exists_derivedPushforwardSquareMateUnit
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    let P₀ := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
    let Q₀ := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let RF := schemeDerivedDirectImage f
    let RG := schemeDerivedDirectImage g
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
    let p : ∀ {X Y Z : Scheme.{u}} (h : X ⟶ Y) (i : Y ⟶ Z),
        derivedPullback i ⋙ derivedPullback h ≅ derivedPullback (h ≫ i) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h)
        (pullback.condition (f := f) (g := g)).symm) ≪≫
      (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    ∃ e : P₀ ⋙ F₀ ≅ Q₀ ⋙ G₀,
      (∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : M.val.obj (op ⊤)), ((e.hom.app M).val.app (op ⊤)) x = x) ∧
      ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (.up ℤ),
        F₀.rightDerivedFunctorUnit.app ((P₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RF.map (P₀.rightDerivedFunctorUnit.app J) ≫
          δ.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
          G₀.rightDerivedFunctorUnit.app ((Q₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RG.map (Q₀.rightDerivedFunctorUnit.app J) := by sorry

end AlgebraicGeometry
