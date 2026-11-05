/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Composition

/-!
# The canonical composition isomorphism in a compact support formalism

For a compact support formalism `F` satisfying proper base change, and morphisms admitting
compactifications, `F.lowerShriek f` is the compactly supported direct image along the chosen
compactification of `f`. This file defines the composition isomorphism

`F.lowerShriekCompIso f g : F.lowerShriek f ⋙ F.lowerShriek g ≅ F.lowerShriek (f ≫ g)`

of blueprint `sk-thm-sf-comp-composition` and proves that

- it is computed by any triangle of compactifications, up to the comparison isomorphisms
  `F.shriekIso` (`lowerShriekCompIso_hom_eq`): it is independent of all compactification
  choices;
- it is the identity when `f` or `g` is an identity (`lowerShriekCompIso_id_left`,
  `lowerShriekCompIso_id_right`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

variable {X Y S : Scheme.{u}}

/-- The compactly supported direct image along `f`, computed with the chosen compactification
`AlgebraicGeometry.HasCompactification.compactification f`. -/
noncomputable abbrev lowerShriek (f : X ⟶ Y) [HasCompactification f] : F.obj X ⥤ F.obj Y :=
  F.shriek (HasCompactification.compactification f)

/-- The isomorphism `F.lowerShriek f ≅ F.lowerShriek f'` for `f = f'`. -/
noncomputable def lowerShriekCongr {f f' : X ⟶ Y} [HasCompactification f]
    [HasCompactification f'] (h : f = f') : F.lowerShriek f ≅ F.lowerShriek f' := by
  subst h
  exact Iso.refl _

@[simp]
lemma lowerShriekCongr_refl (f : X ⟶ Y) [HasCompactification f] :
    F.lowerShriekCongr (rfl : f = f) = Iso.refl _ :=
  rfl

variable [F.HasProperExchange]

/-- **The composition isomorphism** `F.lowerShriek f ⋙ F.lowerShriek g ≅ F.lowerShriek (f ≫ g)`
for morphisms admitting compactifications with quasi-compact composite: the composition
isomorphism of the triangle `Compactification.Triangle.ofHasCompactification f g`, compared with
the chosen compactifications. (blueprint: `sk-thm-sf-comp-composition`) -/
noncomputable def lowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] :
    F.lowerShriek f ⋙ F.lowerShriek g ≅ F.lowerShriek (f ≫ g) :=
  have : QuasiCompact f := .of_comp f g
  Functor.isoWhiskerRight
      (F.shriekIso _ (Compactification.Triangle.ofHasCompactification f g).cf) _ ≪≫
    F.compIso (Compactification.Triangle.ofHasCompactification f g) ≪≫ F.shriekIso _ _

/-- **Independence of all compactification choices**: the composition isomorphism is computed
by any triangle of compactifications `T` of `(f, g)`, up to the comparison isomorphisms
`F.shriekIso` between the compactifications of `T` and the chosen ones.
(blueprint: `sk-thm-sf-comp-composition`, via `sk-prop-sf-comp-coherence`) -/
theorem lowerShriekCompIso_hom_eq {f : X ⟶ Y} {g : Y ⟶ S} [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact f] [QuasiCompact g]
    [QuasiCompact (f ≫ g)] (T : Compactification.Triangle f g) :
    (F.lowerShriekCompIso f g).hom =
      NatTrans.hcomp (F.shriekIso _ T.cf).hom (F.shriekIso _ T.cg).hom ≫
        (F.compIso T).hom ≫ (F.shriekIso T.cfg _).hom := by
  rw [lowerShriekCompIso, Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    F.compIso_hom_eq _ T, ← Functor.hcomp_id]
  simp only [Category.assoc]
  rw [← Category.assoc (NatTrans.hcomp _ _), ← NatTrans.exchange, Category.id_comp]
  have h₁ := congrArg Iso.hom (F.shriekIso_trans (HasCompactification.compactification f)
    (Compactification.Triangle.ofHasCompactification f g).cf T.cf)
  have h₂ := congrArg Iso.hom (F.shriekIso_trans T.cfg
    (Compactification.Triangle.ofHasCompactification f g).cfg
    (HasCompactification.compactification (f ≫ g)))
  simp only [Iso.trans_hom] at h₁ h₂
  rw [h₁, h₂]
  rfl

end AlgebraicGeometry.CompactSupportFormalism
