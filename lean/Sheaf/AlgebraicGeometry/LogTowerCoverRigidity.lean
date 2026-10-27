/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.LogBlowupFullPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-!
# Rigidity and common-cover comparison of log blowup towers

Source: ILO VIII 3.3.7--3.3.10 and proof of 3.3.15, printed pp.107--110
(blueprint: lem-trf-log-tower-cover-rigidity).

Full comparisons exhibit recursive uncontracted pullbacks. Their Cartesian squares
are in fs log schemes. No center is recovered merely from its blowup space.
The product of two objects of the small étale site is their scheme fibre product.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The cocycle equation for three ordered center-preserving tower isomorphisms,
including the actual log-section maps. Source: ILO VIII proof of 3.3.15, pp.109--110
(blueprint: lem-trf-log-tower-cover-rigidity). -/
def LogBlowupTowerIso.IsComposite {X : FineSaturatedLogScheme.{u}}
    {A B C : LogBlowupTowerOver X} (e : LogBlowupTowerIso A B)
    (f : LogBlowupTowerIso B C) (g : LogBlowupTowerIso A C) : Prop :=
  (∀ i, f.index (e.index i) = g.index i) ∧
    ∀ i, ∃ r : EtaleLogHom (C.tower.level (g.index i)) (B.tower.level (e.index i)),
      HEq r (f.forward (e.index i)) ∧ r.CompEq (e.forward i) (g.forward i)

/-- Ideal detection, prescribed lifting, rigidity, equality tests, common-cover comparison,
cocycles, and normalization on the identity cover.
Source: ILO VIII 3.3.7--3.3.10 and proof of 3.3.15, pp.107--110
(blueprint: lem-trf-log-tower-cover-rigidity).

Proof plan (the six steps of the DAG node):
1. Base-change the surjective étale cover to each test object. The sheaf equalizer
for an ideal glues a section whose restriction belongs to it; separatedness of the
log sheaf identifies the glued section with the original one. Apply to both ideals.
This uses lem-weil-pbc-etale-covering-base-change and the sheaf and fs-log definitions.
2. Induct on the ordered blowups. Two center-preserving isomorphisms agree at level
zero. At each successor, the universal saturated blowup property makes their lifts
of the same log map equal. This includes their section maps and the zero-length case.
3. For a prescribed local isomorphism, synchronize the full pullback at each level
using lem-trf-log-tower-cover-synchronization. The level covers are surjective strict
étale. Transport the next center by the already descended level isomorphism; step 1
identifies this actual ideal with the source center.
4. The blowup universal property now supplies the next lift. Construct the reverse
lift in the same way; uniqueness makes both composites identities and identifies
the pullback of the constructed lift with the prescribed local lift.
5. Finite induction constructs the ordered isomorphism. Step 2 gives uniqueness and
detects all equalities, including equations between composites, on the cover.
6. For two covers, take their fs fibre product, which is the ordinary scheme fibre
product because the maps are strict. Associate recursive pullbacks by their universal
properties. Apply steps 3--5 first over the first cover and then over the base.
This gives equal lengths and the unique comparison of the descended towers.
Uniqueness gives the three-choice cocycle, compatibility with any specified descent
data, and the comparison with the original tower for the identity cover.
No contraction is applied to a full pullback and proper principal centers are retained. -/
theorem log_tower_cover_rigidity :
    (∀ (X U : FineSaturatedLogScheme.{u}) (f : EtaleLogHom U X),
      f.IsStrict → ∀ [Etale f.base], Function.Surjective f.base →
      (∀ (I J : X.logStructure.IdealFamily),
        X.logStructure.IsIdeal I → X.logStructure.IsIdeal J →
        f.pullbackIdeal I = f.pullbackIdeal J → I = J) ∧
      (∀ (I : X.logStructure.IdealFamily), X.logStructure.IsIdeal I →
        ∀ (W : X.scheme.Etale) (s : X.logStructure.monoidSheaf.obj.obj (op W)),
          s ∈ I W ↔
            X.logStructure.monoidSheaf.obj.map
              (prod.fst (X := W) (Y := Scheme.Etale.mk f.base)).op s ∈
                I (W ⨯ Scheme.Etale.mk f.base))) ∧
    (∀ (X U : FineSaturatedLogScheme.{u}) (f : EtaleLogHom U X),
      f.IsStrict → Etale f.base → Function.Surjective f.base →
      ∀ (B C : LogBlowupTowerOver X) (S T : LogBlowupTowerOver U)
        (p : LogBlowupFullPullback f B S) (q : LogBlowupFullPullback f C T)
        (a : LogBlowupTowerIso S T),
        ∃! e : LogBlowupTowerIso B C, e.IsPullbackIso p q a) ∧
    (∀ (X : FineSaturatedLogScheme.{u}) (B C : LogBlowupTowerOver X),
      Subsingleton (LogBlowupTowerIso B C)) ∧
    (∀ (X U : FineSaturatedLogScheme.{u}) (f : EtaleLogHom U X),
      f.IsStrict → Etale f.base → Function.Surjective f.base →
      ∀ (B C : LogBlowupTowerOver X) (S T : LogBlowupTowerOver U)
        (p : LogBlowupFullPullback f B S) (q : LogBlowupFullPullback f C T)
        (e e' : LogBlowupTowerIso B C) (a a' : LogBlowupTowerIso S T),
        e.IsPullbackIso p q a → e'.IsPullbackIso p q a' → (e = e' ↔ a = a')) ∧
    (∀ (X U : FineSaturatedLogScheme.{u}) (f : EtaleLogHom U X),
      f.IsStrict → Etale f.base → Function.Surjective f.base →
      ∀ (B C D : LogBlowupTowerOver X) (S T R : LogBlowupTowerOver U)
        (p : LogBlowupFullPullback f B S) (q : LogBlowupFullPullback f C T)
        (r : LogBlowupFullPullback f D R)
        (a : LogBlowupTowerIso B C) (b : LogBlowupTowerIso C D)
        (c : LogBlowupTowerIso B D) (α : LogBlowupTowerIso S T)
        (β : LogBlowupTowerIso T R) (γ : LogBlowupTowerIso S R),
        a.IsPullbackIso p q α → b.IsPullbackIso q r β → c.IsPullbackIso p r γ →
          (a.IsComposite b c ↔ α.IsComposite β γ)) ∧
    (∀ (X U V W : FineSaturatedLogScheme.{u})
      (f : EtaleLogHom U X) (g : EtaleLogHom V X)
      (r : EtaleLogHom W U) (s : EtaleLogHom W V),
      f.IsStrict → Etale f.base → Function.Surjective f.base →
      g.IsStrict → Etale g.base → Function.Surjective g.base →
      r.IsFSPullback f s g →
      ∀ (B C : LogBlowupTowerOver X)
        (S : LogBlowupTowerOver U) (T : LogBlowupTowerOver V),
        S.IsContracted → T.IsContracted →
        LogBlowupFullPullback f B S → LogBlowupFullPullback g C T →
        ∀ (S' T' : LogBlowupTowerOver W),
          LogBlowupFullPullback r S S' → LogBlowupFullPullback s T T' →
          LogBlowupTowerIso S' T' →
          B.tower.length = C.tower.length ∧
            Nonempty (LogBlowupTowerIso B C) ∧ Subsingleton (LogBlowupTowerIso B C)) ∧
    (∀ (X : FineSaturatedLogScheme.{u}) (A B C : LogBlowupTowerOver X)
      (e : LogBlowupTowerIso A B) (f : LogBlowupTowerIso B C)
      (g : LogBlowupTowerIso A C), e.IsComposite f g) ∧
    (∀ (X : FineSaturatedLogScheme.{u}), IsChartedLogBlowupInput X →
      ∀ (B C : LogBlowupTowerOver X) (f : EtaleLogHom X X),
        f.IsIdentity → LogBlowupFullPullback f B C →
          Nonempty (LogBlowupTowerIso B C)) := by
  sorry

end AlgebraicGeometry
