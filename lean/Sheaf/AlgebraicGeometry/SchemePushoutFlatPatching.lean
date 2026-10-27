module

public import Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.RingTheory.FibreProductAlgebraFlatPresentation
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Mathlib.RingTheory.FiniteStability
import Mathlib.AlgebraicGeometry.Gluing

/-! # Flat scheme patching over an infinitesimal pushout

Source: Stacks Project, More on Morphisms, Tags 07RV and 07RX (3) and the flat counit
(blueprint: lem-sfb-scheme-pushout-flat-patching).

The helper maps are the canonical maps obtained from the pullback and pushout
universal properties. No flatness is used in their definitions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SchemePushoutPatching

/-- The canonical structural morphism from the glued scheme to the base pushout.
Source: Stacks Project, Tag 07RV, construction of G
(blueprint: lem-sfb-scheme-pushout-flat-patching). -/
noncomputable def structureMap
    {T T' S P X Y Z : Scheme.{u}} {i : T ⟶ T'} {a : T ⟶ S}
    {j : S ⟶ P} {b : T' ⟶ P} (hp : IsPushout a i j b)
    (f : X ⟶ S) (g : Y ⟶ T') (e : pullback f a ≅ pullback g i)
    (he : e.hom ≫ pullback.snd g i = pullback.snd f a)
    {l : X ⟶ Z} {r : Y ⟶ Z}
    (hz : IsPushout (pullback.fst f a) (e.hom ≫ pullback.fst g i) l r) : Z ⟶ P :=
  hz.desc (f ≫ j) (g ≫ b) (by
    calc
      pullback.fst f a ≫ f ≫ j = pullback.snd f a ≫ a ≫ j := by
        rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = pullback.snd f a ≫ i ≫ b := by rw [hp.w]
      _ = (e.hom ≫ pullback.snd g i) ≫ i ≫ b := by rw [he]
      _ = (e.hom ≫ pullback.fst g i) ≫ g ≫ b := by
        simp only [Category.assoc, pullback.condition_assoc])

/-- The canonical map W times_P T to W times_P S, induced by a.
Source: Stacks Project, Tag 07RX, flat counit
(blueprint: lem-sfb-scheme-pushout-flat-patching). -/
noncomputable def baseChangeLeft
    {T S P W : Scheme.{u}} (a : T ⟶ S) (j : S ⟶ P) (w : W ⟶ P) :
    pullback w (a ≫ j) ⟶ pullback w j :=
  pullback.map w (a ≫ j) w j (𝟙 W) a (𝟙 P) (by simp) (by simp)

/-- The canonical map W times_P T to W times_P T', induced by i.
Source: Stacks Project, Tag 07RX, flat counit
(blueprint: lem-sfb-scheme-pushout-flat-patching). -/
noncomputable def baseChangeRight
    {T T' S P W : Scheme.{u}} {i : T ⟶ T'} {a : T ⟶ S}
    {j : S ⟶ P} {b : T' ⟶ P} (hp : IsPushout a i j b) (w : W ⟶ P) :
    pullback w (a ≫ j) ⟶ pullback w b :=
  pullback.map w (a ≫ j) w b (𝟙 W) i (𝟙 P) (by simp) (by simpa using hp.w)

end AlgebraicGeometry.SchemePushoutPatching

namespace AlgebraicGeometry

/-- Flat local finite presentation patches across an arbitrary thickening, and every
flat scheme over the pushout is recovered by the canonical counit. The existential
pushout in the second clause specifies the canonical map through `IsPushout.desc`;
its isomorphism property is independent of the representative of the pushout.

Source: Stacks Project, More on Morphisms, Tag 07RX (3) and the flat counit,
with the construction in Tag 07RV
(blueprint: lem-sfb-scheme-pushout-flat-patching).

Proof plan:
1. Apply lem-sfb-infinitesimal-pushout-affine-charts. It identifies X and Y with
   the base changes of Z and supplies charts R = B times_A A' and
   E = D times_C C', with C = D tensor_B A = C'/IC', for the actual morphisms.
2. If f and g are flat and locally finitely presented, use
   lem-weil-pbc-flat-morphism-affine-criterion and
   lem-weil-pbc-lfp-affine-opens-finite-presentation on these charts. Apply
   lem-sfb-fibre-product-algebra-flat-presentation to deduce that R to E is flat
   and finitely presented. The affine flatness criterion and
   def-sbc-locally-finite-presentation give the assertion for Z to P.
3. Conversely the chart recovery identifies f and g as base changes. Apply
   lem-weil-pbc-flat-morphism-base-change for flatness and
   lem-weil-pbc-finite-presentation-base-change-composition for finite presentation
   of the chart algebras. The charts cover by lem-weil-pbc-affine-opens-basis, so
   def-sbc-locally-finite-presentation applies to both component morphisms.
4. For a flat W to P choose affine W_0 = Spec L above affine P_0 = Spec R using
   lem-weil-pbc-affine-opens-basis. The chart lemma and
   lem-weil-pbc-fibre-product-affine-spectra give coordinate rings
   L tensor_R B, L tensor_R A', and L tensor_R A. The pushout is affine by
   lem-sfb-affine-closed-pinching-pushout. The final assertion of
   lem-sfb-fibre-product-algebra-flat-presentation identifies the canonical ring
   comparison with an isomorphism since L is flat by the affine flatness criterion.
   The inverses agree on overlaps and glue by lem-weil-pbc-scheme-morphism-gluing.
   No finite presentation of W, Noetherianity, or finite nilpotence order is used.
-/
theorem scheme_pushout_flat_patching
    {T T' S P : Scheme.{u}} (i : T ⟶ T') (a : T ⟶ S)
    (hi : IsThickening i) [IsAffineHom a]
    (j : S ⟶ P) (b : T' ⟶ P) (hp : IsPushout a i j b) :
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T')
      (e : pullback f a ≅ pullback g i)
      (he : e.hom ≫ pullback.snd g i = pullback.snd f a)
      (l : X ⟶ Z) (r : Y ⟶ Z)
      (hz : IsPushout (pullback.fst f a) (e.hom ≫ pullback.fst g i) l r),
      (Flat (SchemePushoutPatching.structureMap hp f g e he hz) ∧
        LocallyOfFinitePresentation (SchemePushoutPatching.structureMap hp f g e he hz)) ↔
      (Flat f ∧ LocallyOfFinitePresentation f) ∧ (Flat g ∧ LocallyOfFinitePresentation g)) ∧
    (∀ (W : Scheme.{u}) (w : W ⟶ P), Flat w →
      ∃ (H : Scheme.{u}) (l : pullback w j ⟶ H) (r : pullback w b ⟶ H)
        (hh : IsPushout (SchemePushoutPatching.baseChangeLeft a j w)
          (SchemePushoutPatching.baseChangeRight hp w) l r),
        IsIso (hh.desc (pullback.fst w j) (pullback.fst w b)
          (by simp [SchemePushoutPatching.baseChangeLeft,
            SchemePushoutPatching.baseChangeRight]))) := by
  sorry

end AlgebraicGeometry
