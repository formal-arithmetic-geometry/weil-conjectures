/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.RingTheory.FlatUnderRegular

/-!
# Reduced regular centers from étale closed models

Source: Stacks Project, Tags 034E, 01J3, 01JU, 02GO and 00OF; the regular-center
argument in ILO VIII 4.1.8, printed p. 118
(blueprint: lem-trf-etale-reduced-regular-center).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/-- The reduced closed subscheme of a closed subset is regular if it has regular reduced
closed models étale locally at every point. Every such model is the actual base change,
with the same ideal sheaf and canonically isomorphic local rings. The map from a model to
this reduced closed subscheme induces flat local maps of Noetherian local rings. On an
affine chart cut out by finitely many specified equations, the extended ideal is their
ideal itself. The global ideal is finitely generated on every affine open and is the
radical ideal of the given closed subset. The empty subset is included.

Source: Stacks Project, descent.tex Tag 034E, schemes.tex Tags 01J3 and 01JU,
morphisms.tex Tag 02GO, algebra.tex Tags 00OF and 00FN; ILO VIII 4.1.8, printed p. 118
(blueprint: lem-trf-etale-reduced-regular-center).

Proof:
1. On each affine open of X, its ring is Noetherian (pqf-lem-affine-open-locnoeth).
   The reduced induced subscheme is the quotient by the radical vanishing ideal
   (lem-weil-pbc-reduced-induced-closed-subscheme). This ideal is finitely generated
   (def-weil-pbc-noetherian-ring). The quotient is Noetherian by finite type with no
   algebra generators (lem-weil-pbc-finite-type-algebra-noetherian), and its prime
   localizations are Noetherian (lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-localization-noetherian).
2. The first clause of lem-trf-etale-reduced-cartier-descent identifies the pullback
   with the reduced induced structure on the inverse image. Both it and C are reduced
   with the same image, so uniqueness in lem-weil-pbc-reduced-induced-closed-subscheme
   gives their equal ideal sheaves and their unique isomorphism over W. Its stalk maps
   give the canonical local-ring isomorphisms.
3. By lem-pc-closed-subscheme-base-change-ideal-image, the extended ideal is the ideal
   of this pullback. Hence it is the ideal of C (def-sbc-closed-immersion-ideal-sheaf).
   If C is cut out by the displayed finite family, it is exactly its generated ideal,
   without taking a radical. For zero equations this is the zero ideal.
4. The projection to the reduced center is étale by lem-weil-pbc-etale-scheme-base-change.
   It is flat by def-weil-etale-morphism, and its stalk maps are flat local maps by
   def-weil-flat-morphism. Their target rings are regular Noetherian local rings by
   def-weil-regular-scheme, and their source rings are Noetherian by step 1.
   Apply lem-weil-pbc-flat-under-regular to descend regularity at every covered point.
5. Local Noetherianity from step 1 and stalk regularity from step 4 give
   IsRegularScheme. For the empty subset the reduced subscheme is empty, the stalk
   assertions are vacuous, and the ideal is the finitely generated unit ideal.
-/
theorem etale_reduced_regular_center
    (X : Scheme.{u}) [IsLocallyNoetherian X] (T : TopologicalSpace.Closeds X)
    (hcharts : ∀ x ∈ T, ∃ (W : Scheme.{u}) (e : W ⟶ X),
      Etale e ∧ ∃ w : W, e w = x ∧
        ∃ (C : Scheme.{u}) (i : C ⟶ W),
          IsClosedImmersion i ∧ IsRegularScheme C ∧ IsReduced C ∧
            Set.range i = e ⁻¹' (T : Set X)) :
    IsRegularScheme (vanishingIdeal T).subscheme ∧
    (∀ (W : Scheme.{u}) (e : W ⟶ X) [Etale e]
        (C : Scheme.{u}) (i : C ⟶ W) [IsClosedImmersion i] [IsReduced C],
      IsRegularScheme C → Set.range i = e ⁻¹' (T : Set X) →
        (vanishingIdeal T).comap e = i.ker ∧
        (pullback.snd (vanishingIdeal T).subschemeι e).ker = i.ker ∧
        (∃! φ : C ≅ pullback (vanishingIdeal T).subschemeι e,
          φ.hom ≫ pullback.snd (vanishingIdeal T).subschemeι e = i ∧
          ∀ c : C, IsIso (φ.hom.stalkMap c) ∧
            ((φ.hom ≫ pullback.fst (vanishingIdeal T).subschemeι e).stalkMap c).hom.Flat ∧
            IsLocalHom
              ((φ.hom ≫ pullback.fst (vanishingIdeal T).subschemeι e).stalkMap c).hom ∧
            IsNoetherianRing ((vanishingIdeal T).subscheme.presheaf.stalk
              ((φ.hom ≫ pullback.fst (vanishingIdeal T).subschemeι e) c)) ∧
            IsNoetherianRing (C.presheaf.stalk c) ∧
            IsRegularLocalRing (C.presheaf.stalk c)) ∧
        (∀ (A : CommRingCat.{u}) (a : W ≅ Spec A) (n : ℕ) (t : Fin n → A),
          (i ≫ a.hom).ker =
              ofIdealTop ((Ideal.span (Set.range t)).comap (Scheme.ΓSpecIso A).hom.hom) →
            (vanishingIdeal T).comap (a.inv ≫ e) =
              ofIdealTop ((Ideal.span (Set.range t)).comap (Scheme.ΓSpecIso A).hom.hom))) ∧
    (∀ U : X.affineOpens,
      ((vanishingIdeal T).ideal U).FG ∧
      ((vanishingIdeal T).ideal U).IsRadical ∧
      (vanishingIdeal T).ideal U =
        PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (T : Set X))) ∧
    (T = ⊥ → IsEmpty (vanishingIdeal T).subscheme) := by
  sorry

end AlgebraicGeometry
