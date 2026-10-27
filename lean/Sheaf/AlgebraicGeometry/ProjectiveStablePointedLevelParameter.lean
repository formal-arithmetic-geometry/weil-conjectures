/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition

/-! # A projective level parameter for stable pointed curves

Source: de Jong, Smoothness, semi-stability and alterations (1996), §2.24 and §4.17;
Pikaart--de Jong (1995), §2.3.3--2.3.7; Knudsen (1983), II §2
(blueprint: lem-sfb-projective-stable-pointed-level-parameter).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective finite-type level parameter with a universal stable labelled family.
Representability is expressed by a universal pair `(mP, eP)` and the unique classifying
map `q` for every test pair `(m, e)`. The morphism `v` is the canonical map of the
pullbacks of the universal family: its two projection equations determine it uniquely.
The last equation identifies the two isomorphisms after projection to `C`; their other
projection agrees because both isomorphisms are over the test scheme. This is precisely
pullback of the universal pair, and supplies the natural, rather than pointwise, bijection.

Source: de Jong (1996), §2.24, printed p.62, and §4.17, pp.71--72, with the genus-at-least-two
extension to all marking numbers by Pikaart--de Jong (1995), §2.3.3--2.3.7 and Knudsen II §2
(blueprint: lem-sfb-projective-stable-pointed-level-parameter).

Proof plan:
1. Choose level 3 in characteristic different from 3 and level 5 otherwise. Apply
   lem-sfb-smooth-curve-abelian-level-rigidification, retaining all components of the level
   cover. Use def-sfb-stable-pointed-moduli-groupoids to interpret its maps as actual families.
2. Apply lem-sfb-unpointed-stable-coarse-projective and
   lem-sfb-stable-abelian-level-normalization to normalize the projective coarse space in
   this cover, obtaining M0 and its stable unpointed family. By lem-fin-finite-over-projective
   over Spec k, M0 is H-projective. By lem-pc-projective-proper and def-weil-proper-morphism
   it is finite type. The two projective conventions agree here by quasi-compactness.
3. Inductively take the universal curve as the next parameter scheme. Apply
   lem-sfb-knudsen-pointed-forgetful-universal-curve for its next marking and family.
   lem-weil-pbc-projective-ample-invertible supplies an ample invertible sheaf on each
   projective base. lem-trf-projective-bundle-to-h-projective and
   lem-trf-h-projective-composition give H-projectivity at the next step; properness gives
   finite type. This includes n = 0 and adds no auxiliary markings.
4. Pulling the resulting family back along any map yields a stable family, by the
   base-change clause of lem-sfb-knudsen-pointed-forgetful-universal-curve and the meaning
   of maps to def-sfb-stable-pointed-moduli-groupoids. This proves (a).
5. Over a smooth marked curve, the successive 2-cartesian universal-curve squares identify
   its labelled-isomorphism pairs with unpointed-isomorphism pairs over M0. Forgetting
   markings requires no stabilization because the smooth genus is at least two. Conversely
   transport each marking along the unpointed isomorphism. These operations are inverse
   and commute with pullback; no automorphism or permutation quotient is taken.
6. The smooth-locus square of lem-sfb-stable-abelian-level-normalization identifies this
   functor with the level-frame functor. By lem-sfb-smooth-curve-abelian-level-rigidification
   it is represented by a finite etale surjective scheme P over F. It is nonempty even
   when it has no F-point. Its universal pair and unique classifying maps give (b).
-/
theorem exists_projective_stable_pointed_level_parameter
    (k : Type u) [Field k] (g n : ℕ) (hg : 2 ≤ g) :
    ∃ (M : Scheme.{u}) (a : M ⟶ Spec (.of k)),
      LocallyOfFiniteType a ∧ QuasiCompact a ∧ IsHProjective a ∧
      ∃ (U : Scheme.{u}) (f : U ⟶ M) (t : Fin n → (M ⟶ U))
        (ht : ∀ i, t i ≫ f = 𝟙 M),
        (∀ (B : Scheme.{u}) (b : B ⟶ Spec (.of k)) (m : B ⟶ M),
          m ≫ a = b →
          IsStablePointedCurve (pullback.snd f m)
            (fun i : Fin n ↦ f.baseChangeSection (t i) (ht i) m)
            (fun i : Fin n ↦ Scheme.Hom.baseChangeSection_snd f (t i) (ht i) m)) ∧
        ∀ (F : Type u) [Field F] [Algebra k F]
          (C : Scheme.{u}) [C.Over (Spec (.of F))],
          Smooth (C ↘ Spec (.of F)) → IsHProjective (C ↘ Spec (.of F)) →
          GeometricallyIntegral (C ↘ Spec (.of F)) →
          topologicalKrullDim C = 1 → C.arithmeticGenus F = g →
          ∀ (p : Fin n → (Spec (.of F) ⟶ C))
            (hp : ∀ i, p i ≫ C ↘ Spec (.of F) = 𝟙 (Spec (.of F))),
            Function.Injective p →
            ∃ (P : Scheme.{u}) (r : P ⟶ Spec (.of F)),
              Nonempty P ∧ IsFinite r ∧ Etale r ∧
              ∃ (mP : P ⟶ M),
                mP ≫ a = r ≫ Spec.map (CommRingCat.ofHom (algebraMap k F)) ∧
                ∃ (eP : pullback f mP ≅ pullback (C ↘ Spec (.of F)) r),
                  eP.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
                  (∀ i : Fin n, f.baseChangeSection (t i) (ht i) mP ≫ eP.hom =
                    (C ↘ Spec (.of F)).baseChangeSection (p i) (hp i) r) ∧
                  ∀ (B : Scheme.{u}) (b : B ⟶ Spec (.of F)) (m : B ⟶ M),
                    m ≫ a = b ≫ Spec.map (CommRingCat.ofHom (algebraMap k F)) →
                    ∀ (e : pullback f m ≅ pullback (C ↘ Spec (.of F)) b),
                      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ →
                      (∀ i : Fin n, f.baseChangeSection (t i) (ht i) m ≫ e.hom =
                        (C ↘ Spec (.of F)).baseChangeSection (p i) (hp i) b) →
                      ∃! q : B ⟶ P, q ≫ r = b ∧ q ≫ mP = m ∧
                        ∃ v : pullback f m ⟶ pullback f mP,
                          v ≫ pullback.fst f mP = pullback.fst f m ∧
                          v ≫ pullback.snd f mP = pullback.snd f m ≫ q ∧
                          v ≫ eP.hom ≫ pullback.fst (C ↘ Spec (.of F)) r =
                            e.hom ≫ pullback.fst (C ↘ Spec (.of F)) b := by
  sorry

end AlgebraicGeometry
