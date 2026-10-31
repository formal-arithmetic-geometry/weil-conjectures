/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedCurve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.FieldTheory.FieldTower
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.TraceFormula.FiniteResiduePointClosedInFibre
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Extension of a stable generic pointed curve

Source: de Jong, Families of curves and alterations (1997), §3.6 and Lemma 3.7,
printed p.608 (blueprint: lem-sfb-stable-pointed-generic-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A smooth projective geometrically integral generic curve of genus at least two with
finitely many distinct rational markings extends over a finite separable alteration.
The generic isomorphism respects each label. Consequently it also respects the unordered
marking convention. Stability is asserted after every base change, including an empty base.

Source: de Jong (1997), §3.6 and Lemma 3.7, printed p.608
(blueprint: lem-sfb-stable-pointed-generic-extension).

Proof plan:
1. Apply lem-sfb-projective-stable-pointed-level-parameter with the given genus and marking
   number. Its nonempty finite etale isomorphism parameter over K is Spec A. By
   lem-weil-pbc-etale-algebra-over-field-product choose a factor L/K, finite separable.
   This gives an actual labelled generic isomorphism, not merely a coarse moduli point.
2. Normalize S in L using def-fin-normalization-extension and
   lem-weil-pbc-normalization-in-residue-field-extension. The normalization is integral
   with function field L, and is finite by lem-fin-normalization-extension-finite.
   By lem-weil-pbc-finite-closed-map-finite-fibres it is proper and closed; its image
   contains the generic point, hence is all of S. It is finite type over k by
   lem-sfb-finite-type-composition-base-change.
3. Form the product of this normalization with the projective level parameter M.
   The projection is proper by lem-pc-projective-proper and lem-pc-proper-base-change.
   The selected L-point is closed in its generic fibre by
   lem-trf-finite-residue-point-closed-in-fibre: its residue field is exactly L.
4. Take its reduced closure T using lem-weil-pbc-reduced-induced-closed-subscheme.
   It is integral. On an affine chart the closure is B/p; localizing at the nonzero
   elements of the base domain gives the reduced closed L-point, hence L. Every
   chart meeting the closure contains its generic point. Thus the generic fibre is
   precisely Spec L and the function field of T is L.
5. By lem-weil-pbc-closed-immersion-proper and lem-weil-pbc-proper-composition,
   T maps properly and surjectively to S. The base S is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Apply
   lem-weil-pbc-generic-finite-morphism-open-neighborhood to obtain a dense open
   over which the map is finite. This is the required finite separable alteration.
6. Pull the universal pointed curve back to T. The selected generic isomorphism from
   step 1, with associativity of fibre products, identifies its labelled generic fibre.
   Clause (a) of the level-parameter theorem gives every stable condition, also after
   arbitrary base change, even over nonreduced, disconnected or empty schemes.
-/
theorem exists_stable_pointed_generic_extension
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S] [S.Over (Spec (.of k))]
    [IsHProjective (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (C : Scheme.{u}) [C.Over (Spec S.functionField)]
    [Smooth (C ↘ Spec S.functionField)] [IsHProjective (C ↘ Spec S.functionField)]
    [GeometricallyIntegral (C ↘ Spec S.functionField)]
    (hdim : topologicalKrullDim C = 1) (hgenus : 2 ≤ C.arithmeticGenus S.functionField)
    (n : ℕ) (p : Fin n → (Spec S.functionField ⟶ C))
    (hp : ∀ i, p i ≫ C ↘ Spec S.functionField = 𝟙 (Spec S.functionField))
    (hdistinct : Function.Injective p) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (r : T ⟶ S),
      LocallyOfFiniteType r ∧ QuasiCompact r ∧ IsProper r ∧ Surjective r ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (r ∣_ U)) ∧
      ∃ (hr : r (genericPoint T) = genericPoint S)
        (_ : Algebra S.functionField T.functionField),
        algebraMap S.functionField T.functionField =
          (S.presheaf.stalkSpecializes (specializes_of_eq hr) ≫
            r.stalkMap (genericPoint T)).hom ∧
        Module.Finite S.functionField T.functionField ∧
        Algebra.IsSeparable S.functionField T.functionField ∧
        ∃ (W : Scheme.{u}) (f : W ⟶ T) (s : Fin n → (T ⟶ W))
          (hs : ∀ i, s i ≫ f = 𝟙 T),
          IsStablePointedCurve f s hs ∧
          (∃ e : pullback f (T.fromSpecStalk (genericPoint T)) ≅
              pullback (C ↘ Spec S.functionField)
                (Spec.map (CommRingCat.ofHom (algebraMap S.functionField T.functionField))),
            e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
            ∀ i : Fin n,
              f.baseChangeSection (s i) (hs i) (T.fromSpecStalk (genericPoint T)) ≫
                e.hom =
              (C ↘ Spec S.functionField).baseChangeSection (p i) (hp i)
                (Spec.map (CommRingCat.ofHom (algebraMap S.functionField T.functionField)))) ∧
          ∀ (T' : Scheme.{u}) (a : T' ⟶ T),
            IsStablePointedCurve (pullback.snd f a)
              (fun i : Fin n ↦ f.baseChangeSection (s i) (hs i) a)
              (fun i : Fin n ↦ Scheme.Hom.baseChangeSection_snd f (s i) (hs i) a) := by
  sorry

end AlgebraicGeometry
