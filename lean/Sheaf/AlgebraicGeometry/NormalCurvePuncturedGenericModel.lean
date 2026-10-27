module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# A punctured normal curve with a prescribed generic morphism

Source: Stacks Project, Limits, Tag 0GWV, final paragraph of the proof of
`lemma-essentially-finite-type-criterion-universally-closed`, and Morphisms, Tag 0BX8.
(blueprint: lem-sfb-normal-curve-punctured-generic-model)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A finite generic field extension admits a normal finite type curve model with a point
above the specified closed point and the prescribed morphism on its punctured complement.
The residue-field isomorphism and the last three equations specify the generic restrictions;
in particular the equation for `p` makes the identification compatible with the given `K`.
No separability or separatedness assumption is made.

Source: Stacks Project, Limits, Tag 0GWV, final paragraph of the proof of
`lemma-essentially-finite-type-criterion-universally-closed`; Morphisms, Tag 0BX8.
(blueprint: lem-sfb-normal-curve-punctured-generic-model)

Proof plan:
1. Write `T = Spec A`. By `lem-sc-integral-function-field-affine-fraction`, its generic
   field is `Frac A`. Form the integral closure `B` of `A` in `L` and `N = Spec B`, using
   `def-fin-normalization-extension`. The affine description in
   `lem-weil-pbc-relative-normalization` identifies this with relative normalization.
   Its stalks are integrally closed by `lem-weil-pbc-normalization-normal-stalks`.
   The subring `B` of `L` is a domain, and `B` is finite over `A` by
   `lem-fin-normalization-extension-finite` and `def-weil-finite-integral-morphism`.
2. Algebra generators of `A` and module generators of `B` generate `B` over `k`.
   By `lem-weil-pbc-finite-type-domain-dimension-local-ring`, `dim A = 1`; by
   `lem-weil-pbc-integral-injective-dimension-equal`, `dim B = 1`. The scheme `N` is
   Noetherian by `lem-wf-affine-noetherian-components`.
3. Lying over (`lem-weil-pbc-integral-injective-lying-over`) gives a prime over `y`;
   it is maximal by `lem-weil-pbc-integral-prime-over-maximal-maximal`. This is `c`.
   Its local dimension is one by `lem-weil-pbc-finite-type-domain-dimension-local-ring`.
   By `lem-sbc-normalization-generic-field` the generic field is the prescribed `L`,
   with its prescribed map to `T`.
4. The morphism `f` is locally of finite type: on affine pairs, generators over `k`
   still generate over the target's coordinate ring (`lem-weil-pbc-lft-affine-pairs`).
5. Apply `lem-sfb-local-ring-map-spread` on the locally Noetherian scheme `N`
   (`pqf-def-locnoeth`) to the generic map `u`, transported through the generic-field
   identification. Obtain a representative `b : V → W` over `Y` agreeing exactly with `u`.
6. Remove `c` from `V`. Its complement has finitely many irreducible components by
   `lem-sc-noetherian-closed-subset-finite-components`, with generic points by
   `lem-sc-scheme-sober`. In the one-dimensional domain `B`, every nonzero prime is
   maximal, so these components are closed points. For each unwanted point choose an
   element in its maximal ideal but outside the maximal ideal of `c`. Their product `s`
   avoids `c` and vanishes at every unwanted point (the empty product is one).
7. Set `C = D(s)` and restrict `p` and `b`; then `C` contains `c` and its puncture lies
   in `V`. Localization is finite type over `k`. Open immersions preserve the local rings
   (`def-weil-open-immersion`), including the generic field and the local ring at `c`.
   All required equations restrict from those on `N` and `V`. -/
theorem exists_normal_curve_punctured_generic_model
    {k : Type u} [Field k] (T : Scheme.{u}) [IsAffine T] [IsIntegral T]
    (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (η : T) (hη : IsGenericPoint η Set.univ)
    (y : T) (hy : IsClosed ({y} : Set T))
    (hdy : ringKrullDim (T.presheaf.stalk y) = 1)
    (L : Type u) [Field L] [Algebra (T.residueField η) L]
    [FiniteDimensional (T.residueField η) L]
    (Y W : Scheme.{u}) (s : Y ⟶ Spec (CommRingCat.of k))
    (w : W ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [LocallyOfFiniteType w]
    (i : T ⟶ Y) (f : W ⟶ Y) (hi : i ≫ s = t) (hf : f ≫ s = w)
    (uL : Spec (CommRingCat.of L) ⟶ W)
    (huL : uL ≫ w = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField η) L)) ≫
      T.fromSpecResidueField η ≫ t)
    (hfu : uL ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField η) L)) ≫
      T.fromSpecResidueField η ≫ i) :
    ∃ (C : Scheme.{u}) (q : C ⟶ Spec (CommRingCat.of k)) (p : C ⟶ T) (c : C),
      IsIntegral C ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧ p ≫ t = q ∧
      IsClosed ({c} : Set C) ∧
      (∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x)) ∧
      p c = y ∧ ringKrullDim (C.presheaf.stalk c) = 1 ∧
      ∃ (U : C.Opens) (a : U.toScheme ⟶ W),
        (U : Set C) = ({c} : Set C)ᶜ ∧ a ≫ w = U.ι ≫ q ∧ a ≫ f = U.ι ≫ p ≫ i ∧
        ∃ ηC : C, IsGenericPoint ηC Set.univ ∧
          ∃ (e : C.residueField ηC ≅ CommRingCat.of L)
            (g : Spec (CommRingCat.of L) ⟶ U.toScheme),
            g ≫ U.ι = Spec.map e.hom ≫ C.fromSpecResidueField ηC ∧
            (Spec.map e.hom ≫ C.fromSpecResidueField ηC) ≫ p =
              Spec.map (CommRingCat.ofHom (algebraMap (T.residueField η) L)) ≫
                T.fromSpecResidueField η ∧
            g ≫ a = uL := by
  sorry

end AlgebraicGeometry
