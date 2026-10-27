/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Universal closedness tested by normal finite-type curves

Source: Stacks Project, Limits, Tag 0GWV, equivalence (1)--(3), over a field;
Algebra, Tag 0335, fields are Nagata
(blueprint: lem-sfb-normal-curve-universal-closedness-test).

Generic agreement is expressed after pullback of the punctured open along the
canonical map from the fraction field of the local ring. This uses only canonical
fibre products, without choosing a factorization through the punctured open.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact morphism between schemes locally of finite type over a field is
universally closed exactly when its affine-space products are closed, and exactly
when the stated normal finite-type local tests admit a lift.
Source: Stacks Project, Limits, Tag 0GWV, equivalence (1)--(3), specialized to Spec k
(blueprint: lem-sfb-normal-curve-universal-closedness-test).

Proof:
1. Universal closedness implies closedness of every affine-space product by the
fibre-product universal property and the definition of universal closedness.
2. Conversely, work over an affine open of Y. For a closed subset of an arbitrary
base change whose image is not closed, use its reduced induced closed subscheme
(lem-weil-pbc-reduced-induced-closed-subscheme) and the missing-fibre approximation
(lem-sfb-missing-fibre-finite-presentation-approximation). The finite-presentation
model embeds in an affine space; closed immersions survive base change. The
assumed closedness forces its image to contain the omitted specialization, a
contradiction. Quasi-compactness survives base change (lem-pc-quasi-compact-base-change).
3. For a normal test C,c, the local ring is Noetherian: choose an affine neighborhood,
use finite type over k (lem-weil-pbc-lft-affine-pairs), Noetherianity
(lem-wf-affine-noetherian-components), and localization
(lem-weil-pbc-localization-noetherian). Its normality and dimension one make it a DVR
(lem-sc-normal-dim1-dvr, def-sc-discrete-valuation-ring). Valuative existence
(lem-sfb-universally-closed-valuative-existence) gives the requested local lift.
The canonical local-spectrum morphism is the one of
lem-weil-pbc-spec-local-ring-canonical-morphism.
4. The local extension property is inherited by affine-space products by pairing
the lift with the given affine-space component, and by restriction to target opens
by factoring through the inverse-image open (def-pc-fibre-product).
5. Products and target-open restrictions remain quasi-compact and locally of finite
type by lem-sfb-finite-type-composition-base-change and
lem-pc-quasi-compact-base-change. Closedness can be checked on affine target opens.
6. For a closed subset with nonclosed image, the boundary-point lemma
(lem-sfb-finite-type-image-immediate-boundary-point) gives y outside the image, a
point x in the closed subset, and its finite residue extension. The normal punctured
model (lem-sfb-normal-curve-punctured-generic-model) supplies C,c,a,b with b(c)=y
and generic image x, including exactly the required generic compatibility.
7. Apply the local extension property. The inverse image of the closed subset under
the lift contains the generic point of Spec R, hence all of Spec R. Its closed point
therefore maps into that subset, but also maps to y by the canonical local-spectrum
map, a contradiction. Thus all affine-space products are closed. No uniqueness,
separatedness, or reducedness of X or Y is used. -/
theorem normal_curve_universal_closedness_test
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (g : X ⟶ Y) [QuasiCompact g] (hg : g ≫ q = p) :
    List.TFAE [
      UniversallyClosed g,
      ∀ n : ℕ, IsClosedMap
        (pullback.map
          (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k))) p
          (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k))) q
          (𝟙 _) g (𝟙 _) (by simp) (by simpa using hg.symm)),
      ∀ (C : Scheme.{u}) (s : C ⟶ Spec (CommRingCat.of k))
        [IsIntegral C] [LocallyOfFiniteType s] [QuasiCompact s],
        (∀ z : C, IsDomain (C.presheaf.stalk z) ∧
          IsIntegrallyClosed (C.presheaf.stalk z)) →
        ∀ (c : C), IsClosed ({c} : Set C) → ringKrullDim (C.presheaf.stalk c) = 1 →
        ∀ (U : C.Opens), (U : Set C) = {c}ᶜ →
        ∀ (a : U.toScheme ⟶ X) (b : C ⟶ Y),
          a ≫ p = U.ι ≫ s → b ≫ q = s → a ≫ g = U.ι ≫ b →
          ∃ h : Spec (C.presheaf.stalk c) ⟶ X,
            h ≫ p = C.fromSpecStalk c ≫ s ∧
            h ≫ g = C.fromSpecStalk c ≫ b ∧
            pullback.snd U.ι
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
                    C.fromSpecStalk c) ≫
              Spec.map (CommRingCat.ofHom
                (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫ h =
            pullback.fst U.ι
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
                    C.fromSpecStalk c) ≫ a] := by
  sorry

end AlgebraicGeometry
