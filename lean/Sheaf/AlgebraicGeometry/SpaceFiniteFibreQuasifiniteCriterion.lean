/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceFieldDiscretenessCriterion

/-!
# Finite field fibres and quasi-finiteness along a fibre

Source: Stacks Project, Decent Spaces, Tag 0ACK, conditions (4), (5), (8);
Tag 0ACA and Morphisms of Spaces, Tag 03HF
(blueprint: lem-sfb-space-finite-fibre-quasifinite-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type algebraic space over a scheme has finitely many points
in its fibre over any extension of the residue field exactly when it is quasi-finite
at every point over the given base point. The right side uses all representable
etale scheme charts and the Stacks scheme predicate, including local finite type.
There is no nonemptiness, algebraicity or algebraic-closedness restriction on the field.

Source: Stacks Project, Decent Spaces, Tag 0ACK, (4), (5), (8), with Tag 0ACA,
Tag 03M5 (separated implies decent), and Morphisms of Spaces, Tag 03HF
(blueprint: lem-sfb-space-finite-fibre-quasifinite-criterion).

Proof:
1. Form E_K = E times_S Spec K. By lem-sfb-stack-finite-type-calculus and
   lem-sfb-space-separated-fp-composition the base-changed map is finite type and
   separated. Choose an affine open V containing s. Quasi-compactness gives a
   quasi-compact scheme atlas U0 of E_V. Pulling it back to Spec K gives an etale
   surjective scheme atlas U of E_K by lem-trf-space-fibre-products-etale-covers.
   A finite affine open cover of U0 gives a finite affine cover of U, so U is
   quasi-compact, and hence the point space of E_K is compact.
2. The point lifting clause of lem-a1-space-point-open-calculus says that E_K maps
   onto every point of E over s. By lem-sfb-space-quasifinite-locus-open, its
   quasi-finite locus is the inverse image of that of E. Thus E_K is locally
   quasi-finite exactly when h is quasi-finite at all points above s.
3. By lem-sfb-space-field-discreteness-criterion, finite |E_K| implies discrete
   |E_K|, because E_K is separated. Discreteness is equivalent to local
   quasi-finiteness of E_K over K. This proves the forward implication and gives
   discreteness in the reverse implication.
4. The atlas in step 1 has a continuous surjective point map by
   lem-a1-space-point-open-calculus. Pull back any open cover and take a finite
   subcover to prove compactness of |E_K|. In the discrete case the singleton
   cover then has a finite subcover, proving finiteness. The right side does not
   involve K, so the equivalence applies to every residue-field extension,
   including the residue field itself and its algebraic closures. Empty fibres
   give a finite empty point set and a vacuous chart condition. -/
theorem finite_field_fibre_iff_quasiFinite_at_fibre {S : Scheme.{u}}
    (E : AlgebraicSpace S) (h : E.obj.obj ⟶ yoneda.obj (Over.mk (𝟙 S)))
    (hsep : MapToSchemeIsSeparated E (Over.mk (𝟙 S)) h)
    (hqc : ∀ V : S.Opens, IsCompact (V : Set S) →
      IsCompact (mapPoint h ⁻¹'
        (schemePointMap (𝟙 (yoneda.obj (Over.mk (𝟙 S)))) '' (V : Set S))))
    (hft : MapToSchemeIsLocally (@LocallyOfFiniteType) E (Over.mk (𝟙 S)) h)
    (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K] :
    Finite (Point (Limits.pullback h (yoneda.map (Over.mkIdTerminal.from
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
        S.fromSpecResidueField s)))))) ↔
      ∀ (U : Over S) (a : yoneda.obj U ⟶ E.obj.obj), IsEtale a →
        ∀ x : U.left, (yoneda.preimage (a ≫ h)).left x = s →
          (yoneda.preimage (a ≫ h)).left.IsQuasiFiniteAtPoint x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
