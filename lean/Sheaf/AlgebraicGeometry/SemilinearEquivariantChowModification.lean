/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Ring.Equiv
import Sheaf.AlgebraicGeometry.NoetherianChowModification
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.TraceFormula.ReducedSchemeImage
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Semilinear equivariant projective Chow modification

Source: Stacks Project, Tag 0200 (Chow's lemma), Tag 01WD (Segre embedding),
and the finite-translate averaging construction referred to in de Jong (1997),
section 2.10, printed p. 605.
(blueprint: lem-sfb-semilinear-equivariant-chow-modification)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A proper integral scheme with a compatible finite semilinear group action has an
integral equivariant modification projective both over the field and over the scheme.
The field action `rho` is a left action. Its inverse under `Spec.map` gives the associated
left scheme action on the field spectrum. Neither action is required to be faithful.
The final clause is the induced function-field identification: `eta` is the generic
point of `T`, its image is the generic point of `X`, and the actual stalk map of `q` is
an isomorphism. These stalks are precisely the function fields of the integral schemes.

Source: Stacks Project, Tag 0200, lemma-chow-Noetherian; Tag 01WD,
lemma-segre-embedding; de Jong (1997), section 2.10, printed p. 605.
(blueprint: lem-sfb-semilinear-equivariant-chow-modification)

Proof:
1. The field spectrum is affine Noetherian. Since X is integral it is reduced.
   Apply lem-fin-noetherian-chow-modification to obtain a proper modification
   pi : Y to X, an isomorphism over a dense open U0, with Y projective over the field.
   X is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
2. For each g in H take a copy of Y with map a_g pi to X and scalar map b_g f pi.
   This semilinear twist is a base change along the base automorphism b_g inverse.
   Its projective embedding follows from lemma-nagata-projective-space-base-change-pullback
   and lem-weil-pbc-closed-immersion-base-change. Intersect the finitely many translates
   a_g(U0) to get a dense H-invariant open U; no faithfulness is used.
3. Form the finite nonempty fibre product P of these copies over X. The separated
   diagonal of X over the field gives a closed immersion into their product over the
   field by lem-weil-pbc-fibre-product-change-of-base-closed-immersion. Use
   lem-weil-pbc-closed-immersion-products and iterate lem-chow-segre to embed P into
   finite-dimensional projective space over the field.
4. Define A_h on P by the g-projection rho_g A_h = rho_(h inverse g). The components
   have common image a_h r in X, so the fibre-product universal property gives A_h.
   The same uniqueness gives A_h A_l = A_(hl), A_1 = 1, and semilinearity over b_h.
5. Over U every twisted modification is an isomorphism, hence P times_X U is U.
   This embeds U openly in P. Equivariance and uniqueness of the inverse show this
   open subscheme is invariant under every A_h.
6. Take T to be its schematic image in P. By lem-trf-reduced-scheme-image this is
   the reduced closure of U, whose support is nonempty and irreducible, hence T is
   integral. P is Noetherian by projectivity and finite type over the field. Thus
   the open immersion of U is quasi-compact and quasi-separated. Apply
   lemma-nagata-scheme-image-restrict-open to get T times_X U = U as schemes.
7. The ideal of T consists locally of functions vanishing on U by
   lem-weil-pbc-scheme-image-qc-kernel. Every A_h preserves U, and A_(h inverse)
   gives the reverse ideal inclusion. The actions descend to the quotient closed
   scheme T and satisfy their group laws. The restricted map q is equivariant
   and its composite to the field spectrum has the required semilinearity.
8. Compose T's closed immersion into P with P's projective embedding. The graph
   of q is closed since X is separated over the field, by
   lem-weil-pbc-fibre-product-change-of-base-closed-immersion. Base change the
   absolute embedding along X to obtain an embedding of T into projective space
   over X, using lemma-nagata-projective-space-base-change-pullback and
   lem-weil-pbc-closed-immersion-base-change. Composition of closed immersions
   proves both H-projectivity claims. By lem-kun-projective-implies-proper, q is
   proper and both structure maps are finite type. Its closed image contains the
   dense U, so q is surjective; it is already an isomorphism over U.
9. Every dense open of an integral scheme contains its generic point. U is dense
   in X and in T by the closure construction. The isomorphism over U therefore
   carries the generic point of T to that of X and makes the stalk map of q an
   isomorphism. By def-sc-function-field these stalks are the function fields;
   lem-sc-integral-function-field-affine-fraction supplies their field property.
-/
theorem exists_semilinear_equivariant_chow_modification
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (H : Type v) [Group H] [Finite H] (rho : H →* (k ≃+* k))
    (a : H →* Aut X)
    (ha : ∀ h : H, (a h).hom ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (q : T ⟶ X) (aT : H →* Aut T),
      LocallyOfFiniteType (q ≫ f) ∧ QuasiCompact (q ≫ f) ∧
      (∀ h : H, (aT h).hom ≫ (q ≫ f) =
        (q ≫ f) ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)) ∧
      (∀ h : H, (aT h).hom ≫ q = q ≫ (a h).hom) ∧
      IsProper q ∧ Surjective q ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (q ∣_ U)) ∧
      IsHProjective (q ≫ f) ∧ IsHProjective q ∧
      ∃ eta : T, IsGenericPoint eta Set.univ ∧
        q eta = genericPoint X ∧ IsIso (q.stalkMap eta) := by
  sorry

end AlgebraicGeometry
