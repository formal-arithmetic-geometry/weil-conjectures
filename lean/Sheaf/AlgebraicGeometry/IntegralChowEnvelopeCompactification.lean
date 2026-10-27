/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Integral Chow envelope and reduced projective compactification

Source: Stacks Project, Tag 0208, proof of (4) implies (1), using Chow's lemma
(Tag 0200) and the reduced induced closed structure (Tag 01J3).
(blueprint: lem-sfb-integral-chow-envelope-compactification).

The generic point is `genericPoint R`; its generic stalk `R.functionField` is canonically
its residue field because `R` is integral. The field identifications are constrained by
commuting canonical generic-point maps, so they are precisely those induced by the dense
open isomorphism and the open immersion into the compactification.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An integral Chow envelope with its reduced projective closure over an affine Noetherian
base. Source: Stacks Project, Tag 0208, proof of (4) implies (1); Tag 0200; Tag 01J3.
(blueprint: lem-sfb-integral-chow-envelope-compactification).

Proof:
1. Apply `lem-weil-pbc-chow-noetherian` to obtain a proper surjective Chow map, an
   immersion into projective space, and an isomorphism over a dense open `U`.
   By `lem-weil-pbc-finite-type-over-noetherian` its source and `R` are Noetherian.
   Since `R` is integral, `U` is nonempty (`def-pc-integral-scheme`).
2. Give the closure of the inverse image of `U` its reduced induced closed structure,
   using `lem-weil-pbc-reduced-induced-closed-subscheme`. Its underlying space is
   nonempty irreducible, so the resulting `Y` is integral (`def-pc-integral-scheme`).
3. Restriction of that reduced closure to the inverse image of `U` is the original
   integral open: uniqueness in `lem-weil-pbc-reduced-induced-closed-subscheme`
   identifies their reduced closed structures. Thus the new map is an isomorphism over `U`.
4. Its composite to `R` is proper by `lem-weil-pbc-closed-immersion-proper`, and its
   closed image contains dense `U`, hence is all of `R` by `lem-weil-pbc-proper-closed-image`.
   Finite type over a Noetherian scheme gives Noetherianity of `Y`.
5. Compose the closed inclusion into the Chow source with its immersion. Composing the
   two closed parts of a closed-then-open factorization gives the required immersion `j`
   (`def-weil-closed-immersion`), over `S` by the original Chow equality.
6. Apply `lem-weil-pbc-reduced-induced-closed-subscheme` to the closure of `j(Y)`.
   The resulting `Z` is integral. Projective space uses `n+1` homogeneous coordinates
   (`def-nagata-projective-space-base-change`); it is proper by
   `lemma-nagata-projective-space-base-change-proper`. Its closed subscheme `Z` is
   proper and Noetherian by the closed-immersion and finite-type lemmas above.
7. In the open part of a closed-then-open factorization of `j`, its image is closed.
   The reduced closure restricts there to exactly that reduced closed subscheme.
   Uniqueness in `lem-weil-pbc-reduced-induced-closed-subscheme` gives `e`, an open
   immersion with `e ≫ c = j`. Its image is dense and it is over `S`.
8. The generic point of `R` lies in `U` (`def-sc-generic-point`). Transport it over
   the open isomorphism and then along `e`; these are the generic points of `Y` and `Z`.
   Open immersions identify their local rings (`def-weil-open-immersion`), which are
   their function fields by the integral-scheme clause of `def-sc-function-field`.
9. On affine neighbourhoods the canonical maps from the spectra of these fields are
   induced by the same generic-germ homomorphisms. Functoriality of Spec
   (`def-weil-affine-spectrum`) gives both displayed generic-map compatibilities.
-/
theorem exists_integral_chow_envelope_compactification
    (S R : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S] [IsIntegral R]
    (f : R ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : ℕ) (Y Z : Scheme.{u}) (_ : IsIntegral Y) (_ : IsIntegral Z)
      (π : Y ⟶ R) (j : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) S)
      (c : Z ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) S) (e : Y ⟶ Z),
      IsNoetherian Y ∧ IsNoetherian Z ∧ IsProper π ∧ Surjective π ∧
      IsImmersion j ∧ IsClosedImmersion c ∧ IsOpenImmersion e ∧
      Dense (Set.range e) ∧ e ≫ c = j ∧
      j ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) S ↘ S) = π ≫ f ∧
      IsProper (c ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) S ↘ S)) ∧
      c.ker = Scheme.IdealSheafData.vanishingIdeal
        ⟨closure (Set.range j), isClosed_closure⟩ ∧
      ∃ U : R.Opens, (U : Set R).Nonempty ∧ Dense (U : Set R) ∧ IsIso (π ∣_ U) ∧
        ∃ (a : Y.functionField ≅ R.functionField) (b : Z.functionField ≅ R.functionField),
          Spec.map a.hom ≫ Y.fromSpecFunctionField ≫ π = R.fromSpecFunctionField ∧
          Spec.map a.hom ≫ Y.fromSpecFunctionField ≫ e =
            Spec.map b.hom ≫ Z.fromSpecFunctionField := by
  sorry

end AlgebraicGeometry
