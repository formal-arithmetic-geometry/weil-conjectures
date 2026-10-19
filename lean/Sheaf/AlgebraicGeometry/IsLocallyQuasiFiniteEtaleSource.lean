/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.RingTheory.QuasiFiniteComposition
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource

/-!
# Local quasi-finiteness is etale local on the source

Source: Stacks Project, Descent, Tag 03X4, including etale precomposition in its proof
(blueprint: lem-a1-scheme-lqf-etale-source-locality).

The predicate `Scheme.Hom.IsLocallyQuasiFinite` includes the local finite-type condition
of Stacks Tag 01TD. No quasi-compactness or separation condition is imposed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Etale precomposition preserves local quasi-finiteness, and a surjective etale source map
also detects it. Source: Stacks Project, Descent, Tag 03X4
(blueprint: lem-a1-scheme-lqf-etale-source-locality).

Proof:
1. Restrictions of the etale map `p` to compatible opens are etale. Flatness is unchanged
   on local rings. To check finite presentation at a point in source and target opens,
   start with affine charts Spec A' -> Spec R for `p`. Shrink the target to D(r) inside
   the prescribed target open, then the source to D(a) inside the prescribed source open
   and the inverse image of D(r). The algebra A'_a is finitely presented over R, and r
   is a unit in it; base change to R_r therefore makes A'_a finitely presented over R_r.
   The diagonal is the restriction of the open diagonal of `p`, hence is open. Apply
   def-sbc-locally-finite-presentation, def-weil-flat-morphism,
   def-weil-open-immersion, def-weil-unramified-morphism and def-weil-etale-morphism.
   Restriction over a target open also preserves surjectivity when `p` is surjective.
2. Suppose `g` is locally quasi-finite. Around any u choose affine opens Z in T, W in V,
   and A in U with u in A, p(A) contained in W and g(W) contained in Z.
   The map on rings for W -> Z is finite type and quasi-finite at every prime by
   lem-a1-scheme-lqf-affine-criterion. The same is true for A -> W by step 1 and
   lem-weil-pbc-etale-ring-map-quasi-finite. Apply lem-trf-quasi-finite-composition.
   Functoriality identifies the composite ring map with that for A -> Z, giving the
   affine witnesses in pqf-def-quasifinite at every u.
3. Conversely, suppose `p` is surjective and `p ≫ g` is locally quasi-finite. Apply
   lem-weil-pbc-lqf-locally-finite-type, then lem-a1-lft-flat-lfp-source-descent to the
   flat, locally finitely presented, surjective map `p` to see `g` is locally finite type.
4. For affine Z in T and W in V mapping into Z, restrict `p` over W. Apply
   lem-weil-pbc-etale-covering-affine-refinement to get finitely many affine opens A_j
   in its source whose images cover W. By lem-weil-pbc-lqf-restriction-to-opens,
   every A_j -> Z is locally quasi-finite.
5. Each A_j -> Z is affine by lem-weil-pbc-morphism-affine-schemes-affine, hence
   quasi-compact by lem-weil-pbc-affine-morphism-permanence. Apply
   pqf-lem-qf-locqf-qc and pqf-lem-qf-finitefibres: each A_j -> Z has finite fibres.
6. Every fibre of W -> Z is the union of the images of these finitely many finite
   fibres. Surjectivity of the covering gives equality, so the fibre is finite.
   If the affine refinement is empty, W is empty and this remains valid.
7. By lem-weil-pbc-lft-affine-pairs and step 3, W -> Z is locally finite type. It is
   affine, hence quasi-compact and of finite type (def-weil-finite-type-morphism).
   Its finite fibres give quasi-finiteness by pqf-lem-qf-finitefibres, and then local
   quasi-finiteness by pqf-lem-qf-locqf-qc. Apply the affine-cover clause of
   lem-a1-scheme-lqf-affine-criterion to conclude that `g` is locally quasi-finite.
   Quasi-compactness has only been used on the affine charts. -/
theorem isLocallyQuasiFinite_etale_source {U V T : Scheme.{u}} (p : U ⟶ V) (g : V ⟶ T)
    [Etale p] :
    (IsLocallyQuasiFinite g → IsLocallyQuasiFinite (p ≫ g)) ∧
      (Function.Surjective p → IsLocallyQuasiFinite (p ≫ g) → IsLocallyQuasiFinite g) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
