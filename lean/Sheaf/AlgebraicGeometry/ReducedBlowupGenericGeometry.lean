/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Density
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Generic geometry of a reduced blowup

Source: ILO, Expose VIII, 2.1.1--2.1.3 and 2.2.1--2.2.3; Stacks Project,
Tags 0808, 0BFM, 02OS and 02NS (blueprint: lem-trf-reduced-blowup-generic-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An ordinary blowup of a reduced finite-type rational scheme, with centre avoiding every
component generically, is reduced, proper, surjective and componentwise birational.
Coherence is imposed on the associated ideal module `J.toModules`. The last clause
expresses birationality by dense opens of the actual reduced induced component schemes,
with an isomorphism compatible with the blowup map.

Source: ILO, Expose VIII, 2.1.1--2.1.3 and 2.2.1--2.2.3; Stacks Tags 0808, 0BFM,
02OS and 02NS (blueprint: lem-trf-reduced-blowup-generic-geometry).

Proof:
1. Coherence gives finite generation on affine opens (pqf-def-coherent).
   Apply lemma-nagata-blowup-proper. Compose with the finite-type rational structure map
   (lem-sfb-finite-type-composition-base-change). The field Q is Noetherian, so
   pqf-lem-locnoeth-lft makes S and its blowup locally Noetherian. Finite affine covers
   and lem-sc-affine-noetherian-underlying-space make their spaces Noetherian; use
   lem-sc-noetherian-finite-irreducible-components. Every subset is compact by
   lem-sfb-noetherian-space-compact-subsets, so the complement's open immersion is
   quasi-compact and quasi-separated.
2. Components cover S (lem-sc-irreducible-components-cover), so the complement U is dense.
   On U the ideal is the unit ideal; thm-nagata-global-blowup-complement gives the
   isomorphism above U. By lemma-nagata-reduced-dense-image-schematic and
   def-nagata-scheme-theoretic-image, the kernel of O_S -> j_* O_U is zero. Thus U is
   scheme-theoretically dense (def-nagata-scheme-theoretically-dense-open).
3. Apply lemma-nagata-admissible-blowup-preserves-density. The inverse image V of U is
   scheme-theoretically dense in the blowup and therefore topologically dense: a nonempty
   open disjoint from V would have its structure sheaf inject into zero, contradicting
   the proper maximal ideal of any stalk there.
4. U, and hence V, is reduced (def-pc-reduced-scheme). A nilpotent section on the blowup
   vanishes on V; schematic density forces it to vanish. This proves reducedness.
5. In a space with finitely many components, a dense open meets every component densely:
   remove the other components, then use irreducibility. Intersections identify the
   components of the open with those of the whole space. Apply this to U and V and their
   isomorphism. By lem-sc-scheme-sober each component has a unique generic point, which
   lies in every nonempty component open. Thus the blowup map bijects generic points.
6. The isomorphism over U identifies local rings at these points, hence their residue
   fields (def-weil-residue-field). Use uniqueness in
   lem-weil-pbc-reduced-induced-closed-subscheme inside the isomorphic opens to identify
   the reduced component opens. This gives the compatible dense-open isomorphisms.
7. Properness makes the image closed (def-weil-proper-morphism). It contains the dense
   U, hence is all of S (def-weil-surjective-morphism). For empty S the component and
   generic-point assertions are vacuous. For the unit ideal U = S and the blowup is S. -/
theorem reducedBlowup_generic_geometry (S : Scheme.{u})
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType q] [QuasiCompact q] (J : S.IdealSheafData)
    (hJ : RingedSpace.IsCoherent S.toRingedSpace J.toModules)
    (hcentre : ∀ C ∈ irreducibleComponents S,
      Dense {x : C | x.1 ∈ J.support.compl}) :
    IsReduced J.blowup ∧
    IsLocallyNoetherian J.blowup ∧
    (irreducibleComponents J.blowup).Finite ∧
    LocallyOfFiniteType (J.blowupMap ≫ q) ∧ QuasiCompact (J.blowupMap ≫ q) ∧
    IsProper J.blowupMap ∧ Surjective J.blowupMap ∧
    IsIso (J.blowupMap ∣_ J.support.compl) ∧
    (∀ C ∈ irreducibleComponents J.blowup,
      Dense {x : C | J.blowupMap x.1 ∈ J.support.compl}) ∧
    Set.BijOn J.blowupMap (genericPoints J.blowup) (genericPoints S) ∧
    (∀ x ∈ genericPoints J.blowup, IsIso (J.blowupMap.residueFieldMap x)) ∧
    (∀ (C : TopologicalSpace.Closeds J.blowup) (D : TopologicalSpace.Closeds S),
      (C : Set J.blowup) ∈ irreducibleComponents J.blowup →
      (D : Set S) ∈ irreducibleComponents S →
      (∃ x : J.blowup, IsGenericPoint x (C : Set J.blowup) ∧
        IsGenericPoint (J.blowupMap x) (D : Set S)) →
      ∃ (V : (vanishingIdeal C).subscheme.Opens) (U : (vanishingIdeal D).subscheme.Opens),
        Dense (V : Set (vanishingIdeal C).subscheme) ∧
        Dense (U : Set (vanishingIdeal D).subscheme) ∧
        ∃ e : V.toScheme ≅ U.toScheme,
          e.hom ≫ U.ι ≫ (vanishingIdeal D).subschemeι =
            V.ι ≫ (vanishingIdeal C).subschemeι ≫ J.blowupMap) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
