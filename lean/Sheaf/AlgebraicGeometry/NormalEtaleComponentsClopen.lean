/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Connected.Clopen
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Sheaf.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import Sheaf.RingTheory.StrictHenselizationLocalMaximalIdeal
import Sheaf.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Clopen components of an etale scheme over a locally Noetherian normal base

Source: Bhatt--Scholze, The pro-etale topology for schemes, proof of Lemma 7.4.10,
p. 71, first paragraph; Stacks Project, Tags 0BQ3 and 0357
(blueprint: lem-a1-normal-etale-components-clopen).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An etale scheme over a locally Noetherian scheme with normal local domains is locally
topologically Noetherian and geometrically unibranch. Its irreducible components are clopen,
and its nonempty connected components are irreducible and clopen. The source can be empty.
Strict henselizations are quantified in a common universe at least as large as the stalks.
Source: Bhatt--Scholze, proof of Lemma 7.4.10, p. 71, first paragraph; Stacks Project,
Tags 0BQ3, 0357 and 06DI (blueprint: lem-a1-normal-etale-components-clopen).

Proof:
1. Etaleness (`def-weil-etale-morphism`) gives locally finite presentation
   (`def-sbc-locally-finite-presentation`), hence pointwise finite type. The pointwise
   criterion `lem-weil-pbc-lft-pointwise-criterion` gives locally finite type
   (`def-weil-finite-type-morphism`), so `pqf-lem-locnoeth-lft` makes the source locally
   Noetherian. Choose affine Noetherian neighbourhoods (`pqf-def-locnoeth`); their spaces
   are Noetherian by `lem-sc-affine-noetherian-underlying-space`.
2. The localization at every prime of an affine chart of the base is its corresponding
   stalk (`lem-weil-pbc-affine-open-stalk-localization`), hence a normal domain. Thus the
   chart ring is normal (`def-weil-pbc-normal-ring`).
3. Cover the source by affine etale charts over such base charts. Their rings are normal
   by `lem-weil-pbc-etale-over-normal-ring-normal`; their stalks are normal domains by
   `lem-weil-pbc-affine-open-stalk-localization` and `def-weil-pbc-normal-ring`.
4. A source stalk is also a normal ring by `lem-weil-pbc-localization-normal-domain`.
   Any strict henselization (`def-sc-ring-strict-henselization`) is a pointed-etale colimit
   with essentially small filtered index (`lem-sc-pointed-etale-small-filtered`) and local
   vertex (`lem-sc-ring-strict-henselization-local-maximal-ideal`). By clause (a) of
   `lem-weil-pbc-etale-colimit-normal-local-domain` it is a normal domain. Its spectrum is
   integral by `lem-weil-pbc-spec-domain-stalks-function-field`, hence irreducible by
   `def-pc-integral-scheme`. This is geometric unibranchness at every point.
5. Given an irreducible component and one of its points, choose an affine Noetherian
   neighbourhood. Its stalks are normal by step 3. Clause (2) of `rem-pc-regular-normal`
   makes its components disjoint and clopen. The intersection of the global component
   with this neighbourhood is a component by `lem-sc-components-open-injection`, hence
   open. These intersections cover the global component, so it is open; it is closed by
   `def-weil-irreducible-components`.
6. Two global components meeting at a point restrict to the same component in an affine
   neighbourhood, by the disjointness in `rem-pc-regular-normal`. The injectivity in
   `lem-sc-components-open-injection` identifies them. Thus distinct components are disjoint.
7. Choose a point in a nonempty connected component and an irreducible component through
   it (`lem-sc-irreducible-components-cover`). The latter is clopen by step 5, so
   connectedness forces the former into it (`def-weil-connected-scheme`). Irreducibility
   implies connectedness (`def-weil-irreducible-components`), and maximality gives equality.
   Therefore the connected component is irreducible and clopen. If the source is empty,
   there are no points or nonempty components, and every assertion is vacuous. -/
theorem normal_etale_components_clopen
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (q : Z ⟶ X) [Etale q] :
    (∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ TopologicalSpace.NoetherianSpace U) ∧
    (∀ (z : Z) (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Z.presheaf.stalk z)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Z.presheaf.stalk z)) K]
      [Algebra (Z.presheaf.stalk z) K]
      [IsScalarTower (Z.presheaf.stalk z)
        (IsLocalRing.ResidueField (Z.presheaf.stalk z)) K]
      [CommRing H] [Algebra (Z.presheaf.stalk z) H],
      Algebra.StrictHenselizationPresentationIn.{u, v} (Z.presheaf.stalk z) K H →
        IrreducibleSpace (PrimeSpectrum H)) ∧
    (∀ C : Set Z, C ∈ irreducibleComponents Z → IsClopen C) ∧
    (∀ C : Set Z, Maximal IsConnected C → IsIrreducible C ∧ IsClopen C) := by
  sorry

end AlgebraicGeometry
