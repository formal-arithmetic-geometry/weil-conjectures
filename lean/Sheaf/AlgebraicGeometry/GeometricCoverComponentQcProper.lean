/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Sheaf.RingTheory.EtaleNormalRing
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Compactification.ValuativeCriterion
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen

/-!
# Quasi-compactness and properness of a geometric-cover component

Source: Bhatt--Scholze, The pro-étale topology for schemes, proof of Lemma 7.4.10, p. 71
(blueprint: lem-a1-geometric-cover-component-qc-proper).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An open connected component of an étale geometric covering of a connected quasi-compact
locally Noetherian scheme with integrally closed local domains is quasi-compact and proper
with finite fibres over the base. The component is represented by an open `C` whose underlying
set is a connected component. `ValuativeCriterion q` is unique lifting for every valuation ring
and its fraction field. Source: Bhatt--Scholze, proof of Lemma 7.4.10, p. 71
(blueprint: lem-a1-geometric-cover-component-qc-proper).

Proof:
1. By `lem-a1-normal-etale-components-clopen`, the component `C` is also closed. Its open
   inclusion is étale, and `lem-weil-pbc-etale-composition-cancellation` makes its composite
   with `q` étale. Every valuation lift into `Z` stays in `C`: its inverse image is clopen in
   the irreducible valuation spectrum and contains the generic point. Uniqueness is inherited.
2. Apply the component lemma also to the identity of `X`. Thus `X` and `C` are irreducible.
   The reduced/integral definitions `def-pc-reduced-scheme` and `def-pc-integral-scheme`,
   `lem-weil-pbc-normal-domain-of-local-normal`, and
   `lem-weil-pbc-etale-over-normal-ring-normal` make both schemes integral with normal affine
   coordinate domains.
3. Étaleness and `def-weil-unramified-morphism` give local finite type.
   `pqf-lem-locnoeth-lft`, `lem-weil-pbc-locally-noetherian-quasi-separated`, and
   `lem-weil-pbc-qcqs-morphism-permanence` give local Noetherianity and quasi-separatedness.
   Apply `sk-lem-nagata-sketch-dense-valuative` with the identity of `C` to get separatedness,
   before assuming quasi-compactness.
4. By `lem-sc-scheme-sober` and `lem-sc-integral-function-field-affine-fraction`, take the
   generic point of `X` with field `K`. Étale openness
   (`lem-weil-pbc-etale-morphism-open-map`) makes every nonempty open of `C` meet its generic
   fibre. The fibre topology of `lem-weil-pbc-fibre-spec-homeomorphism` and irreducibility of
   `C` then make that fibre nonempty and irreducible.
5. `lem-weil-pbc-etale-fibre-discrete-separable-points` makes the generic fibre a singleton
   `Spec L` with `L/K` finite separable. Its point is the generic point of `C`.
   `lem-sc-integral-function-field-affine-fraction` identifies `L` with the fraction fields of
   its nonempty affine charts.
6. On a nonempty affine `V = Spec A` in `X`, let `B` be the integral closure of `A` in `L`
   (`def-weil-pbc-integral-closure`). The affine rings are Noetherian by
   `pqf-lem-affine-open-locnoeth`, and `B` is finite by
   `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`. Thus `Spec B` is finite
   over `V` (`def-weil-finite-integral-morphism`), of finite type
   (`def-weil-finite-type-morphism`), and Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`.
7. Exhaust the nonempty inverse image of `V` by nonempty quasi-compact opens `U`, directed
   by finite unions. Their maps to `V` are étale, quasi-compact, separated and quasi-finite
   (`pqf-def-quasifinite`, the étale-fibre theorem, and qcqs permanence). Apply
   `pqf-lem-normalization-open` to embed each `U` into its relative normalization over `V`.
8. Embed the sections of `U` into `L` by their generic germs. Normal affine charts show that
   every element of `B` extends to a section, so their integral closure over `A` is `B`.
   `lem-weil-pbc-relative-normalization` identifies every normalization with `Spec B` and
   its canonical factorization with the inclusion on sections. A possibly different open
   immersion from step 7 gives an injective `A`-map `B` into `L`. Each element of `L` is
   `b/a` for `b` in `B`, nonzero `a` in `A`, by clearing denominators in a monic equation.
   The map therefore extends to a `K`-automorphism of `L`, preserving `B`. By
   `lem-weil-pbc-morphism-into-affine-scheme`, the canonical factorization differs from the
   open immersion by an automorphism of `Spec B`, so it too is an open immersion.
9. The same affine-target Hom bijection makes the canonical embeddings compatible with
   inclusions `U ⊆ U'`, since their maps on sections are the same generic rational functions.
10. By `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, choose a minimal closed
    complement of an image in `Spec B`. Directedness forces its open `U₀` to contain every
    `U`; hence the whole inverse image of `V` equals this quasi-compact `U₀`.
11. Empty affine opens have empty inverse image. Thus the restricted morphism is
    quasi-compact, hence of finite type. Its discrete étale fibres make it quasi-finite,
    and `pqf-lem-qf-finitefibres` gives precisely the asserted finite fibres.
12. Apply `sk-lem-nagata-sketch-dense-valuative` again with the identity of `C`, now with
    finite type, quasi-separatedness and unique valuation lifting, to obtain properness. -/
theorem geometricCoverComponentQcProper
    {X Z : Scheme.{u}} [ConnectedSpace X] [CompactSpace X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (q : Z ⟶ X) [Etale q] (hval : ValuativeCriterion q)
    (C : Z.Opens) (hC : ∃ z : Z, (C : Set Z) = connectedComponent z) :
    QuasiCompact (C.ι ≫ q) ∧ IsProper (C.ι ≫ q) ∧
      Scheme.Hom.HasFiniteFibres (C.ι ≫ q) := by
  sorry

end AlgebraicGeometry
