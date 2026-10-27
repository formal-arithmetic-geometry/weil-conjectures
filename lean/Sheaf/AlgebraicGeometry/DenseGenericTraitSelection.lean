/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen
import WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor

/-! # Trait selection meeting a prescribed generic open

Source: Stacks Project, More on Morphisms, Tag 05GU, and Algebra, Tag 00PH
(blueprint: lem-sfb-dense-generic-trait-selection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral finite-type dominant scheme over a DVR with nonempty special fibre admits
an integral trait through every nonempty generic open, with finite fraction-field extension.
The trait ring need not be module-finite over the base DVR.

Source: Stacks Project, More on Morphisms, Tag 05GU
(`more-morphisms-lemma-quasi-finite-quasi-section-meeting-nearby-open-X`), and Algebra,
Tag 00PH (`algebra-lemma-exists-dvr`)
(blueprint: lem-sfb-dense-generic-trait-selection).

Proof:
1. A DVR is Noetherian. For a uniformizer t, its punctured spectrum D(t) is Spec K.
   Thus U is open in Y. Choose an affine X = Spec B meeting the special fibre.
   By lem-weil-pbc-lft-affine-pairs, B is finite type over R. A maximal ideal containing
   tB exists by lem-weil-pbc-proper-ideal-contained-in-maximal; its point x is closed
   in the special fibre of X.
2. Integrality and lem-sc-scheme-sober give the generic point of Y, lying in both X
   and U and specializing to x. Apply lem-sfb-quasi-section-nearby-open to X and U
   intersected with X. Obtain an integral closed Z with generic point z in U, containing
   x, and quasi-finite over the base at x.
3. The closed Z is affine and finite type, hence locally Noetherian by
   pqf-lem-locnoeth-lft. By lem-sc-quasi-finite-points-open, choose an affine neighbourhood
   W = Spec E of x in its quasi-finite locus; it contains z. Use
   lem-weil-pbc-lqf-restriction-to-opens and lem-weil-pbc-lqf-qc-source-bounded-fibres:
   its generic fibre is Spec D for a finite-dimensional K-algebra D. The lemma
   lem-sbc-affine-fibre-sections-tensor identifies D with E[1/t].
4. By lem-sc-integral-function-field-affine-fraction, L = kappa(z) is Frac E.
   Dominance makes R -> E -> L injective, and E[1/t] embeds in L. This finite-dimensional
   domain is a field by lem-weil-pbc-finite-dimensional-domain-is-field. It therefore
   equals L, proving that L/K is finite.
5. The points x and z are distinct, since they lie over different points of Spec R.
   Apply lem-sfb-nongeneric-point-same-field-dvr to Z at x: obtain a DVR R0 in L,
   with fraction field L and a map Spec R0 -> Z sending its closed point to x and its
   generic restriction to the canonical generic-point morphism. Compose to obtain c.
   Its generic restriction factors through U and its closed point lies in Y_s.
6. The composite c followed by the structural map supplies R -> R0. Its composite
   into L is the original injection R -> K -> L, so it is injective. The image of the
   closed point is the closed point of Spec R; contraction of maximal ideals makes
   the ring map local. Identify L with the canonical FractionRing R0, transporting its
   K-algebra structure and finite dimension. No finiteness of R0 as an R-module is used. -/
theorem exists_dense_generic_trait
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] (hf : DenseRange f)
    (hYs : Nonempty (f.fiber (IsLocalRing.closedPoint R)))
    (U : (f.fiber (genericPoint (Spec (CommRingCat.of R)))).Opens)
    (hU : (U : Set (f.fiber (genericPoint (Spec (CommRingCat.of R))))).Nonempty) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : IsDomain R₀)
      (_ : IsDiscreteValuationRing R₀) (_ : Algebra R R₀)
      (_ : Algebra K (FractionRing R₀)),
      Function.Injective (algebraMap R R₀) ∧ IsLocalHom (algebraMap R R₀) ∧
      FiniteDimensional K (FractionRing R₀) ∧
      (algebraMap K (FractionRing R₀)).comp (algebraMap R K) =
        (algebraMap R₀ (FractionRing R₀)).comp (algebraMap R R₀) ∧
      ∃ c : Spec (CommRingCat.of R₀) ⟶ Y,
        c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R₀)) ∧
        f (c (IsLocalRing.closedPoint R₀)) = IsLocalRing.closedPoint R ∧
        ∃ cη : Spec (CommRingCat.of (FractionRing R₀)) ⟶ U.toScheme,
          cη ≫ U.ι ≫ f.fiberι (genericPoint (Spec (CommRingCat.of R))) =
            Spec.map (CommRingCat.ofHom (algebraMap R₀ (FractionRing R₀))) ≫ c := by
  sorry

end AlgebraicGeometry
