/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.AlgebraicGeometry.UnresolvedStrataGeometry
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularBaseChange
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.ReducedNoetherianBlowupGeometry
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Regular pullback of unresolved sets and lowest codimension strata

Source: Temkin, Non-embedded Desingularization, §§2.1.6, 2.1.8--2.1.10,
4.1.1--4.1.3 and 4.3 (blueprint: lem-per-regular-pullback-unresolved-strata).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ResolutionStrata

/-- Regular morphisms preserve reducedness on reduced locally Noetherian base changes,
and pull back singular loci. The induced local maps are regular. In particular these
assertions apply to localizations and their finite-type base changes.
Source: Temkin §§2.1.8--2.1.10
(blueprint: lem-per-regular-pullback-unresolved-strata).

Proof (node steps 1--3): use lem-weil-pbc-flat-morphism-affine-criterion,
lem-weil-pbc-regular-local-maximal and lem-weil-pbc-localization-regular for regular stalk
maps, including localizations. lem-weil-pbc-regular-base-change applies to the finite-type
base changes used below. Identify the closed fibre with the fibre stalk by
lem-sbc-scheme-fibre-stalk-quotient. Ascend and descend regularity by
lem-weil-pbc-flat-over-regular-with-regular-fibre and lem-weil-pbc-flat-under-regular.
Regular local rings are domains by lem-sc-regular-local-domain. Detect reducedness of
finite-extension fibres using lem-weil-pbc-prime-localizations-jointly-injective, then
apply lem-trf-geometric-reducedness-finite-inseparable-test and
lem-sfb-flat-geometrically-reduced-pullback. -/
theorem regular_pullback_geometry {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y] [IsNoetherian X] [IsNoetherian Y]
    (hQX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (hQY : ∀ U : Y.affineOpens, IsQuasiExcellent Γ(Y, U))
    (h : Y ⟶ X) (hRegular : IsRegularSchemeMorphism h) :
    (∀ y : Y, (h.stalkMap y).hom.IsRegular) ∧
    singularSet Y = h ⁻¹' singularSet X ∧
    (∀ (T : Scheme.{u}) [IsReduced T] [IsLocallyNoetherian T] (f : T ⟶ X),
      IsReduced (pullback f h)) ∧
    (∀ (T : Scheme.{u}) [IsNoetherian T] (f : T ⟶ X) [LocallyOfFiniteType f],
      IsRegularSchemeMorphism (pullback.fst f h) ∧
      singularSet (pullback f h) = (pullback.fst f h) ⁻¹' singularSet T) := by
  sorry

/-- The unresolved set of any finite coherent ordinary tower is closed, and its
contracted regular pullbacks exist and have exactly the inverse-image unresolved set.
The comparison retains precisely the extended nonunit center ideals in their order.
Source: Temkin §§4.1.1, 4.3
(blueprint: lem-per-regular-pullback-unresolved-strata).

Proof (node steps 4--6): lem-per-reduced-noetherian-blowup-geometry and
lem-per-quasi-excellent-finite-type-stability apply to all levels and centers. J-2 from
def-exc-excellent-ring and lem-trf-regular-locus-affine-chart-gluing close their singular
loci. thm-nagata-global-blowup-proper, lem-weil-pbc-closed-immersion-proper and
lem-weil-pbc-proper-composition give closed images; take the finite union. Inductively
use def-nagata-blowup-flat-base-change-map and thm-nagata-blowup-flat-base-change;
cor-nagata-blowup-cartier-iso deletes exactly the empty unit-ideal centers. Step 2 identifies
all pulled-back singular loci. For each proper singular image, use
lem-weil-pbc-reduced-induced-closed-subscheme and
lem-weil-pbc-reduced-source-factors-through-closed-subscheme to factor its reduction
surjectively onto the reduced image. lem-weil-pbc-surjective-base-change then identifies
its pulled-back image with the inverse image. Empty deleted centers contribute nothing. -/
theorem unresolvedSet_isClosed_and_regular_pullback {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y] [IsNoetherian X] [IsNoetherian Y]
    (hQX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (hQY : ∀ U : Y.affineOpens, IsQuasiExcellent Γ(Y, U))
    (h : Y ⟶ X) (hRegular : IsRegularSchemeMorphism h)
    (A : OrdinaryBlowupTower X)
    (hCenters : ∀ i : Fin A.length,
      RingedSpace.IsCoherent (A.level i.castSucc).toRingedSpace (A.center i).toModules) :
    IsClosed (unresolvedSet A) ∧
    (∃ B : OrdinaryBlowupTower Y, Nonempty (OrdinaryResolutionComparison h A B)) ∧
    (∀ (B : OrdinaryBlowupTower Y) (_comparison : OrdinaryResolutionComparison h A B),
      unresolvedSet B = h ⁻¹' unresolvedSet A) := by
  sorry

/-- The lowest height stratum is finite and consists of component generic points.
Regular pullback identifies its reduced closure as a closed subscheme, not just as a set:
the equality of ideals uses the canonical scheme-theoretic ideal pullback `comap`.
Source: Temkin §§4.1.2--4.1.3, 4.3 and the flat local height formula, Stacks 00ON
(blueprint: lem-per-regular-pullback-unresolved-strata).

Proof (node steps 7--9): by lem-weil-pbc-noetherian-finitely-many-components and
lem-sc-scheme-sober there are finitely many component generic points. Strict specialization
strictly increases height; extend a prime chain, whose length is bounded by
lem-trf-noetherian-prime-finite-height. Thus the height-r points of Z are precisely its
component generic points of height r. Flat going down, lem-sc-flat-going-down, says generic
points of a reduced closed pullback are exactly fibre-generic points over generic points.
Use lem-weil-pbc-flat-height-formula and lem-sbc-scheme-fibre-stalk-quotient: height at y is
height at x plus fibre local dimension. At a fibre generic point the last term is zero;
conversely height r forces both base height r and fibre dimension zero. Reduced base change
from step 3 and lem-weil-pbc-reduced-induced-closed-subscheme give the ideal equality.
Step 1 gives regularity of all indicated local maps. The empty stratum and r=0 are allowed. -/
theorem lowestCodimensionStrata_regular_pullback {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y] [IsNoetherian X] [IsNoetherian Y]
    (hQX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (hQY : ∀ U : Y.affineOpens, IsQuasiExcellent Γ(Y, U))
    (h : Y ⟶ X) (hRegular : IsRegularSchemeMorphism h)
    (Z : Set X) (hZ : IsClosed Z) (r : ℕ)
    (hHeight : ∀ x ∈ Z, (r : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    (heightStratum Z r).Finite ∧
    heightStratum Z r ⊆ componentGenericPoints Z ∧
    heightStratum (h ⁻¹' Z) r =
      componentGenericPoints (h ⁻¹' closure (heightStratum Z r)) ∧
    (reducedClosureIdeal (heightStratum Z r)).comap h =
      reducedClosureIdeal (heightStratum (h ⁻¹' Z) r) ∧
    (∀ y ∈ componentGenericPoints (h ⁻¹' closure (heightStratum Z r)),
      h y ∈ heightStratum Z r ∧
      ringKrullDim (Y.presheaf.stalk y) = (r : WithBot ℕ∞) ∧
      (h.stalkMap y).hom.IsRegular) := by
  sorry

/-- A reduced center with pure-codimension image and schematic density over its generic
image points retains these properties after regular pullback, unless it becomes empty.
Source: Temkin §§2.1.6, 4.1.3, 4.3
(blueprint: lem-per-regular-pullback-unresolved-strata).

Proof (node steps 10--13): the center W is proper over X by
lem-weil-pbc-closed-immersion-proper. Factor W through its reduced closed image D using
lem-weil-pbc-reduced-source-factors-through-closed-subscheme. Schematic density forces every
generic point of W to map to a generic point of D: otherwise the closure of those local
schemes is a proper closed subscheme agreeing on all of them. Step 3 makes W_Y and D_Y
reduced; lem-weil-pbc-surjective-base-change gives image W_Y = D_Y, and
lem-weil-pbc-proper-base-change gives properness. Steps 8--9 give pure codimension e of D_Y.
For a generic point w' of W_Y, going down first along W_Y to W makes its image generic,
hence lying over generic s of D. In the fibre W_s times Y_s, the projection to Y_s is flat
because all vector spaces over kappa(s) are flat. A second use of lem-sc-flat-going-down
makes its image generic in Y_s, hence generic in D_Y. Finally
lem-weil-pbc-reduced-noetherian-total-ring-fractions embeds each affine ring of W_Y into
the product of its generic local rings; injectivity follows from
def-weil-pbc-module-localization, since the denominators are nonzerodivisors. All these
generic points lie over generic points of D_Y, proving schematic density there. -/
theorem equicodimensionalCenter_regular_pullback {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y] [IsNoetherian X] [IsNoetherian Y]
    (hQX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (hQY : ∀ U : Y.affineOpens, IsQuasiExcellent Γ(Y, U))
    (h : Y ⟶ X) (hRegular : IsRegularSchemeMorphism h)
    (P : Scheme.{u}) (p : P ⟶ X) [IsProper p] (I : P.IdealSheafData)
    [IsReduced I.subscheme] (e : ℕ)
    (hPure : HasPureCodimension (Set.range (I.subschemeι ≫ p)) e)
    (hDense : IsGenericallySchematicallyDense (I.subschemeι ≫ p)) :
    IsReduced (pullback (I.subschemeι ≫ p) h) ∧
    IsProper (pullback.snd (I.subschemeι ≫ p) h) ∧
    (Nonempty (pullback (I.subschemeι ≫ p) h : Scheme.{u}) →
      HasPureCodimension (Set.range (pullback.snd (I.subschemeι ≫ p) h)) e ∧
      IsGenericallySchematicallyDense (pullback.snd (I.subschemeι ≫ p) h)) := by
  sorry

end AlgebraicGeometry.ResolutionStrata
