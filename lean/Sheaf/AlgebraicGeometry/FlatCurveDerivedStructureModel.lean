/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit
import Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel

/-! # The two-degree derived structure model of a proper flat curve family

Source: Stacks Project, Tag 0GKA, proof of lemma-genus-in-nodal-family-of-curves;
Tags 0B91, 0E62, 02UZ and 0BCD
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model).

The hypotheses used from the nodal setting are stated explicitly: proper flat finite
presentation, fibre dimension at most one, and fibrewise constant global functions.
The auxiliary constructions below merely name the structure complex, its unit, its
first cohomology, and its canonical base-change arrow, all using the shared library.
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The abbreviation `K = Rf_*(O_X[0])` in the structure-model statement.
Source: Stacks, Tag 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
abbrev derivedStructureImage {X S : Scheme.{u}} (f : X ⟶ S) :
    schemeDerivedCategory S :=
  (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
      (SheafOfModules.unit X.ringCatSheaf))

/-- The derived structural unit: the ordinary structural map in degree zero followed
by the canonical right-derived unit. Its H0 is structural function pullback by
`Scheme.Modules.canonicalDirectImageH0Unit`.
Source: Stacks, Tag 0E62, proof, and Tag 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
def derivedStructureUnit {X S : Scheme.{u}} (f : X ⟶ S) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ derivedStructureImage f :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    Scheme.Modules.canonicalSingleDirectImageMap f (SheafOfModules.unit X.ringCatSheaf)

/-- The abbreviation `E = H^1(K)` in the structure-model statement.
Source: Stacks, Tag 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
abbrev derivedStructureH1 {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj (derivedStructureImage f)

/-- Canonical structure-sheaf base change. The pinned tensor-pullback counit in
`canonicalSinglePullbackMap` is transported through the unique adjunction-preserving
tensor-to-ordinary pullback isomorphism. Composing with the ordinary adjoint structural
map identifies the pulled-back unit with the unit on the fibre product. Thus this is
the canonical module base-change arrow with target `Rf_{T,*}(O_{X_T}[0])`.
Source: Stacks, Tags 08HY, 0096, 0B91 and 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
def derivedStructureBaseChangeMap {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    (derivedPullback g).obj (derivedStructureImage f) ⟶
      derivedStructureImage (pullback.snd f g) :=
  schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map
      (Scheme.Modules.canonicalSinglePullbackMap (pullback.fst f g)
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit (pullback.fst f g).toRingCatSheafHom))

/-- The structure complex of a proper flat finitely presented family with fibres of
dimension at most one and only constant global functions is locally `O_S[0] ⊕ E[-1]`,
with `E` quasi-coherent finite locally free. The structural H0 unit and every canonical
derived base-change map are invertible, and all other cohomology sheaves vanish.
Source: Stacks, Tag 0GKA, proof, using only the explicitly stated fibre assumptions
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model).

Proof:
1. Apply lem-pc-rf-perfect-base-change (Tag 0B91) to O_X: it has the one-generator
   presentation without relations and is relatively flat because f is flat. This gives
   perfectness and arbitrary canonical module base change. The adjoint structural
   map identifies the ordinary pulled-back unit with O_{X_T}, giving the displayed
   base-change arrow. By lem-sc-perfect-qcoherent every cohomology sheaf is quasi-coherent.
2. Apply lem-sc-flat-derived-structure-unit and
   lem-sc-perfect-degree-zero-fibre-criterion (Tag 0E62). The fibrewise H0 assumption
   and negative residue vanishing give local decompositions O_S[0] ⊕ P, with P perfect
   of Tor-amplitude in [1,infinity). The degree-zero map of the supplied lift equals
   that of the explicitly defined derivedStructureUnit, so H0 of this unit is invertible.
3. By lem-sfb-finite-type-composition-base-change, each fibre is finite type over its
   residue field. That spectrum is Noetherian, so lem-weil-pbc-finite-type-over-noetherian
   makes the fibre Noetherian. Apply lem-sc-noetherian-cohomology-above-dimension
   (Tag 02UZ): its structure cohomology vanishes above degree one. Canonical base change
   identifies this with residue cohomology of K.
4. Pull the decomposition to each residue field. P has zero cohomology below one by its
   Tor-amplitude and above one by step 3. Apply lem-sc-perfect-finite-free-residue-model
   (Tag 0BCD). Locally its finite free representative has a single nonzero term in
   degree one, hence zero differentials. That term is H1(P) = E. These neighbourhoods
   give finite local freeness and the required splitting, and show locally, hence
   globally, that all cohomology in degrees other than zero and one vanishes. -/
theorem flatCurve_derivedStructure_model
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (hconstants : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    S.IsPerfect (derivedStructureImage f) ∧
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map (derivedStructureUnit f)) ∧
      (derivedStructureH1 f).IsQuasicoherent ∧
      (derivedStructureH1 f).IsFiniteLocallyFree ∧
      (∀ s : S, ∃ U : S.Opens, s ∈ U ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj (derivedStructureImage f) ≅
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
                (SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)) ⊞
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
                ((derivedStructureH1 f).over U))⟦(-1 : ℤ)⟧)) ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj (derivedStructureImage f))) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (derivedStructureBaseChangeMap f g)) := by
  sorry

end

end AlgebraicGeometry
