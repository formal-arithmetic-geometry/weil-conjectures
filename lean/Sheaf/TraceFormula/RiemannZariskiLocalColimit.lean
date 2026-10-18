/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple

/-!
# Valuation rings as local colimits of centred quasi-models

Source: Temkin, *Stable modification*, §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5,
pp. 15--17 (blueprint: lem-trf-riemann-zariski-local-colimit).

## Main definitions and statement

* `CenteredQuasiModel`, `CenteredRefinement`, `CenteredQuasiModelIso`: the actual
  models, their refinement morphisms, and their isomorphisms.
* `CenteredQuasiModel.localToValuation`, `CenteredQuasiModel.localToField`,
  `CenteredRefinement.localMap`: canonical maps on centre local rings.
* `CenteredLocalSystem`: a complete small skeleton and its canonical ring and scheme diagrams.
* `LocalColimitData`: the two Mathlib universal properties of these canonical diagrams.
* `riemann_zariski_local_colimit`: existence for the full and both restricted families.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RiemannZariski

/-- A centred quasi-model for a valuation point. Source: Temkin §3.2, p. 15
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
structure CenteredQuasiModel
    (T : Scheme.{u}) (L : Type u) [Field L]
    (η : Spec (.of L) ⟶ T) (V : ValuationSubring L)
    (s : Spec (.of V) ⟶ T) where
  model : QuasiModel T L η
  centre : model.X
  lift : Spec (.of V) ⟶ model.X
  lift_map : lift ≫ model.map = s
  lift_generic : Spec.map (CommRingCat.ofHom V.subtype) ≫ lift = model.generic
  lift_centre : lift (IsLocalRing.closedPoint V) = centre

/-- A refinement map between centred quasi-models, over `T` and the two
specified spectra. Source: Temkin §3.2, p. 15
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
structure CenteredRefinement
    {T : Scheme.{u}} {L : Type u} [Field L]
    {η : Spec (.of L) ⟶ T} {V : ValuationSubring L}
    {s : Spec (.of V) ⟶ T}
    (U U' : CenteredQuasiModel T L η V s) where
  hom : U'.model.X ⟶ U.model.X
  over : hom ≫ U.model.map = U'.model.map
  valuation : U'.lift ≫ hom = U.lift
  generic : U'.model.generic ≫ hom = U.model.generic
  centre : hom U'.centre = U.centre

/-- Isomorphisms of centred quasi-models preserve the maps to `T` and from `Spec L`
and `Spec V`. Source: Temkin §3.2, p. 15
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
structure CenteredQuasiModelIso
    {T : Scheme.{u}} {L : Type u} [Field L]
    {η : Spec (.of L) ⟶ T} {V : ValuationSubring L}
    {s : Spec (.of V) ⟶ T} (U U' : CenteredQuasiModel T L η V s) where
  iso : U.model.X ≅ U'.model.X
  over : iso.hom ≫ U'.model.map = U.model.map
  valuation : U.lift ≫ iso.hom = U'.lift
  generic : U.model.generic ≫ iso.hom = U'.model.generic

variable {T : Scheme.{u}} {L : Type u} [Field L]
  {η : Spec (.of L) ⟶ T} {V : ValuationSubring L} {s : Spec (.of V) ⟶ T}

/-- The actual map to `V` induced by the lift on the stalk at its closed point.
Source: Temkin Lemma 3.2.2; Stacks 01J6
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredQuasiModel.localToValuation (U : CenteredQuasiModel T L η V s) :
    U.model.X.presheaf.stalk U.centre →+* V :=
  ((U.model.X.presheaf.stalkCongr (.of_eq U.lift_centre.symm)).hom ≫
    Scheme.stalkClosedPointTo U.lift).hom

/-- The generic embedding of a centre local ring into the specified field `L`.
Source: Temkin §3.2 and the stalk inclusions of Lemma 3.2.2
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredQuasiModel.localToField (U : CenteredQuasiModel T L η V s) :
    U.model.X.presheaf.stalk U.centre →+* L :=
  U.model.toGenericScheme.fieldEmbedding.comp
    (algebraMap (U.model.X.presheaf.stalk U.centre) U.model.X.functionField)

/-- The transition homomorphism is the stalk map of the specified refinement,
transported along its equality of centres. Source: Temkin §3.2, Lemma 3.2.2
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredRefinement.localMap {U U' : CenteredQuasiModel T L η V s}
    (r : CenteredRefinement U U') :
    U.model.X.presheaf.stalk U.centre →+* U'.model.X.presheaf.stalk U'.centre :=
  ((U.model.X.presheaf.stalkCongr (.of_eq r.centre.symm)).hom ≫
    r.hom.stalkMap U'.centre).hom

/-- A small directed skeleton of all centred quasi-models satisfying `P`.
The maps on this skeleton are defined canonically below from its refinement data.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
structure CenteredLocalSystem
    {T : Scheme.{u}} {L : Type u} [Field L]
    {η : Spec (.of L) ⟶ T} {V : ValuationSubring L}
    {s : Spec (.of V) ⟶ T}
    (P : CenteredQuasiModel T L η V s → Prop) where
  I : Type u
  [order : PartialOrder I]
  [nonempty : Nonempty I]
  [directed : IsDirected I (· ≤ ·)]
  U : I → CenteredQuasiModel T L η V s
  admissible : ∀ i, P (U i)
  /-- Every admissible centred model occurs up to the specified isomorphism. -/
  complete : ∀ Q : CenteredQuasiModel T L η V s,
    P Q → ∃ i, Nonempty (CenteredQuasiModelIso Q (U i))
  representatives : ∀ i j, Nonempty (CenteredQuasiModelIso (U i) (U j)) → i = j
  le_iff_refinement : ∀ i j, i ≤ j ↔ Nonempty (CenteredRefinement (U i) (U j))
  refinement : ∀ {i j}, i ≤ j → CenteredRefinement (U i) (U j)
  refinement_unique : ∀ {i j}
    (r r' : CenteredRefinement (U i) (U j)), r.hom = r'.hom

attribute [instance] CenteredLocalSystem.order CenteredLocalSystem.nonempty
  CenteredLocalSystem.directed

namespace CenteredLocalSystem

/-- The canonical transition induced by the selected refinement.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def ringMap {P : CenteredQuasiModel T L η V s → Prop}
    (d : CenteredLocalSystem P) {i j : d.I} (h : i ≤ j) :
    (d.U i).model.X.presheaf.stalk (d.U i).centre →+*
      (d.U j).model.X.presheaf.stalk (d.U j).centre :=
  (d.refinement h).localMap

/-- The canonical map from a centre stalk to the fixed valuation ring.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def intoV {P : CenteredQuasiModel T L η V s → Prop}
    (d : CenteredLocalSystem P) (i : d.I) :
    (d.U i).model.X.presheaf.stalk (d.U i).centre →+* V :=
  (d.U i).localToValuation

end CenteredLocalSystem

/-- Properties of the canonical maps on a centred local system.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
structure CenteredLocalSystemData
    {T : Scheme.{u}} {L : Type u} [Field L]
    {η : Spec (.of L) ⟶ T} {V : ValuationSubring L}
    {s : Spec (.of V) ⟶ T}
    {P : CenteredQuasiModel T L η V s → Prop}
    extends CenteredLocalSystem P where
  ringMap_local : ∀ {i j} (h : i ≤ j),
    IsLocalHom (CenteredLocalSystem.ringMap toCenteredLocalSystem h)
  ringMap_injective : ∀ {i j} (h : i ≤ j),
    Function.Injective (CenteredLocalSystem.ringMap toCenteredLocalSystem h)
  ringMap_id : ∀ i,
    CenteredLocalSystem.ringMap toCenteredLocalSystem (le_refl i) = RingHom.id _
  ringMap_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k),
    (CenteredLocalSystem.ringMap toCenteredLocalSystem hjk).comp
      (CenteredLocalSystem.ringMap toCenteredLocalSystem hij) =
      CenteredLocalSystem.ringMap toCenteredLocalSystem hik
  intoV_local : ∀ i, IsLocalHom (CenteredLocalSystem.intoV toCenteredLocalSystem i)
  intoV_injective : ∀ i, Function.Injective (CenteredLocalSystem.intoV toCenteredLocalSystem i)
  insideL : ∀ i, V.subtype.comp (CenteredLocalSystem.intoV toCenteredLocalSystem i) =
    (U i).localToField
  intoV_compat : ∀ {i j} (h : i ≤ j),
    (CenteredLocalSystem.intoV toCenteredLocalSystem j).comp
      (CenteredLocalSystem.ringMap toCenteredLocalSystem h) =
      CenteredLocalSystem.intoV toCenteredLocalSystem i

/-- The centre local-ring diagram with the canonical refinement stalk maps.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredLocalSystemData.ringDiagram
    {P : CenteredQuasiModel T L η V s → Prop} (d : CenteredLocalSystemData (P := P)) :
    d.I ⥤ CommRingCat.{u} where
  obj i := (d.U i).model.X.presheaf.stalk (d.U i).centre
  map f := CommRingCat.ofHom (CenteredLocalSystem.ringMap d.toCenteredLocalSystem (leOfHom f))
  map_id i := by
    change CommRingCat.ofHom (CenteredLocalSystem.ringMap d.toCenteredLocalSystem (le_refl i)) = _
    rw [d.ringMap_id]
    rfl
  map_comp {i j k} f g := by
    change CommRingCat.ofHom
      (CenteredLocalSystem.ringMap d.toCenteredLocalSystem (leOfHom (f ≫ g))) =
      CommRingCat.ofHom ((CenteredLocalSystem.ringMap d.toCenteredLocalSystem (leOfHom g)).comp
        (CenteredLocalSystem.ringMap d.toCenteredLocalSystem (leOfHom f)))
    exact congrArg CommRingCat.ofHom
      (d.ringMap_comp i j k (leOfHom f) (leOfHom g) (leOfHom (f ≫ g))).symm

/-- The canonical cocone into the given valuation ring.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredLocalSystemData.ringCocone
    {P : CenteredQuasiModel T L η V s → Prop} (d : CenteredLocalSystemData (P := P)) :
    Cocone d.ringDiagram where
  pt := .of V
  ι :=
    { app := fun i ↦ CommRingCat.ofHom (CenteredLocalSystem.intoV d.toCenteredLocalSystem i)
      naturality := fun _ _ f ↦ by
        change CommRingCat.ofHom ((CenteredLocalSystem.intoV d.toCenteredLocalSystem _).comp
          (CenteredLocalSystem.ringMap d.toCenteredLocalSystem (leOfHom f))) =
          CommRingCat.ofHom (CenteredLocalSystem.intoV d.toCenteredLocalSystem _)
        exact congrArg CommRingCat.ofHom (d.intoV_compat (leOfHom f)) }

/-- The affine spectra diagram of the canonical ring diagram.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredLocalSystemData.schemeDiagram
    {P : CenteredQuasiModel T L η V s → Prop} (d : CenteredLocalSystemData (P := P)) :
    d.Iᵒᵖ ⥤ Scheme.{u} := d.ringDiagram.op ⋙ Scheme.Spec

/-- The spectrum cone induced by the canonical valuation-ring cocone.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5.
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
def CenteredLocalSystemData.schemeCone
    {P : CenteredQuasiModel T L η V s → Prop} (d : CenteredLocalSystemData (P := P)) :
    Cone d.schemeDiagram := Scheme.Spec.mapCone d.ringCocone.op

/-- The canonical ring cocone is colimiting, and its spectrum cone is limiting.
These use Mathlib's universal-property predicates on the actual diagrams.
Source: Temkin §3.2, Lemma 3.2.2 and Corollaries 3.2.4--3.2.5; Stacks 01YW
(blueprint: lem-trf-riemann-zariski-local-colimit). -/
structure LocalColimitData
    {T : Scheme.{u}} {L : Type u} [Field L]
    {η : Spec (.of L) ⟶ T} {V : ValuationSubring L}
    {s : Spec (.of V) ⟶ T}
    (P : CenteredQuasiModel T L η V s → Prop) extends CenteredLocalSystemData (P := P) where
  ring_colimit : IsColimit toCenteredLocalSystemData.ringCocone
  scheme_limit : IsLimit toCenteredLocalSystemData.schemeCone

/-- The valuation-centre local-colimit theorem, including the cofinal
restriction clauses. Source: Temkin, *Stable modification*, §3.2,
Lemma 3.2.2 and Corollaries 3.2.4--3.2.5. (blueprint: lem-trf-riemann-zariski-local-colimit)

Proof, following the eight steps of the node:
1. Embed each centre stalk in its function field and then in `L`, using
   `lem-sc-integral-scheme-stalks-in-function-field`. The actual lift induces
   `localToValuation` by `lem-weil-pbc-morphism-from-spec-local-ring`; the generic
   compatibility identifies its composite into `L`. Refinement stalk maps are local
   by `def-weil-locally-ringed-space-morphism`, and injective by this identification.
2. Finite type over the Noetherian base makes quasi-models Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`, and quasi-separated by
   `lem-weil-pbc-locally-noetherian-quasi-separated`. An affine centre neighbourhood
   is qcqs (`lem-weil-pbc-affine-scheme-qcqs`), its inclusion is quasi-compact
   (`lem-weil-pbc-qcqs-morphism-permanence`) and finite type
   (`lem-weil-pbc-qc-open-immersion-finite-type`). Over a fixed affine base chart,
   each finitely generated subalgebra of `V` gives an affine centred quasi-model;
   use `def-weil-finite-type-morphism`,
   `lem-sfb-finite-type-composition-base-change`, and
   `lem-weil-pbc-affine-source-morphism-separated` for its morphism properties.
3. Two refinements agree generically. Separatedness (`def-weil-proper-morphism`)
   and closed-diagonal base change (`lem-pc-closed-imm-base-change`) make their
   equalizer closed, and injectivity into the function field makes its ideal zero.
   Finite affine covers with coordinate subrings of `L`, gluing data and specified
   maps range over sets. Choose one representative of each isomorphism class.
4. The identity base model gives nonemptiness. Choose finite-type affine centre
   charts in two models over a common base chart. The subalgebra of `V` generated
   by their two finite generating sets gives a common affine refinement.
5. Adjoining any `a ∈ V` to the base chart ring gives a model whose centre stalk
   contains `a`. Its denominators lie outside the contracted maximal ideal, hence
   are units in `V` (`def-weil-pbc-localization-at-prime`). The stalk union is `V`.
6. A compatible family of ring maps defines a map on this union: pick a stalk
   containing an element; common refinements make its value independent of the
   pick. A common refinement for any two elements proves addition and multiplication
   are preserved. The union forces uniqueness (`def-weil-pbc-category-colimit`).
7. A common affine refinement with a fixed model, or with its affine centre
   neighbourhood, proves both restricted families nonempty, directed and cofinal.
   Refine the models from Step 5 into either family and repeat Step 6.
8. Apply `lem-weil-pbc-spec-colimit-limit` to the full and both restricted ring
   diagrams. The legs are exactly the spectra of `localToValuation`, and the
   transitions exactly the spectra of refinement stalk maps. -/
theorem riemann_zariski_local_colimit
    (T : Scheme.{u}) [hT : IsIntegral T]
    (t : T ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType t] [QuasiCompact t]
    (L : Type u) [Field L] [Algebra T.functionField L] [IsSepClosure T.functionField L]
    (V : ValuationSubring L)
    (s : Spec (.of V) ⟶ T)
    (hs : Spec.map (CommRingCat.ofHom V.subtype) ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
        T.fromSpecStalk (genericPoint T)) :
    Nonempty (LocalColimitData (fun _ : CenteredQuasiModel
      (T := T) (L := L) (Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
        T.fromSpecStalk (genericPoint T)) V s ↦ True)
      (η := Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
        T.fromSpecStalk (genericPoint T)) (V := V) (s := s)) ∧
      (∀ (U₀ : CenteredQuasiModel (T := T) (L := L)
          (η := Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T)) (V := V) (s := s)),
        Nonempty (LocalColimitData (fun U ↦
          Nonempty (@CenteredRefinement T L _ _ V s U₀ U))
          (η := Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T)) (V := V) (s := s))) ∧
      (∀ (U₀ : CenteredQuasiModel (T := T) (L := L)
          (η := Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T)) (V := V) (s := s))
          (W : U₀.model.X.Opens) (hW : IsAffineOpen W)
          (hx : U₀.centre ∈ W),
        Nonempty (LocalColimitData (fun U ↦ IsAffine U.model.X ∧
          ∃ r : @CenteredRefinement T L _ _ V s U₀ U,
            ∃ f : U.model.X ⟶ W.toScheme, f ≫ W.ι = r.hom)
          (η := Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T)) (V := V) (s := s))) := by
  sorry

end AlgebraicGeometry.RiemannZariski
