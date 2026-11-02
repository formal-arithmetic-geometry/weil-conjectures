/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing

/-! # Condensed cohomology transport for geometric Frobenius

Source: latest blueprint, `def-weil-global-geometric-frobenius`, the first
isomorphism in each displayed ordinary and compact-support composite
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport).

The geometric-fibre square is constructed from the finite-field datum and the
published geometric Frobenius.  The transport laws are stated on the existing
canonical derived exchanges and compactification comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The semilinear square attached to geometric Frobenius on a finite-field fibre.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def geometricFrobeniusGeometry (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    Geometry D.k := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let Y := (D.geometricFiber Y₀).left
  let aY : Y ⟶ Spec (.of D.k) := (D.geometricFiber Y₀).hom
  let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  let b : Spec (.of D.k) ≅ Spec (.of D.k) :=
    Scheme.Spec.mapIso γ.toRingEquiv.toCommRingCatIso.op
  let gY : Y ⟶ Y := (D.geometricFrobenius Y₀).hom
  have w : gY ≫ aY = aY ≫ b.hom := by
    dsimp [gY, aY, b, WeilConjectures.FiniteFieldDatum.geometricFrobenius,
      WeilConjectures.FiniteFieldDatum.galoisMap,
      WeilConjectures.FiniteFieldDatum.geometricFiber]
    exact (D.galoisMap_projections Y₀.hom γ).2
  letI : IsSeparated aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  letI : LocallyOfFiniteType aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  letI : QuasiCompact aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  exact
    { X := Y
      X' := Y
      a := aY
      a' := aY
      b := b
      h := ⟨gY, (D.geometricFrobenius Y₀).inv,
        (D.geometricFrobenius Y₀).hom_inv_id, (D.geometricFrobenius Y₀).inv_hom_id⟩
      comm := w
      separated := inferInstance
      finiteType := inferInstance
      quasiCompact := inferInstance
      separated' := inferInstance
      finiteType' := inferInstance
      quasiCompact' := inferInstance }

/-- The actual proper/open diagram obtained by reindexing along an isomorphism.
The middle scheme is unchanged; this models base change along the base automorphism.
Source: the compact-support first arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def frobeniusReindexedSquare {k : Type u} [Field k] (q : Geometry k)
    (c : Compactification q.a) :
    CompactificationReindexing.Square c (reindex q.b.hom q.h.hom q.comm c)
      q.h.hom q.b.hom where
  middle := 𝟙 c.Z
  openSquare := by
    let : IsIso (𝟙 c.Z) := IsIso.id c.Z
    apply IsPullback.of_horiz_isIso
    exact ⟨by
      simp [reindex, Compactification.precomp, Compactification.postcomp,
        Compactification.copy]⟩
  properSquare := ⟨by
    simp [reindex, Compactification.precomp, Compactification.postcomp,
      Compactification.copy]⟩

/-- Canonically normalized comparison and compact exchange data for one fixed square.
Only compactifications of its two structure maps occur. No transport theorem for an
arbitrary semilinear square is included in this type.
Source: the compact-support first arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
structure FrobeniusTransportData {k : Type u} [Field k] (q : Geometry k) where
  pull_constructible : ∀ M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory,
    boundedConstructible (condensedRingObj Λ q.X') ((L Λ q.h.hom).obj M.obj)
  sourceCompare : ∀ c d : Compactification q.a, bc Λ q.X ⋙ C Λ c ≅ bc Λ q.X ⋙ C Λ d
  targetCompare : ∀ c d : Compactification q.a', bc Λ q.X' ⋙ C Λ c ≅ bc Λ q.X' ⋙ C Λ d
  source_refinement : ∀ (c d z : Compactification q.a)
    (r : z.Refinement c) (t : z.Refinement d)
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    (sourceCompare c d).hom.app M ≫ (CompactificationReindexing.refinement Λ t).app M.obj =
      (CompactificationReindexing.refinement Λ r).app M.obj
  target_refinement : ∀ (c d z : Compactification q.a')
    (r : z.Refinement c) (t : z.Refinement d)
    (M : (boundedConstructible (condensedRingObj Λ q.X')).FullSubcategory),
    (targetCompare c d).hom.app M ≫ (CompactificationReindexing.refinement Λ t).app M.obj =
      (CompactificationReindexing.refinement Λ r).app M.obj
  source_identity : ∀ c : Compactification q.a, sourceCompare c c = Iso.refl _
  target_identity : ∀ c : Compactification q.a', targetCompare c c = Iso.refl _
  source_cocycle : ∀ c d z : Compactification q.a,
    sourceCompare c d ≪≫ sourceCompare d z = sourceCompare c z
  target_cocycle : ∀ c d z : Compactification q.a',
    targetCompare c d ≪≫ targetCompare d z = targetCompare c z
  exchange : ∀ (c : Compactification q.a) (d : Compactification q.a'),
    bc Λ q.X ⋙ C Λ c ⋙ L Λ q.b.hom ≅ bc Λ q.X ⋙ L Λ q.h.hom ⋙ C Λ d
  exchange_normalization : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    (exchange c d).hom.app M =
      (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)).app M.obj ≫
        (targetCompare (reindex q.b.hom q.h.hom q.comm c) d).hom.app
          ⟨(L Λ q.h.hom).obj M.obj, pull_constructible M⟩

/-- The compact-support transport is insertion followed by evaluation of the exchange.
Its exchange is fixed by the proper/open reindexing and common-refinement normalization.
Source: the formula t_{!,g,M} = Γ_s(e_{!,g,M}) ∘ iota in the assigned node
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def frobeniusCompactTransport {k : Type u} [Field k] [IsAlgClosed k] (q : Geometry k)
    (S : FrobeniusTransportData Λ q) (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) :
    (Γ Λ (Spec (.of k))).obj ((C Λ c).obj M.obj) ⟶
      (Γ Λ (Spec (.of k))).obj ((C Λ d).obj ((L Λ q.h.hom).obj M.obj)) :=
  (insertion Λ q.b.hom).hom.app ((C Λ c).obj M.obj) ≫
    (Γ Λ (Spec (.of k))).map ((S.exchange c d).hom.app M)

/-- The transport conclusions for this square, on the specified maps in D(Λ(*)).
The two naturality equations quantify over all ambient derived morphisms between
bounded constructible objects. Homology uses the actual maps in every integer degree.
Source: the two first arrows in `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
structure FrobeniusTransportLaws {k : Type u} [Field k] [IsAlgClosed k] (q : Geometry k)
    (S : FrobeniusTransportData Λ q) : Prop where
  ordinary_exchange_iso : ∀ M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory,
    IsIso ((ordinary Λ q.h.hom q.a' q.a q.b.hom q.comm).app M.obj)
  ordinary_iso : ∀ M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory,
    IsIso (ordinaryTransport Λ q M.obj)
  compact_iso : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    IsIso (frobeniusCompactTransport Λ q S c d M)
  ordinary_naturality : ∀
    (M N : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) (f : M ⟶ N),
    (Γ Λ (Spec (.of k))).map ((R Λ q.a).map f.hom) ≫ ordinaryTransport Λ q N.obj =
      ordinaryTransport Λ q M.obj ≫
        (Γ Λ (Spec (.of k))).map ((R Λ q.a').map ((L Λ q.h.hom).map f.hom))
  compact_naturality : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M N : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) (f : M ⟶ N),
    (Γ Λ (Spec (.of k))).map ((C Λ c).map f.hom) ≫
        frobeniusCompactTransport Λ q S c d N =
      frobeniusCompactTransport Λ q S c d M ≫
        (Γ Λ (Spec (.of k))).map ((C Λ d).map ((L Λ q.h.hom).map f.hom))
  compactification_independent : ∀ (c d : Compactification q.a)
    (c' d' : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    (Γ Λ (Spec (.of k))).map ((S.sourceCompare c d).hom.app M) ≫
        frobeniusCompactTransport Λ q S d d' M =
      frobeniusCompactTransport Λ q S c c' M ≫
        (Γ Λ (Spec (.of k))).map ((S.targetCompare c' d').hom.app
          ⟨(L Λ q.h.hom).obj M.obj, S.pull_constructible M⟩)
  homology_iso : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) (i : ℤ),
    IsIso ((DerivedCategory.homologyFunctor _ i).map (ordinaryTransport Λ q M.obj)) ∧
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        (frobeniusCompactTransport Λ q S c d M))

/-- Geometric Frobenius preserves bounded constructibility and gives the two specified
natural scalar-linear isomorphisms of derived cohomology objects. Exact terminal
sections identify the derived evaluation with evaluation applied termwise.

Source: latest blueprint, `def-weil-global-geometric-frobenius`, the first isomorphism
in each displayed ordinary and compact-support composite
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport).

Proof:
1. The published geometric-fibre Frobenius is an automorphism over Spec(γ), with
   g_Y;a_Y = a_Y;Spec(γ). Its exact inverse image preserves bounded constructible
   complexes; this assertion needs no Weil structure on M.
2. The ordinary exchange is the unit/compositor/counit mate of this square.
   Inverse images along its horizontal isomorphisms are equivalences, so this
   specified mate is invertible and natural.
3. Reindex a compactification along the base automorphism. On its proper part use
   the ordinary exchange and on its open part the inverse open-adjunction mate.
   The finite-extension and finite-subextension-valued algebraic-closure comparison
   theorem gives invertible proper refinements on bounded constructible inputs.
   Compare to the target compactification through a common refinement. Refinement
   normalization, independence and cocycle identify these maps for every choice.
4. Terminal evaluation on the algebraically closed point is exact. Restriction
   along b gives the insertion map and preserves the constant scalars Λ(*), by
   the monoidal pullback-from-point comparison. The maps are therefore linear.
   Compose insertion with evaluation of the two exchanges. Their naturality gives
   the displayed naturality equations, and refinement descent gives independence.
5. Apply the ordinary homology functor in every i : ℤ to these derived
   isomorphisms. It preserves the inverse equations and yields both H^i transports.
-/
theorem geometricFrobeniusCohomologyTransport
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (closure : Bool) :
    letI : IsAlgClosed F.k := IsAlgClosure.isAlgClosed F.k₀
    let Λ := coefficient.{u} ell E closure
    let q := geometricFrobeniusGeometry F Y₀
    (sections Λ (Spec (.of F.k))).PreservesHomology ∧
      IsIso (sections Λ (Spec (.of F.k))).rightDerivedFunctorUnit ∧
      ∃ S : FrobeniusTransportData Λ q, FrobeniusTransportLaws Λ q S := by
  sorry

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option maxHeartbeats 0 in
-- Repeated native derived-functor endpoints need more elaboration heartbeats.
end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
