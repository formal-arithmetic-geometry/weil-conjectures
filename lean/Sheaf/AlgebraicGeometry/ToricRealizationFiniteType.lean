/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NO stage 2
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.AlgebraicGeometry.MonoschemeFiniteChartComponents
import Sheaf.AlgebraicGeometry.LatticeTorusCoordinatesAction
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.ComponentTorusActionLaws
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Connected.Basic
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite-type reduced toric realizations and their smooth tori

Source: ILO, Travaux de Gabber, Exposé VIII, Remark 3.1.4 and 3.1.10(ii),
Proposition 3.2.2 and 3.2.4--3.2.5, printed pp.98--100, 103; smooth torus input
in 2.3.16--2.3.17 and application in 3.2.19 (blueprint:
lem-trf-toric-realization-finite-type).

The proof first analyzes the finite monoid charts and their common generic torus,
then uses the monoid-algebra domain and finite-generator calculations.  It identifies
the generic lattice with a finite-rank free abelian group, identifies its torus with
Laurent coordinates, and checks the coaction, multiplication, and unit on monomials.
The Laurent presentation gives finite type and formal smoothness after arbitrary
base change, while the identity section gives surjectivity.  Geometric reducedness
of the torus and the tensor-product reducedness statement give reduced products.
Finally, finite coproducts preserve the reduced, finite-type, and finite-component
properties.  The proof uses the dependency nodes
`lem-trf-fg-torsionfree-group-free`, `lem-trf-affine-monoid-algebra-normalization`,
`lem-trf-geometrically-reduced-base-change`, `def-sbc-locally-finite-presentation`,
`def-sbc-first-order-thickening`, and the definitions cited below.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Monoscheme

/-- The existing component torus with its canonical group-scheme structure, obtained
from the group-algebra Hopf structure. Its underlying scheme and structure map are
`torus k C` and `torusToBase k C`, definitionally.
Source: ILO VIII 3.2.4 (blueprint: lem-trf-toric-realization-finite-type). -/
noncomputable abbrev torusGroup (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : Grp (Over (Spec (.of k))) :=
  Grp.mk ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))

/-- The rank-r coordinate torus. Its algebra is the Laurent monomial algebra on
integer exponent vectors; its canonical Hopf structure gives coordinate multiplication,
unit coordinates one, and coordinate inversion, including r = 0.
Source: ILO VIII 3.2.4--3.2.5 (blueprint: lem-trf-toric-realization-finite-type). -/
noncomputable abbrev coordinateTorusGroup (k : Type u) [Field k] (r : ℕ) :
    Grp (Over (Spec (.of k))) :=
  Grp.mk ((Spec (.of (MonoidAlgebra k (Multiplicative (Fin r → ℤ))))).asOver
    (Spec (.of k)))

private theorem finite_union (n : ℕ) (X : Fin n → Scheme.{u})
    (S : Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hr : ∀ i, IsReduced (X i))
    (ht : ∀ i, LocallyOfFiniteType (f i))
    (hq : ∀ i, QuasiCompact (f i))
    (hc : ∀ i, Finite (ConnectedComponents (X i)))
    [CompactSpace S] [QuasiSeparatedSpace S] :
    IsReduced (∐ X) ∧ Finite (ConnectedComponents (∐ X : Scheme.{u})) ∧
      LocallyOfFiniteType (Sigma.desc f) ∧ QuasiCompact (Sigma.desc f) := by
  have hri (i : Fin n) : IsReduced (X i) := hr i
  have hci (i : Fin n) : CompactSpace (X i) := by
    have : QuasiCompact (f i) := hq i
    exact QuasiCompact.compactSpace_of_compactSpace (f i)
  have hfi (i : Fin n) : Finite (ConnectedComponents (X i)) := hc i
  have : Finite (sigmaOpenCover X).I₀ := inferInstanceAs (Finite (Fin n))
  have : ∀ i, CompactSpace ((sigmaOpenCover X).X i) := hci
  have : ∀ i, IsReduced ((sigmaOpenCover X).X i) := hri
  have : CompactSpace (∐ X : Scheme.{u}) := (sigmaOpenCover X).compactSpace
  refine ⟨IsReduced.of_openCover (∐ X) (sigmaOpenCover X), ?_,
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) ht, inferInstance⟩
  let g : (Σ i, ConnectedComponents (X i)) → ConnectedComponents (∐ X : Scheme.{u}) :=
    fun ⟨i, c⟩ ↦ (Sigma.ι X i).continuous.connectedComponentsMap c
  apply Finite.of_surjective g
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, xi, rfl⟩ := (sigmaOpenCover X).exists_eq x
  exact ⟨⟨i, ConnectedComponents.mk xi⟩, by rfl⟩

private theorem component_torus_smooth (k : Type u) [Field k] [CharZero k]
    (M : Fine.{u}) (hM : M.IsTorsionFree) (C : ToricComponent M) :
    Smooth (torusToBase k C) := by
  obtain ⟨r, ⟨b⟩⟩ := (finite_chart_components_algebra k M hM C).2.1
  have : LocallyOfFiniteType (torusToBase k C) :=
    (latticeTorus_finiteType k C.lattice r b).2.1
  let : GrpObj (Over.mk (torusToBase k C)) := (torusGroup k C).grp
  exact smooth_of_grpObj_of_charZero (torusToBase k C)

private theorem component_torus_projection_surjective (k : Type u) [Field k]
    {M : Fine.{u}} (C : ToricComponent M) (Y : Scheme.{u})
    (fY : Y ⟶ Spec (.of k)) : Surjective (pullback.snd (torusToBase k C) fY) := by
  let ε := Spec.map (CommRingCat.ofHom
    (Bialgebra.counitAlgHom k (MonoidAlgebra k C.lattice)).toRingHom)
  have hε : ε ≫ torusToBase k C = 𝟙 _ := by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun c ↦
      Bialgebra.counit_algebraMap (R := k) (A := MonoidAlgebra k C.lattice) c)
  let s : Y ⟶ pullback (torusToBase k C) fY :=
    pullback.lift (fY ≫ ε) (𝟙 Y) (by simp [Category.assoc, hε])
  have hs : s ≫ pullback.snd (torusToBase k C) fY = 𝟙 Y := by simp [s]
  constructor
  intro y
  exact ⟨s y, congrArg (fun f : Y ⟶ Y ↦ f y) hs⟩

/-- Fine torsion-free monoschemes with finite affine covers have reduced finite-type
realizations, integral connected components, and smooth split component tori.
The group objects carry the canonical Hopf structures: comultiplication sends each
monomial to its tensor square and the counit sends it to one. Thus the Laurent
coordinate group has coordinatewise multiplication and identity coordinates one.
The action is required to be the specified chartwise coaction, with the group-action
identities supplied by `ModObj`. The base field `ULift.{u} ℚ` is just the rational
numbers placed in the universe of the monoscheme and its realization.

Source: ILO, Travaux de Gabber, Exposé VIII, Remark 3.1.4 and 3.1.10(ii),
Proposition 3.2.2 and 3.2.4--3.2.5, pp.98--100,103; 2.3.16--2.3.17 and 3.2.19
(blueprint: lem-trf-toric-realization-finite-type).

Proof plan:
1. In a finite monoid chart the prime ideals are determined by the finite set of
   generators they contain. The empty prime is its unique generic point. These
   generic points agree on overlaps, partitioning the monoscheme into finitely many
   clopen irreducible components (`def-trf-fine-fan-blowup`,
   `def-trf-monoscheme-toric-realization`, `def-weil-connected-scheme`).
2. Each generic lattice is generated by the chart generators and is torsion free
   by the hypothesis. Apply `lem-trf-fg-torsionfree-group-free` to choose a finite
   integral basis, including the empty basis in rank zero.
3. By `lem-trf-affine-monoid-algebra-normalization`, the chart algebras are domains.
   Their local rings are reduced. The monomials of the finite monoid generators
   generate these algebras, so the finite affine cover gives finite type
   (`def-pc-reduced-scheme`, `def-weil-finite-type-morphism`).
4. Invert the product of all chart generators to obtain the common group algebra.
   Its spectrum is a nonempty dense torus in every chart of its component. Therefore
   each realized component is irreducible and reduced, hence integral. Realization
   respects the disjoint clopen decomposition (`def-pc-integral-scheme`).
5. The lattice basis identifies its group algebra with Laurent monomials. This
   identification preserves comultiplication, counit, and antipode on monomials,
   giving a group-scheme isomorphism with coordinatewise multiplication and unit one.
   The chart coactions satisfy the action identities on monomials and agree on
   localizations, so they give the indicated action on the component.
6. Over any affine base R, the torus product is the Laurent algebra over R, with
   presentation R[t_i,u_i]/(t_i*u_i-1). This gives finite presentation and, for a
   finite-type base, finite type (`def-sbc-locally-finite-presentation`).
7. Units lift over a square-zero ideal: if v*w=1+j, then w*(1-j) is the inverse of v.
   These lifts prove formal smoothness and hence smoothness of the projection
   (`def-sbc-first-order-thickening`, `def-sbc-smooth-morphisms`).
8. Evaluating all Laurent variables at one gives a section of the projection to Y,
   proving surjectivity, including rank zero and empty Y (`def-pc-fibre-product`).
9. The group algebra stays a domain over every extension field by the affine monoid
   lemma. Apply `lem-trf-geometrically-reduced-base-change` to every reduced affine
   chart of Y. Localization preserves reducedness, giving a reduced product.
10. For a finite disjoint union, local rings come from the summands, the union of
    their finite affine covers is finite, and connected components come from the
    summands. This also covers the empty monoscheme and empty disjoint union. -/
theorem toric_realization_finite_type (M : Fine.{u})
    (hM : Fine.IsTorsionFree M) :
    IsReduced (realization (ULift.{u} ℚ) M) ∧
      LocallyOfFiniteType (realizationToBase (ULift.{u} ℚ) M) ∧
      QuasiCompact (realizationToBase (ULift.{u} ℚ) M) ∧
      Finite (ConnectedComponents (realization (ULift.{u} ℚ) M).carrier) ∧
      (∀ D : ConnectedComponents (realization (ULift.{u} ℚ) M).carrier,
        ∃ C : ToricComponent M,
          Set.range (componentι (ULift.{u} ℚ) C) =
            {x | ConnectedComponents.mk x = D}) ∧
      (∀ C : ToricComponent M,
        IsIntegral (componentRealization (ULift.{u} ℚ) C) ∧
          ∃ r : ℕ,
            Nonempty (C.lattice ≃* Multiplicative (Fin r → ℤ)) ∧
            Nonempty (torusGroup (ULift.{u} ℚ) C ≅
              coordinateTorusGroup (ULift.{u} ℚ) r) ∧
            Smooth (torusToBase (ULift.{u} ℚ) C) ∧
            LocallyOfFiniteType (torusToBase (ULift.{u} ℚ) C) ∧
            QuasiCompact (torusToBase (ULift.{u} ℚ) C) ∧
            IsCanonicalTorusAction (ULift.{u} ℚ) C (torusAction (ULift.{u} ℚ) C) ∧
            ∃ action : ModObj
                (torusGroup (ULift.{u} ℚ) C).X
                (Over.mk (componentToBase (ULift.{u} ℚ) C)),
              action.smul.left = torusAction (ULift.{u} ℚ) C) ∧
      (∀ (C : ToricComponent M) (Y : Scheme.{u})
          (fY : Y ⟶ Spec (.of (ULift.{u} ℚ))),
        IsReduced Y → LocallyOfFiniteType fY → QuasiCompact fY →
          IsReduced (pullback (torusToBase (ULift.{u} ℚ) C) fY) ∧
            LocallyOfFiniteType
              (pullback.snd (torusToBase (ULift.{u} ℚ) C) fY ≫ fY) ∧
            QuasiCompact (pullback.snd (torusToBase (ULift.{u} ℚ) C) fY ≫ fY) ∧
            Smooth (pullback.snd (torusToBase (ULift.{u} ℚ) C) fY) ∧
            Surjective (pullback.snd (torusToBase (ULift.{u} ℚ) C) fY)) ∧
      (∀ (n : ℕ) (N : Fin n → Fine.{u}),
        (∀ i : Fin n, Fine.IsTorsionFree (N i)) →
          IsReduced (∐ fun i : Fin n => realization (ULift.{u} ℚ) (N i)) ∧
            Finite (ConnectedComponents
              (∐ fun i : Fin n => realization (ULift.{u} ℚ) (N i)).carrier) ∧
            LocallyOfFiniteType
              (Sigma.desc (fun i : Fin n => realizationToBase (ULift.{u} ℚ) (N i))) ∧
            QuasiCompact
              (Sigma.desc (fun i : Fin n => realizationToBase (ULift.{u} ℚ) (N i)))) := by
  classical
  have : CharZero (ULift.{u} ℚ) :=
    ⟨fun _ _ h ↦ Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩
  obtain ⟨hred, hft, hqc, hfin, _, ⟨e, he⟩, hint, _⟩ :=
    finite_chart_components_realization (ULift.{u} ℚ) M hM
  have hb (C : ToricComponent M) :
      ∃ r : ℕ, Nonempty (C.lattice ≃* Multiplicative (Fin r → ℤ)) :=
    (finite_chart_components_algebra (ULift.{u} ℚ) M hM C).2.1
  refine ⟨hred, hft, hqc, hfin, ?_, ?_, ?_, ?_⟩
  · intro D
    obtain ⟨C, rfl⟩ := e.surjective D
    exact ⟨C, he C⟩
  · intro C
    obtain ⟨r, ⟨b⟩⟩ := hb C
    obtain ⟨_, _, _, _, _, _, ⟨i, _⟩⟩ :=
      latticeTorus_coordinates (ULift.{u} ℚ) C.lattice r b
    obtain ⟨_, ht, hq⟩ := latticeTorus_finiteType (ULift.{u} ℚ) C.lattice r b
    have hs := component_torus_smooth (ULift.{u} ℚ) M hM C
    refine ⟨(hint C).2.1, r, ⟨b⟩, ⟨i⟩, hs, ht, hq, ?_, ?_⟩
    · exact Classical.choose_spec (existsUnique_torusAction (ULift.{u} ℚ) C).exists
    · exact component_torus_action_laws (ULift.{u} ℚ) M hM C
  · intro C Y fY hY htY hqY
    obtain ⟨r, ⟨b⟩⟩ := hb C
    have : Smooth (torusToBase (ULift.{u} ℚ) C) :=
      component_torus_smooth (ULift.{u} ℚ) M hM C
    have : IsReduced Y := hY
    have : LocallyOfFiniteType fY := htY
    have := LocallyOfFiniteType.isLocallyNoetherian fY
    obtain ⟨ht, hq⟩ :=
      ((latticeTorus_finiteType (ULift.{u} ℚ) C.lattice r b).1 (Over.mk fY)).2 htY hqY
    exact ⟨inferInstance, ht, hq, inferInstance,
      component_torus_projection_surjective (ULift.{u} ℚ) C Y fY⟩
  · intro n N hN
    have hn (i : Fin n) :=
      finite_chart_components_realization (ULift.{u} ℚ) (N i) (hN i)
    exact finite_union n (fun i ↦ realization (ULift.{u} ℚ) (N i))
      (Spec (.of (ULift.{u} ℚ)))
      (fun i ↦ realizationToBase (ULift.{u} ℚ) (N i))
      (fun i ↦ (hn i).1) (fun i ↦ (hn i).2.1)
      (fun i ↦ (hn i).2.2.1) (fun i ↦ (hn i).2.2.2.1)

end AlgebraicGeometry.Monoscheme
