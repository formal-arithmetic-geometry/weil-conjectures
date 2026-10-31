/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Fibre.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension

/-! # Pointwise dimension from pure geometric fibres

Source: Stacks Project, Algebra, Tag 00P4; Morphisms, Tag 02FY (1);
Varieties, Tag 0A21 (3), (5)
(blueprint: lem-trf-geometric-pure-fibre-point-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Transport local dimension by identifying the open neighbourhoods of a homeomorphism.
private theorem localDim_homeomorph_le {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)

private theorem localDim_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e x) := by
  exact le_antisymm (localDim_homeomorph_le e x)
    (by simpa using localDim_homeomorph_le e.symm (e x))

-- Over a one-point base the fibre inclusion is a surjective embedding.
private theorem localDim_asFiber_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    topologicalKrullDimAt (f.asFiber x) = topologicalKrullDimAt x := by
  have hsurj : Function.Surjective (f.fiberι (f x)) := by
    intro y
    exact ⟨(f.fiberHomeo (f x)).symm ⟨y, Subsingleton.elim _ _⟩,
      f.fiberι_fiberHomeo_symm _ _⟩
  have he := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(f.fiberι (f x)).isEmbedding, hsurj⟩
  simpa using localDim_homeomorph (he.homeomorph _) (f.asFiber x)

-- Pass purity to the subtype of the top open, as required by the open-dimension API.
private theorem pureDimension_top {X : Scheme.{u}} {d : ℕ}
    (h : X.IsPureDimension d) :
    ∀ C ∈ irreducibleComponents ↥(⊤ : X.Opens),
      topologicalKrullDim C = (d : WithBot ℕ∞) := by
  let e : ↥(⊤ : X.Opens) ≃ₜ X :=
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨Topology.IsEmbedding.subtypeVal, fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩).homeomorph _
  intro C hC
  have hC' : e.symm ⁻¹' C ∈ irreducibleComponents X := by
    apply preimage_mem_irreducibleComponents hC e.symm.isOpenEmbedding
    simpa only [e.symm.surjective.range_eq, Set.inter_univ] using hC.1.nonempty
  let eC : C ≃ₜ e.symm ⁻¹' C := e.subtype (by simp)
  exact (IsHomeomorph.topologicalKrullDim_eq eC eC.isHomeomorph).trans (h _ hC')

/-- Pure geometric fibres of a locally finitely presented morphism have local topological
Krull dimension `d`, as do the ordinary fibres, at every point. Every ordinary-fibre point
has a geometric lift, and the dimension comparison holds for every such lift.

The geometric fibre is written as the base change of the ordinary fibre to the chosen
algebraic closure, equivalently the pullback of `g` along `Spec Ω → B` by pullback pasting.
Its projection to the ordinary fibre is `pullback.fst`. The point `x` in its ordinary fibre
is Mathlib's canonical `g.asFiber x`. These are topological dimensions, not local-ring
Krull dimensions. No flatness is assumed.

Source: Stacks Project, Algebra, Tag 00P4; Morphisms, Tag 02FY (1);
Varieties, Tag 0A21 (3), (5)
(blueprint: lem-trf-geometric-pure-fibre-point-dimension).

Proof plan:
1. Finite presentation implies finite type on affine charts. The pointwise criterion
   (lem-weil-pbc-lft-pointwise-criterion) gives local finite type, and base change
   (lem-weil-pbc-lft-base-change) gives it for the ordinary and geometric fibres.
2. Pullback pasting identifies the geometric fibre with the displayed base change.
   The map of field spectra is surjective (lem-pc-field-extension-surjective), hence
   so is its base change (lem-weil-pbc-surjective-base-change). Lift `g.asFiber x`;
   this also makes the geometric fibre nonempty, so `hpure` applies.
3. Fibre-dimension invariance under base change (lem-sc-fibre-dimension-after-base-change,
   Tag 02FY (1), from Tag 00P4) identifies the ordinary and geometric local dimensions
   for every lift. The fibre over the unique point of `Spec Ω` is the geometric fibre.
4. Every component of that fibre has dimension `d` by def-weil-pure-dimension.
   Apply lem-sbc-equidimensional-open-local-dimension to the whole geometric fibre
   as its own open subset; it is locally of finite type over Ω by Step 1. Its local
   dimension is `d` at every point, giving both equalities and the final conclusion.
-/
theorem geometric_pure_fibre_point_dimension
    {T B : Scheme.{u}} (g : T ⟶ B) [LocallyOfFinitePresentation g] (d : ℕ)
    (hpure : ∀ (s : B) (Ω : Type u) [Field Ω] [Algebra (B.residueField s) Ω]
      [IsAlgClosure (B.residueField s) Ω],
      Nonempty ↥(pullback (g.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField s) Ω)))) →
      (pullback (g.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField s) Ω)))).IsPureDimension d)
    (x : T) (Ω : Type u) [Field Ω] [Algebra (B.residueField (g x)) Ω]
    [IsAlgClosure (B.residueField (g x)) Ω] :
    (∃ xbar : ↥(pullback (g.fiberToSpecResidueField (g x))
        (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField (g x)) Ω)))),
      pullback.fst (g.fiberToSpecResidueField (g x))
        (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField (g x)) Ω))) xbar =
          g.asFiber x) ∧
    (∀ xbar : ↥(pullback (g.fiberToSpecResidueField (g x))
        (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField (g x)) Ω)))),
      pullback.fst (g.fiberToSpecResidueField (g x))
          (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField (g x)) Ω))) xbar =
            g.asFiber x →
        topologicalKrullDimAt (g.asFiber x) = topologicalKrullDimAt xbar ∧
          topologicalKrullDimAt xbar = (d : WithBot ℕ∞)) ∧
    topologicalKrullDimAt (g.asFiber x) = (d : WithBot ℕ∞) := by
  let f := g.fiberToSpecResidueField (g x)
  let a := Spec.map (CommRingCat.ofHom (algebraMap (B.residueField (g x)) Ω))
  have : LocallyOfFiniteType f :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective a := inferInstance
  obtain ⟨xbar, hxbar⟩ := (pullback.fst f a).surjective (g.asFiber x)
  have hp : (pullback f a).IsPureDimension d := hpure (g x) Ω ⟨xbar⟩
  have hdim (y : ↥(pullback f a)) : topologicalKrullDimAt y = (d : WithBot ℕ∞) :=
    topologicalKrullDimAt_eq_of_equidimensional_open (pullback.snd f a) ⊤ d
      (pureDimension_top hp) y trivial
  have hcompare (y : ↥(pullback f a)) (hy : pullback.fst f a y = g.asFiber x) :
      topologicalKrullDimAt (g.asFiber x) = topologicalKrullDimAt y := by
    have hbc := (fibre_dimension_after_base_change f a y).2.2
    rw [localDim_asFiber_field (pullback.snd f a) y,
      localDim_asFiber_field f (pullback.fst f a y), hy] at hbc
    exact hbc.symm
  exact ⟨⟨xbar, hxbar⟩, fun y hy ↦ ⟨hcompare y hy, hdim y⟩,
    (hcompare xbar hxbar).trans (hdim xbar)⟩

end AlgebraicGeometry
