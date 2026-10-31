/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.AlgebraicGeometry.FlatRelativeAssociatedSpecialization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Relative equidimensionality from a flat associated point

Source: Stacks Project, More on Morphisms, Tag 0GSJ (lemma-flat-associated-equidimensional),
with Tag 0GSI (lemma-associated-point-specializes) as the pointwise input
(blueprint: lem-trf-flat-associated-equidimensional).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The reduced closed subscheme carried by the closure of a point.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def closureSubscheme {X : Scheme.{u}} (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme

/-- Inclusion of the reduced closure subscheme of a point.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def closureInclusion {X : Scheme.{u}} (x : X) : closureSubscheme x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι

/-- The morphism between reduced point-closure subschemes induced by a scheme morphism.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def closureMap {X S : Scheme.{u}} (f : X ⟶ S) (y : X) :
    closureSubscheme y ⟶ closureSubscheme (f y) :=
  Scheme.IdealSheafData.subschemeMap
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩)
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {f y}, isClosed_closure⟩) f (by
      rw [Scheme.IdealSheafData.map_vanishingIdeal]
      apply (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
        (I := Scheme.IdealSheafData.vanishingIdeal
          ⟨closure {f y}, isClosed_closure⟩)
        (Z := TopologicalSpace.Closeds.closure (f '' (closure {y} : Set X)))).mp
      change closure (f '' (closure {y} : Set X)) ≤ (closure {f y} : Set S)
      apply closure_minimal
      · exact (image_closure_subset_closure_image f.continuous).trans (by simp)
      · exact isClosed_closure)

/-- The pullback module on a scheme-theoretic fibre.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def fibreModule {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) :
    (f.fiber s).Modules :=
  (Scheme.Modules.tensorPullback (f.fiberι s)).obj F

/-- A point of a scheme-theoretic fibre is associated to the pulled-back module when the
maximal ideal of its local ring is an annihilator associated prime of its stalk.
Source: Stacks Project, Divisors, Tags 02OJ and 05AT.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def fibreAssociated {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    (x : f.fiber s) : Prop :=
  IsLocalRing.maximalIdeal ((f.fiber s).presheaf.stalk x) ∈
    RingTheory.annihilatorAssociatedPrimes
      ((f.fiber s).presheaf.stalk x)
      (((RingedSpace.moduleStalkFunctor (f.fiber s).toRingedSpace x).obj
        (fibreModule f F s)))

/-- The relative assassin of a finite-type quasi-coherent module, represented using the
associated point of the corresponding scheme-theoretic fibre.
Source: Stacks Project, Divisors, Tag 05AT.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def relativeAssassin {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Set X :=
  {x | ∃ z : f.fiber (f x), f.fiberι (f x) z = x ∧ fibreAssociated f F (f x) z}

/-- Stalkwise flatness of a module over the base at a point.
Source: Stacks Project, More on Morphisms, Tag 0GSJ; flatness convention Tag 01U4.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def moduleFlatAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) : Prop :=
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F
  letI : Module (S.presheaf.stalk (f x)) M :=
    Module.compHom _ (f.stalkMap x).hom
  Module.Flat (S.presheaf.stalk (f x)) M

private theorem closureInclusion_embedding {X : Scheme.{u}} (y : X) :
    Topology.IsEmbedding (closureInclusion y) := by
  delta closureInclusion
  exact Scheme.Hom.isEmbedding _

private theorem closureInclusion_range {X : Scheme.{u}} (y : X) :
    Set.range (closureInclusion y) = closure {y} := by
  change Set.range
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

private theorem closureMap_fac {X S : Scheme.{u}} (f : X ⟶ S) (y : X) :
    closureMap f y ≫ closureInclusion (f y) = closureInclusion y ≫ f := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

private theorem relativeAssassin_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) :
    x ∈ relativeAssassin f F ↔ x ∈ Scheme.Modules.relativeAssassin f F := by
  constructor
  · rintro ⟨z, hz, ha⟩
    have he : z = f.asFiber x := (f.fiberι (f x)).isEmbedding.injective
      (hz.trans (f.fiberι_asFiber x).symm)
    subst z
    exact ha
  · intro ha
    exact ⟨f.asFiber x, f.fiberι_asFiber x, ha⟩

private def closureFiberHomeo {X S : Scheme.{u}} (f : X ⟶ S) (y : X)
    (s : closureSubscheme (f y)) :
    (closureMap f y).fiber s ≃ₜ
      (f.associatedPointClosureToBase y).fiber (closureInclusion (f y) s) :=
  ((closureMap f y).fiberHomeo s).trans
    ((Homeomorph.setCongr (by
      ext z
      change closureMap f y z = s ↔
        f (closureInclusion y z) = closureInclusion (f y) s
      rw [← Scheme.Hom.comp_apply, ← closureMap_fac, Scheme.Hom.comp_apply]
      exact (closureInclusion_embedding (f y)).injective.eq_iff.symm)).trans
      ((f.associatedPointClosureToBase y).fiberHomeo _).symm)

private theorem closureFiberHomeo_ambient {X S : Scheme.{u}} (f : X ⟶ S) (y : X)
    (s : closureSubscheme (f y)) (x : (closureMap f y).fiber s) :
    f.associatedPointClosureFiberToAmbient y (closureInclusion (f y) s)
        (closureFiberHomeo f y s x) =
      closureInclusion y ((closureMap f y).fiberι s x) := by
  change closureInclusion y
    ((f.associatedPointClosureToBase y).fiberι _ (closureFiberHomeo f y s x)) = _
  congr 1
  exact (f.associatedPointClosureToBase y).fiberι_fiberHomeo_symm _ _

private theorem closure_generic_fiber_irreducible {X S : Scheme.{u}}
    (f : X ⟶ S) (y : X) :
    IrreducibleSpace ((f.associatedPointClosureToBase y).fiber (f y)) := by
  let i := closureInclusion y
  let g := f.associatedPointClosureToBase y
  have hy : y ∈ Set.range i := by
    change y ∈ Set.range (closureInclusion y)
    rw [closureInclusion_range]
    exact subset_closure (Set.mem_singleton y)
  obtain ⟨z, hz⟩ := hy
  have hgz : g z = f y := by
    change f (i z) = f y
    rw [hz]
  let w : g.fiber (f y) := (g.fiberHomeo (f y)).symm ⟨z, hgz⟩
  have hw : g.fiberι (f y) w = z := g.fiberι_fiberHomeo_symm _ _
  have hgen : IsGenericPoint w Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro v
    simp only [Set.mem_univ, iff_true]
    apply (g.fiberι (f y)).isEmbedding.isInducing.specializes_iff.mp
    apply (closureInclusion_embedding y).isInducing.specializes_iff.mp
    rw [hw, hz]
    apply specializes_iff_mem_closure.mpr
    have hv := Set.mem_range_self (f := i) (g.fiberι (f y) v)
    rw [show i = closureInclusion y from rfl, closureInclusion_range] at hv
    exact hv
  exact (irreducibleSpace_def _).mpr hgen.isIrreducible

private theorem closure_generic_fiber_dimension {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (y : X) :
    ∃ d : ℕ, topologicalKrullDim ((f.associatedPointClosureToBase y).fiber (f y)) =
      (d : WithBot ℕ∞) := by
  let g := f.associatedPointClosureToBase y
  have : LocallyOfFiniteType g := by
    dsimp [g, Scheme.Hom.associatedPointClosureToBase]
    infer_instance
  let Z := g.fiber (f y)
  let p := g.fiberToSpecResidueField (f y)
  have : LocallyOfFiniteType p := by
    dsimp [p, Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  let : Z.Over (Spec (.of (S.residueField (f y)))) := ⟨p⟩
  have : LocallyOfFiniteType (Z ↘ Spec (.of (S.residueField (f y)))) := by
    change LocallyOfFiniteType p
    infer_instance
  have : IrreducibleSpace Z := closure_generic_fiber_irreducible f y
  obtain ⟨z⟩ := (inferInstance : Nonempty Z)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hdim := (dimension_locally_algebraic (k := S.residueField (f y)) Z).1 U ⟨z, hzU⟩
  have htop : topologicalKrullDim Z ≠ ⊤ :=
    hdim ▸ hU.topologicalKrullDim_ne_top p
  have hbot : topologicalKrullDim Z ≠ ⊥ := by
    rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    exact ⟨⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  generalize topologicalKrullDim Z = n at hbot htop ⊢
  induction n using WithBot.recBotCoe with
  | bot => exact (hbot rfl).elim
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact (htop rfl).elim
    | coe n => exact ⟨n, rfl⟩

/-- A relative associated point whose fibre-closure has flat stalks at all fibre-component
 generic points yields relative association of those points and one common fibre dimension.
Source: Stacks Project, More on Morphisms, Tag 0GSJ (lemma-flat-associated-equidimensional),
parts (1) and (2), using Tag 0GSI pointwise.

Proof (deferred): identify the fibre of the reduced closure over the closure of `f y` with
its fibre over `S`, and use locally finite type fibre dimension to obtain a finite nonnegative
integer from the fibre at `f y`.  For each component, sobriety supplies its generic point;
the pointwise specialization theorem of Tag 0GSI gives relative association and equality
with this fixed dimension.  This proves both the association clause and equidimensionality.
(blueprint: lem-trf-flat-associated-equidimensional). -/
theorem flat_associated_equidimensional
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ relativeAssassin f F)
    (hflat : ∀ (s : closureSubscheme (f y)),
      ∀ C ∈ irreducibleComponents ((closureMap f y).fiber s),
        ∀ x : (closureMap f y).fiber s,
          IsGenericPoint x C →
            moduleFlatAt f F (closureInclusion y ((closureMap f y).fiberι s x))) :
    (∀ (s : closureSubscheme (f y)),
      ∀ C ∈ irreducibleComponents ((closureMap f y).fiber s),
        ∀ x : (closureMap f y).fiber s,
          IsGenericPoint x C →
            closureInclusion y ((closureMap f y).fiberι s x) ∈ relativeAssassin f F) ∧
    (∃ d : ℕ, ∀ (s : closureSubscheme (f y)),
      ∀ C ∈ irreducibleComponents ((closureMap f y).fiber s),
        topologicalKrullDim C = (d : WithBot ℕ∞)) := by
  have hpoint (s : closureSubscheme (f y))
      (C : Set ((closureMap f y).fiber s))
      (hC : C ∈ irreducibleComponents ((closureMap f y).fiber s))
      (x : (closureMap f y).fiber s) (hx : IsGenericPoint x C) :
      closureInclusion y ((closureMap f y).fiberι s x) ∈ relativeAssassin f F ∧
        topologicalKrullDim C =
          topologicalKrullDim ((f.associatedPointClosureToBase y).fiber (f y)) := by
    let e := closureFiberHomeo f y s
    have hCe : e '' C ∈ irreducibleComponents
        ((f.associatedPointClosureToBase y).fiber (closureInclusion (f y) s)) :=
      image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
        e.isOpenMap
        (fun a ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
        e.surjective hC
    have hxe : IsGenericPoint (e x) (e '' C) := by
      change closure {e x} = e '' C
      rw [← Set.image_singleton, ← e.image_closure, hx.def]
    have hf := hflat s C hC x hx
    have hf' : moduleFlatAt f F
        (f.associatedPointClosureFiberToAmbient y (closureInclusion (f y) s) (e x)) := by
      rw [show e x = closureFiberHomeo f y s x from rfl, closureFiberHomeo_ambient]
      exact hf
    obtain ⟨ha, _, hd⟩ := flat_relative_associated_specialization f F y
      ((relativeAssassin_iff f F y).mp hy) (closureInclusion (f y) s)
      (e '' C) hCe (e x) hxe hf'
    have ha' : closureInclusion y ((closureMap f y).fiberι s x) ∈
        Scheme.Modules.relativeAssassin f F := by
      simpa only [e, closureFiberHomeo_ambient] using ha
    refine ⟨(relativeAssassin_iff f F _).mpr ha', ?_⟩
    exact (e.image C).isHomeomorph.topologicalKrullDim_eq _ |>.trans hd
  refine ⟨fun s C hC x hx ↦ (hpoint s C hC x hx).1, ?_⟩
  obtain ⟨d, hd⟩ := closure_generic_fiber_dimension f y
  refine ⟨d, fun s C hC ↦ ?_⟩
  let x := hC.1.genericPoint
  have hx : IsGenericPoint x C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  exact (hpoint s C hC x hx).2.trans hd

end AlgebraicGeometry
