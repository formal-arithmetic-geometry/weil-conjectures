/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import WeilConjectures.WeilSheaf.Stalk
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import Sheaf.DeligneLaumon.IrreducibleLisseClopenSupport
import Sheaf.DeligneLaumon.SmoothAffineConnectedConstants
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # The geometry of the connected support of a simple lisse sheaf

Source: the connected-component reduction in `sk-i-dl-general-real`.
(blueprint: lem-zl-geometrically-connected-clopen-support).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

private theorem exists_relative_dimension
    {k : Type u} [Field k] {C : Scheme.{u}} [ConnectedSpace C]
    (f : C ⟶ Spec (.of k)) [Smooth f] :
    ∃ d : ℕ, SmoothOfRelativeDimension d f := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have hlocal (x : C) : ∃ (V : C.Opens), x ∈ V ∧
      ∃ d : ℕ, SmoothOfRelativeDimension d (V.ι ≫ f) := by
    obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
    refine ⟨V, hx, d, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  choose V hxV d hd using hlocal
  have hres {W W' : C.Opens} (h : W ≤ W') (n : ℕ)
      [SmoothOfRelativeDimension n (W'.ι ≫ f)] :
      SmoothOfRelativeDimension n (W.ι ≫ f) := by
    rw [← C.homOfLE_ι h, Category.assoc]
    have : SmoothOfRelativeDimension (0 + n) (C.homOfLE h ≫ W'.ι ≫ f) := inferInstance
    simpa using this
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C)
  refine ⟨d x₀, smoothOfRelativeDimension_of_forall_exists_mem f _ fun x ↦ ?_⟩
  have heq : d x = d x₀ := by
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (V x).isOpen (V x₀).isOpen
      ⟨x, hxV x⟩ ⟨x₀, hxV x₀⟩
    have : Nonempty (V x ⊓ V x₀ : C.Opens) := ⟨⟨z, hz⟩⟩
    exact SmoothOfRelativeDimension.eq_of_field _
      (hres (W' := V x) inf_le_left (d x))
      (hres (W' := V x₀) inf_le_right (d x₀))
  exact ⟨V x, hxV x, heq ▸ hd x⟩

/-- The connected support can be regarded over its own field of constants.
No functor between Weil categories or preservation of simplicity is asserted here.

Source: blueprint `sk-i-dl-general-real`, first proof step, and
`thm-zl-real-mixed-by-curves`, geometric-component reduction.
(blueprint: lem-zl-geometrically-connected-clopen-support).

Proof: The smooth affine finite-type scheme has finitely many connected components,
all clopen. Restriction to a clopen component, followed by extension by zero, is a
lisse Weil subobject. Simplicity forces the nonzero stalks at x and y into the same
component U. Smoothness makes U normal, so connectedness makes it integral.
The algebraic closure of k₀ in its function field is a finite field k₁. Its elements
are integral over k₀, hence regular on the normal U, and define U → Spec k₁.
The constants are algebraically closed in the function field by normality and
transitivity of algebraicity. Thus the generic-point scheme is geometrically
irreducible over k₁. The connected-image criterion makes U geometrically connected.
The resulting k₁-scheme C has underlying scheme U, with its clopen inclusion
c into X. Smoothness descends along the finite separable extension k₁/k₀, and its
relative dimension is constant since C is connected. The clopen U is affine and
finite type, giving separatedness and quasi-compactness. Both marked points lift
along the scheme isomorphism C ≅ U, without changing their residue fields. The
empty scheme is excluded by the nonzero marked stalks; dimension zero is allowed. -/
theorem exists_geometrically_connected_clopen_support
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsAffine X]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (x y : X.finitePoints)
    (hx : Nontrivial (V.stalk x).carrier) (hy : Nontrivial (V.stalk y).carrier) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁)
      (_ : Fact (ringChar k₁ ≠ l)) (d : ℕ) (C : Scheme.{u})
      (_ : C.Over (Spec (CommRingCat.of k₁))) (_ : IsAffine C)
      (_ : SmoothOfRelativeDimension d (C ↘ Spec (CommRingCat.of k₁)))
      (_ : GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁)))
      (_ : IsSeparated (C ↘ Spec (CommRingCat.of k₁)))
      (_ : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁)))
      (_ : QuasiCompact (C ↘ Spec (CommRingCat.of k₁)))
      (c : C ⟶ X) (_ : IsOpenImmersion c) (_ : IsClosedImmersion c),
      c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
        (C ↘ Spec (CommRingCat.of k₁)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) ∧
      ∃ s t : C.finitePoints, c s.1 = x.1 ∧ c t.1 = y.1 := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k₀))
  have : IsNoetherian X := ⟨⟩
  let U : X.Opens := ⟨connectedComponent x.1,
    TopologicalSpace.NoetherianSpace.isOpen_connectedComponent x.1⟩
  have hU : IsClopen (U : Set X) := ⟨isClosed_connectedComponent, U.isOpen⟩
  have hxU : x.1 ∈ U := mem_connectedComponent
  have hyU : y.1 ∈ U := hV.mem_clopen_of_nontrivial_stalk V U hU x y hxU hx hy
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hU.isClosed)
  have : IsAffine U.toScheme := isAffine_of_isAffineHom U.ι
  have : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let f := U.ι ≫ (X ↘ Spec (.of k₀))
  have : Smooth f := inferInstance
  obtain ⟨k₁, hk₁, hfin₁, halg₁, g, hfg, hsm, hgeo⟩ :=
    exists_smooth_geometricallyConnected_constant_field f
  let : U.toScheme.Over (Spec (.of k₁)) := ⟨g⟩
  have : Smooth (U.toScheme ↘ Spec (.of k₁)) := hsm
  have hl : Fact (ringChar k₁ ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k₀ k₁]; exact Fact.out⟩
  obtain ⟨d, hd⟩ := exists_relative_dimension g
  let s : U.toScheme := ⟨x.1, hxU⟩
  let t : U.toScheme := ⟨y.1, hyU⟩
  have hs : s ∈ U.toScheme.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso U.ι s).mp x.2
  have ht : t ∈ U.toScheme.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso U.ι t).mp y.2
  refine ⟨k₁, hk₁, hfin₁, halg₁, hl, d, U.toScheme, inferInstance, inferInstance,
    hd, hgeo, inferInstance, inferInstance, inferInstance, U.ι, inferInstance,
    inferInstance, hfg, ⟨s, hs⟩, ⟨t, ht⟩, rfl, rfl⟩

end AlgebraicGeometry.WeilSheaf
