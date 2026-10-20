/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Additive
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionBoundedFlat
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFlatApproximation

/-!
# Tensoring derived global sections with a bounded-below constant integer complex

Source: Stacks Project, Etale Cohomology, Tag 0F0E (lemma-pull-out-constant);
Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lem-kun-0f0e (blueprint: lem-kun-0f0e).

Integer modules are encoded as modules over `ULift ℤ`, as in def-kun-derived-tensor.
This is the usual category of abelian groups, with its integer tensor product, transported
along `ULift.ringEquiv`. Both inputs lie in the full bounded-below derived subcategories.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale


/-- The canonical constant-coefficient projection map is an isomorphism for bounded-below
integer complexes on a quasi-compact quasi-separated scheme.
Source: Stacks Project, Tag 0F0E (blueprint: lem-kun-0f0e).

Proof: fix a cohomological degree n. The bounded-flat approximation theorem chooses
one bounded flat coefficient complex B and a map K to Q(B) inducing isomorphisms in
degree n for both functors in the canonical projection transformation. The projection
formula for bounded flat coefficient complexes makes its component at Q(B) an
isomorphism. Naturality gives the commuting square on degree-n homology. Three sides
are isomorphisms, so cancellation makes the component at K an isomorphism in degree n.
The homology functors jointly reflect isomorphisms, proving the assertion for every K.
This proof uses the actual counit-mate transformation; its formula is unchanged. -/
theorem isIso_constantDerivedProjectionMap_of_boundedBelow
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (K : DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X
      (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj K)) := by
  rw [constantDerivedProjectionMap_eq_transformation]
  apply (DerivedCategory.isIso_iff _ _).2
  intro n
  obtain ⟨B, b, N, hb, hN, hflat, f, hf, hg⟩ :=
    exists_constantProjection_boundedFlat_approximation X E K n
  simp only [constantProjectionSource_eq, constantProjectionTarget_eq,
    Arrow.mk_left, Arrow.mk_right] at hf hg
  let τ := (constantDerivedProjectionTransformation
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X).app (DerivedCategory.Plus.ι.obj E)
  let G := (Arrow.mk τ).right
  have hB : IsIso (τ.app (DerivedCategory.Q.obj B)) := by
    simpa only [constantDerivedProjectionMap_eq_transformation] using
      (@isIso_constantDerivedProjectionMap_of_bounded_flat X _ _ E B b N hb hN hflat)
  have hG : IsIso ((DerivedCategory.homologyFunctor _ n).map (G.map f)) := by
    simpa only [G, Arrow.mk_right] using hg
  have hn := congrArg (DerivedCategory.homologyFunctor _ n).map (τ.naturality f)
  simp only [Functor.map_comp] at hn
  have hc : IsIso ((DerivedCategory.homologyFunctor _ n).map
      (τ.app (DerivedCategory.Plus.ι.obj K)) ≫
      (DerivedCategory.homologyFunctor _ n).map (G.map f)) := by
    dsimp only [G, Arrow.mk_right]
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor _ n).map (G.map f))

end AlgebraicGeometry.Etale
