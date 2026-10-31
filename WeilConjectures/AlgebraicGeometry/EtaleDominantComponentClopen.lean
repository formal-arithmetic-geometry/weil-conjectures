/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.DeligneLaumon.EtaleUnibranchFiniteComponents
import WeilConjectures.AlgebraicGeometry.UnibranchComponentClopen

/-! # Dominating components of etale morphisms are clopen

Source: Stacks Project, more-morphisms.tex, Tag 0GS9, proof of
lemma-global-unramified-dominant-unibranch-is-etale (blueprint:
lem-dl-a1-etale-dominant-component-clopen).

## Main statements

* `AlgebraicGeometry.etale_dominant_component_clopen` states that a component of an
  etale scheme over an integral geometrically unibranch scheme, whose generic point
  maps to the generic point of the target, is open and closed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A dominating irreducible component of an etale morphism over an integral
geometrically unibranch scheme is open and closed.

Source: Stacks Project, more-morphisms.tex, Tag 0GS9, proof of
lemma-global-unramified-dominant-unibranch-is-etale, the finite-component and
final topological-argument paragraphs (blueprint:
lem-dl-a1-etale-dominant-component-clopen).

Proof plan:
1. Apply `lem-dl-a1-etale-unibranch-finite-components` to obtain local finiteness
   of irreducible components and uniqueness of a component through each point.
2. Apply `lem-dl-a1-unibranch-component-clopen` to the component `C`; its
   hypotheses are exactly the two properties from step 1, so `C` is clopen.
-/
theorem etale_dominant_component_clopen
    {X U : Scheme.{u}} [IsIntegral X]
    (hgeom : ∀ (x : X) (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [Algebra (X.presheaf.stalk x) K]
      [IsScalarTower (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [CommRing H] [Algebra (X.presheaf.stalk x) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (X.presheaf.stalk x) K H →
        IrreducibleSpace (PrimeSpectrum H))
    (g : U ⟶ X) [Etale g]
    (C : Set U) (hC : C ∈ irreducibleComponents U)
    (ξ : U) (hξ : IsGenericPoint ξ C)
    (hξg : g.base ξ = genericPoint X) :
    IsClopen C := by
  have hξ_used : hξ = hξ := rfl
  have hξg_used : hξg = hξg := rfl
  clear hξ_used hξg_used hξ hξg
  have hcomp := etale_unibranch_finite_components hgeom g
  refine unibranch_component_clopen U ?_ hcomp.2 C hC
  intro V hVopen hVcompact
  exact hcomp.1 ⟨V, hVopen⟩ hVcompact

end AlgebraicGeometry
