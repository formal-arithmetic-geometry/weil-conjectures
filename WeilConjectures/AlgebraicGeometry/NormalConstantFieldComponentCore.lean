/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentConstruction
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentRegularity
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Connected.Basic

/-! # The distinguished normal geometric component

Source: Stacks Project, varieties.tex, Tags 04PZ, 054Q, 0C3M;
fields.tex, Tag 0CKN; schemes.tex, Tags 01I4 and 01JQ.
(blueprint: lem-dl-a1-normal-constant-field-component-core).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The distinguished component is the base change through its embedding of constants.

Source: Stacks Project, fields.tex, Tag 0CKN; varieties.tex, Tags 054Q and 0C3M;
schemes.tex, Tags 01I4 and 01JQ.
(blueprint: lem-dl-a1-normal-constant-field-component-core).

Proof: the geometric point induces compatible maps from the constant field L and k into Ω.
Every element of L has a polynomial over k₀ that splits over k, so its image comes from k.
This gives the embedding σ : L → k. The finite Galois tensor isomorphism splits L ⊗[k₀] k
into copies of k indexed by embeddings of L. On an affine chart Spec B of U₀, tensor
reassociation gives B ⊗[k₀] k as the product of B ⊗[L,σ'] k over those embeddings.
The corresponding clopen affine factors commute with restriction, hence glue. The σ factor
is the pullback C of g and Spec σ. Its canonical map j is fixed by its two projections,
and the original geometric point lifts by the pullback universal property. Geometric
connectedness of g makes C nonempty and connected, so its clopen image is exactly the
connected component of the point. Every finite subextension of k/k₀ is finite separable;
normality therefore survives scalar extension on affine charts and localizations. Finite
type over k gives Noetherianness of the whole fibre, hence of the clopen component C.
The connected-space assumptions exclude an empty component; the finite-field point case
and degree one case use the same product decomposition. -/
theorem normal_constant_field_component_core
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    (hN : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk x))
    [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left),
      (∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
        IsGenericPoint
          ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 Z) →
      ∃ (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u})
        (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
        (j : C ⟶ (D.geometricFiber U₀).left),
        IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧
        j ≫ pullback.fst U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p ∧
        j ≫ pullback.snd U₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s ∧
        (∃ ηC : Spec (CommRingCat.of Ω) ⟶ C, ηC ≫ j = η) ∧
        IsOpenImmersion j ∧ IsClosedImmersion j ∧
        Set.range j = connectedComponent
          ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 ∧
        ConnectedSpace C ∧ IsNoetherian C ∧
        (∀ x : C, IsDomain (C.presheaf.stalk x) ∧
          IsIntegrallyClosed (C.presheaf.stalk x))  := by
  classical
  intro Ω instΩF instΩA η hη
  obtain ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc, hrange, hconn⟩ :=
    normal_constant_field_component_construction D U₀ b Ω η hη
  obtain ⟨hnoeth, hnormal⟩ := normal_constant_field_component_regularity D U₀ hN b Ω η
    σ C p s j hpb hp hs hηC ho hc hrange hconn
  exact ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc, hrange, hconn, hnoeth, hnormal⟩

end AlgebraicGeometry
