/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentConstruction
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.NormalityPerfectClosureTest

/-! Normality and Noetherianness of the distinguished component.

Source: Stacks Project, varieties.tex, Tag 0C3M; morphisms.tex, Tags 01T4 and 01T6.
(blueprint: lem-dl-a1-normal-constant-field-component-regularity).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Scalar extension along the algebraic closure of a finite field preserves the normal
stalks and finite-type Noetherian structure of the constructed clopen component.

Source: Stacks Project, varieties.tex, Tag 0C3M; morphisms.tex, Tags 01T4 and 01T6.
(blueprint: lem-dl-a1-normal-constant-field-component-regularity).

Proof:
1. The identity base change over `D.k₀` is an isomorphism, so its first projection identifies
   stalks; hence the hypothesis `hN` makes every stalk of the self-pullback an integrally
   closed domain.
2. The finite field `D.k₀` is perfect and every element is its own `p^0`-th power, so
   lem-weil-pbc-normality-perfect-closure-test with `K = D.k₀` extends normality to every
   field extension; specialized to `D.k` it makes every stalk of the geometric fibre an
   integrally closed domain.
3. The geometric fibre is locally of finite type and quasi-compact over the Noetherian
   `Spec D.k`, hence Noetherian.
4. The open immersion `j` identifies stalks of `C` with stalks of the geometric fibre, and
   makes `C` locally Noetherian. Its range is a connected component, a closed subset of a
   Noetherian space, hence compact; so `C` is quasi-compact and therefore Noetherian.
-/
theorem normal_constant_field_component_regularity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    (hN : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk x))
    [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left)
    (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u})
    (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
    (j : C ⟶ (D.geometricFiber U₀).left)
    (hpb : IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)))
    (hp : j ≫ pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p)
    (hs : j ≫ pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s)
    (hηC : ∃ ηC : Spec (CommRingCat.of Ω) ⟶ C, ηC ≫ j = η)
    (ho : IsOpenImmersion j) (hc : IsClosedImmersion j)
    (hrange : Set.range j = connectedComponent
      ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1)
    (hconn : ConnectedSpace C) :
    IsNoetherian C ∧
      (∀ x : C, IsDomain (C.presheaf.stalk x) ∧
        IsIntegrallyClosed (C.presheaf.stalk x)) := by
  clear hpb hp hs hηC hc hconn
  haveI : IsNoetherian (Spec (CommRingCat.of D.k)) := inferInstance
  have hgeom : IsNoetherian (D.geometricFiber U₀).left := {
    toIsLocallyNoetherian := by
      change IsLocallyNoetherian (pullback U₀.hom _)
      infer_instance
    toCompactSpace := by
      change CompactSpace ↥(pullback U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      infer_instance }
  haveI : IsNoetherian (D.geometricFiber U₀).left := hgeom
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k₀))
  have hg : IsIso g := by
    dsimp [g]
    simp only [Spec.map_id]
    infer_instance
  haveI := hg
  let q := pullback.fst U₀.hom g
  have hself (y : (pullback U₀.hom g : Scheme.{u})) :
      IsDomain ((pullback U₀.hom g : Scheme.{u}).presheaf.stalk y) ∧
        IsIntegrallyClosed ((pullback U₀.hom g : Scheme.{u}).presheaf.stalk y) := by
    let e := (asIso (q.stalkMap y)).commRingCatIsoToRingEquiv
    have := (hN (q y)).1
    have := (hN (q y)).2
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  have hnormal (y : (D.geometricFiber U₀).left) :
      IsDomain ((D.geometricFiber U₀).left.presheaf.stalk y) ∧
        IsIntegrallyClosed ((D.geometricFiber U₀).left.presheaf.stalk y) := by
    exact ((normal_stalks_perfectClosure_iff D.k₀ D.k₀
      (fun a ↦ ⟨0, a, by simp⟩) U₀.left U₀.hom).mp hself) D.k y
  haveI : IsOpenImmersion j := ho
  haveI : IsLocallyNoetherian C :=
    isLocallyNoetherian_of_isOpenImmersion j
  haveI : CompactSpace C :=
    ⟨j.isOpenEmbedding.isInducing.isCompact_iff.2 (by
      have hcomp : IsCompact (Set.range j) := by
        rw [hrange]
        exact TopologicalSpace.NoetherianSpace.isCompact _
      have himage : j '' (Set.univ : Set C) = Set.range j := by
        ext y
        constructor
        · rintro ⟨x, -, rfl⟩
          exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨x, Set.mem_univ _, rfl⟩
      rw [himage]
      exact hcomp)⟩
  have hnoeth : IsNoetherian C := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  refine ⟨hnoeth, ?_⟩
  intro x
  let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  have := (hnormal (j x)).1
  have := (hnormal (j x)).2
  exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

end AlgebraicGeometry
