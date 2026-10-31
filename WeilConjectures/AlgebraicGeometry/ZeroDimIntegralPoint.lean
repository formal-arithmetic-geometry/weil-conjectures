/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension

/-!# Integral zero-dimensional schemes over algebraically closed fields

Source: Stacks Project, Varieties, Lemma 06LH.
(blueprint: lem-weil-pbc-zero-dim-integral-point)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral finite-type scheme of dimension zero over an algebraically closed field
is the point `Spec k`.

Source: Stacks Project, Varieties, Lemma 06LH; Algebra, Theorem 00FV; Fields, Lemma 09GR.
(blueprint: lem-weil-pbc-zero-dim-integral-point)

Proof:
1. Integrality gives a nonempty irreducible space (def-pc-integral-scheme). By sobriety
(lem-weil-pbc-scheme-sober), it has a unique generic point. Every point's closure is
irreducible (def-weil-irreducible-components). A proper inclusion of such a closure in Z
would give a chain of length one (def-kun-topological-krull-dimension), contradicting
zero dimension. Thus all points are generic, and Z has exactly one point.
2. Finite type (def-weil-pbc-scheme-conventions, def-weil-finite-type-morphism) gives an
affine open Spec A containing that point, hence equal to Z (def-weil-affine-spectrum).
Integrality makes A a nonzero domain; its zero ideal is its only prime. Any nonzero
nonunit would lie in a nonzero maximal ideal, so A is a field.
3. Since A is a field finitely generated over k, Zariski's lemma
(lem-weil-pbc-zariski-lemma) makes it a finite extension. Algebraic closedness
(def-weil-algebraic-closure, lem-weil-pbc-alg-closed-finite-extension-trivial) makes the
structure ring map k → A bijective.
4. The structure morphism is Spec of this ring isomorphism. Functoriality of Spec
(def-weil-affine-spectrum) gives an inverse from the inverse ring map.
-/
theorem isIso_structure_of_integral_zero_dim
    {k : Type u} [Field k] [IsAlgClosed k] (Z : Scheme.{u})
    [Z.Over (Spec (.of k))] [IsIntegral Z]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (h_dim : topologicalKrullDim Z = 0) :
    IsIso (Z ↘ Spec (.of k)) := by
  classical
  have : Subsingleton Z := by
    refine ⟨fun x y ↦ ?_⟩
    have key (z : Z) : closure {z} = (Set.univ : Set Z) := by
      let A : TopologicalSpace.IrreducibleCloseds Z :=
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
      let B : TopologicalSpace.IrreducibleCloseds Z :=
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
      have hAB : A ≤ B := Set.subset_univ _
      have hBA : B ≤ A := Order.krullDim_nonpos_iff_forall_isMax.mp h_dim.le A hAB
      exact congrArg (fun T : TopologicalSpace.IrreducibleCloseds Z ↦ (T : Set Z))
        (le_antisymm hAB hBA)
    exact (inseparable_iff_closure_eq.mpr ((key x).trans (key y).symm)).eq
  let f := Z ↘ Spec (.of k)
  let : Field Γ(Z, ⊤) := (isField_of_isIntegral_of_subsingleton Z).toField
  let φ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  have hft : φ.hom.FiniteType := by
    exact (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)
  have hi : φ.hom.IsIntegral :=
    (RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft).to_isIntegral
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral φ.hom hi)
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have : IsIso (f ≫ (Spec (.of k)).isoSpec.hom) := by
    rw [← Scheme.isoSpec_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right f (Spec (.of k)).isoSpec.hom

end AlgebraicGeometry
