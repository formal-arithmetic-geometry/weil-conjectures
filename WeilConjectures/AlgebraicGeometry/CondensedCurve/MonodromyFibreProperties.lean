/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedLisseMonodromy
public import Mathlib.RepresentationTheory.Coinvariants
import WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberMaps

/-! # Finiteness and functoriality of the actual geometric monodromy fibre

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`sk-l-dl-a1-endpoints.proof.md`, the monodromy coinvariant formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurve

/-- The actual condensed fibre of a lisse module is finite dimensional.
Source: latest blueprint, the geometric monodromy in the endpoint formula
(blueprint: lem-per-monodromy-fibre-properties).

Proof: the specified fibre comparison identifies the condensed fibre with its
classical algebraic-coefficient fibre. The latter is scalar extension of the
rational fibre of its defining coefficient pair. That rational fibre is scalar
extension of a finite integral fibre. Finite generation is preserved by both
scalar extensions and by the specified linear equivalence. -/
theorem monodromy_fibre_finite (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [IsNoetherian X] [X.IsSeparated]
    [∀ z : X, Invertible (ℓ : X.residueField z)]
    (C : Comparison ℓ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X) (L : Lisse ℓ X) :
    Module.Finite (Coeff.{u} ℓ) ((fibre ℓ η).obj L) := by
  let F := C.equivalence.functor.obj L
  let P := Scheme.lisseAlgebraicPair ℓ X (Coeff.{u} ℓ) F
  let M := Scheme.lisseCoefficientPairModel ℓ X (Coeff.{u} ℓ) P
  have hI := Scheme.lisseIntegralFiber_finite X η ℓ P.base.val M.integral
  have hR : Module.Finite P.base.val (Scheme.lisseRationalFiber ℓ P.base.val X η M) := by
    dsimp [Scheme.lisseRationalFiber]
    infer_instance
  have hA : Module.Finite (Coeff.{u} ℓ)
      (Scheme.lisseAlgebraicFiber ℓ X (Coeff.{u} ℓ) η F) := by
    dsimp [Scheme.lisseAlgebraicFiber]
    change Module.Finite (Coeff.{u} ℓ)
      (TensorProduct P.base.val (Coeff.{u} ℓ) (Scheme.lisseRationalFiber ℓ P.base.val X η M))
    infer_instance
  exact Module.Finite.equiv (C.beta ℓ η L).symm

/-- Fibre morphisms intertwine every representation normalized by `Comparison.path`.
Source: latest blueprint, the natural monodromy coinvariant formula
(blueprint: lem-per-monodromy-fibre-properties).

Proof: the comparison path is a composite of three natural isomorphisms: the
inverse fibre comparison, the classical algebraic path, and the fibre comparison.
Its naturality square is exactly the intertwining equation. Substitute the given
normalization of both representations; the underlying linear map is unchanged. -/
theorem monodromy_fibre_intertwining (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [IsNoetherian X] [X.IsSeparated]
    [∀ z : X, Invertible (ℓ : X.residueField z)]
    (C : Comparison ℓ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X)
    (ρ : ∀ L : Lisse ℓ X,
      Representation (Coeff.{u} ℓ) (Aut (Scheme.FiniteEtale.fiber η)) ((fibre ℓ η).obj L))
    (hρ : ∀ (L : Lisse ℓ X) (τ : Aut (Scheme.FiniteEtale.fiber η))
      (v : (fibre ℓ η).obj L), ρ L τ v = C.path ℓ τ L v)
    (L L' : Lisse ℓ X) (f : L ⟶ L') :
    ∃ q : Representation.IntertwiningMap (ρ L) (ρ L'),
      q.toLinearMap = ((fibre ℓ η).map f).hom := by
  refine ⟨{ toLinearMap := ((fibre ℓ η).map f).hom, isIntertwining' := ?_ }, rfl⟩
  intro τ
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, hρ]
  let e := (C.fibreIso Ω η).symm ≪≫
    Functor.isoWhiskerLeft C.equivalence.functor
      (C.classicalPaths.algebraic.map η η (CondensedLisseMonodromy.flcPath τ)) ≪≫
    C.fibreIso Ω η
  exact (ConcreteCategory.congr_hom (e.hom.naturality f) v).symm

end AlgebraicGeometry.ProEtale.CondensedCurve
