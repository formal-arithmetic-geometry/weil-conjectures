/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Finite scheme supporting a coherent module

Source: Stacks Project, Varieties, Tag 0AYT, proof of parts (3)--(5), and Tag 06LH
(blueprint: lem-pc-zero-support-finite-scheme).

Cohomology is computed in modules over the structure sheaf. The comparison is expressed
in modules over the global functions on `X`, restricting scalars along `i.appTop` on the
finite scheme. Thus it retains the scalar action, including the induced `k`-action.
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- A coherent module with zero-dimensional support is supported on a finite affine scheme.
Source: Stacks Project, Varieties, Tag 0AYT, proof of parts (3)--(5)
(blueprint: lem-pc-zero-support-finite-scheme).

Proof:
1. The support is closed by `lem-weil-pbc-finite-type-module-support-closed`. Finite type
   and dimension at most zero give finitely many closed points by `lem-sc-dim0-finite`.
   Apply `lem-weil-pbc-scheme-theoretic-support` to the annihilator ideal: its closed
   subscheme has underlying image exactly the support and annihilates `F`.
2. By `lem-pc-zero-dimensional-closed-subscheme-finite` (Tag 06LH), this finite-type
   zero-dimensional subscheme is finite over `k` and affine, hence `Spec A` with `A`
   finite-dimensional over `k`. The empty-support case uses the zero algebra.
3. Finite type makes `X` and the closed subscheme Noetherian. Apply
   `lem-weil-pbc-closed-immersion-coherent-equivalence` to obtain coherent `G` and
   `F ≅ i_* G`. Apply `lem-pc-closed-immersion-coherent-cohomology` for the canonical
   cohomology comparison and the projection formula. Pullback preserves invertibility;
   tensoring by an invertible module preserves coherence and nonzero stalks, so the
   twisted module is coherent with the same support, and the same comparison applies.
4. `lem-pc-finite-scheme-cohomology-tensor` on `Spec A`, `G`, and `i^* N` also gives the
   cohomology assertions (and additionally higher vanishing and the degree-zero dimension
   equality used by subsequent nodes). All comparisons respect global-function scalars.
-/
theorem coherent_zero_support_finite_scheme {k : Type v} [Field k]
    (X : Scheme.{v}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hS : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤ 0)
    (N : X.Modules) [N.IsInvertible] :
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra k A) (_ : FiniteDimensional k A)
      (i : Spec (CommRingCat.of A) ⟶ X) (_ : IsClosedImmersion i)
      (G : (Spec (CommRingCat.of A)).Modules),
      i ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧
      Set.range i.base = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      RingedSpace.IsCoherent (Spec (CommRingCat.of A)).toRingedSpace G ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward i).obj G) ∧
      Nonempty (Scheme.Modules.tensorObj F N ≅ (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.tensorObj G ((Scheme.Modules.tensorPullback i).obj N))) ∧
      RingedSpace.IsCoherent X.toRingedSpace (Scheme.Modules.tensorObj F N) ∧
      {x : X | ¬ Subsingleton ((Scheme.Modules.tensorObj F N).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ q : ℕ, Nonempty ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F ≅
        (ModuleCat.restrictScalars i.appTop.hom).obj
          ((RingedSpace.moduleCohomology (Spec (CommRingCat.of A)).toRingedSpace q).obj G))) ∧
      (∀ q : ℕ, Nonempty
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (Scheme.Modules.tensorObj F N) ≅
          (ModuleCat.restrictScalars i.appTop.hom).obj
            ((RingedSpace.moduleCohomology (Spec (CommRingCat.of A)).toRingedSpace q).obj
              (Scheme.Modules.tensorObj G ((Scheme.Modules.tensorPullback i).obj N))))) := by
  sorry

end AlgebraicGeometry
