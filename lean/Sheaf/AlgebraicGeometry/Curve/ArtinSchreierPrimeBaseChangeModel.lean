/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.LinearAlgebra.SemilinearFrobenius

/-! # Prime-coefficient Artin--Schreier comparison under field extension -/

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- Prime-coefficient first cohomology is the Frobenius kernel, naturally under base change.
Source: Stacks Project, Tag 0A3P, proof, and Tag 02KH, flat base change.
(blueprint: lem-pbc-artin-schreier-prime-base-change-model)

Proof: Use H¹(C,O_C) as V, with its scalar action and finite-dimensionality from proper
coherent cohomology and the étale/Zariski quasi-coherent comparison. The sectionwise
p-th power map induces a p-semilinear endomorphism F: the identity
(cx)^p = c^p x^p gives semilinearity after applying additive cohomology. Apply the
Artin--Schreier long exact sequence. Its degree-zero F-1 map is onto by the proper
degree-zero theorem, so the next map identifies H¹(C,Z/p) with ker(F-1). Transport
this identification through the natural Ext/derived comparison. Flat base change gives
H¹(C',O_C') = k' tensor V. Transport its Frobenius across this linear equivalence to F'.
The p-th power maps commute with pullback of functions, giving the displayed tensor
identity. Naturality of the connecting sequence then identifies cohomology pullback
with v mapping to 1 tensor v on kernels. No invariance of kernels is used. For a
connected smooth curve of dimension zero, it is Spec k, and coherent H¹ vanishes;
the same sequence makes both degree-one groups zero, giving V = 0. Thus the
exact-dimension-one scalar-model theorem is only used in the dimension-one case. -/
theorem exists_constantZMod_one_frobenius_baseChange_model
    {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (F : V →ₛₗ[frobenius k p] V)
      (F' : (k' ⊗[k] V) →ₛₗ[frobenius k' p] (k' ⊗[k] V))
      (hF' : ∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v)
      (e : Sheaf.H (C.constantZMod p) 1 ≃+ LinearMap.Frobenius.fixedPoints F)
      (e' : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj
        (C.constantZMod p)) 1 ≃+ LinearMap.Frobenius.fixedPoints F'),
      ∀ x, e' (Etale.cohomologyMap ι' (C.constantZMod p) 1 x) =
        (⟨1 ⊗ₜ[k] (e x : V), by
          rw [LinearMap.Frobenius.mem_fixedPoints, hF',
            LinearMap.Frobenius.mem_fixedPoints.mp (e x).2]⟩ :
          LinearMap.Frobenius.fixedPoints F') := by sorry

end AlgebraicGeometry.IsCurve
