/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.Curve.AdelicStructureSheaf
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.RingTheory.TateResidue.LocalResidue
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Sheaf.AlgebraicGeometry.Curve.PicardDuality
import Sheaf.RingTheory.TateAbstractResidueCalculus
import Sheaf.RingTheory.TateResidue.DVRResidueCalculus
import Sheaf.RingTheory.TateResidueExactSequence

/-! # Tate residues and extension of the ground field

Source: Tate, Residues of differentials on curves, pp. 149–155, §§1–3,
finite-potent traces, Theorem 1 and formula (*)
(blueprint: lem-pc-tate-residue-field-extension).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical map on rational differentials induced by a flat morphism over a
field extension. Both function-field algebras are the structure-map algebras.
The map of fields is the stalk map at the generic point, and the map on
Kähler differentials is Mathlib's map of the resulting commutative square.
Source: Tate, §3, local lattices and scalar extension
(blueprint: lem-pc-tate-residue-field-extension). -/
noncomputable def tateRationalDifferentialMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))]
    (p : Y ⟶ X) [Flat p]
    (h : p ≫ (X ↘ Spec (.of k)) =
      (Y ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    letI := functionFieldAlgebra k X
    letI := functionFieldAlgebra K Y
    KaehlerDifferential k X.functionField → KaehlerDifferential K Y.functionField := by
  letI := functionFieldAlgebra k X
  letI := functionFieldAlgebra K Y
  let ρ := p.functionFieldMap p.apply_genericPoint_of_flat
  have fac : CommRingCat.ofHom (algebraMap k K) ≫
      CommRingCat.ofHom (algebraMap K Y.functionField) =
      CommRingCat.ofHom (algebraMap k X.functionField) ≫ ρ := by
    change CommRingCat.ofHom (algebraMap k K) ≫
        (Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ Spec (.of K)).appTop ≫
          Y.presheaf.germ ⊤ (genericPoint Y) trivial =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial ≫ ρ
    dsimp [ρ, Hom.functionFieldMap]
    rw [X.presheaf.germ_stalkSpecializes_assoc, Hom.germ_stalkMap]
    rw [Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [← Hom.comp_appTop_assoc, ← h, Hom.comp_appTop]
    simp [Hom.appTop, Category.assoc]
  exact fun η ↦ CommRingCat.KaehlerDifferential.map fac η

/-- The sum of the Tate residues over the points above a closed point commutes
with arbitrary extension of the ground field. The index is the underlying
fibre, with each point occurring once, even when its scheme structure is nonreduced.
Source: Tate, pp. 149–155, §1 finite-potent trace, §2 Theorem 1 and formula (*),
§3 local residues (blueprint: lem-pc-tate-residue-field-extension).

Proof plan:
1. Apply lem-pc-curve-local-scalar-principal-parts. With F=k(C), L=K(C_K),
   O=O_{C,x}, A=O tensor_k K, V=F tensor_k K and B=intersection of O_{C_K,y}
   over the fibre, a uniformizer t gives V=A[1/t], L=B[1/t], V intersect B=A,
   finite-dimensional quotients by t^n and both principal-parts isomorphisms.
2. For f dg choose a k-linear projection pi:F→O. By
   lem-pc-tate-abstract-residue-calculus and lem-pc-tate-dvr-residue-calculus,
   the residue is the finite-potent trace of [pi m_f,m_g]. Tensor pi with K.
   A finite-dimensional stable subspace containing a sufficiently high image
   tensors to such a subspace over K. Its matrix and trace extend by k→K.
3. Apply lem-pc-tate-residue-exact-sequence to V→L→L/V with lattice B.
   The inverse-image lattice is A; the image is the whole quotient by the
   principal-parts isomorphism. Its residue is zero, so res_{L,B}=res_{V,A}.
4. Apply the same exact-sequence result to the diagonal L→product_y L,
   with lattice product_y O_y. The inverse image is B and the image is the
   whole quotient, again by principal parts. Thus its residue is res_{L,B}.
5. A product of local projections makes the commutator block diagonal. The
   finite-potent trace is the sum of the block traces: use a common power,
   stable finite-dimensional subspaces, and concatenated bases. By the DVR
   residue calculus each block trace is the corresponding local Tate residue.
6. Every rational differential is a finite sum of f dg. Extend the identity
   by linearity and interchange finite sums. Thickness is already present in
   the local quotients, so each fibre point contributes once, without a factor. -/
theorem tate_residue_field_extension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] :
    letI : GeometricallyIrreducible (C ↘ Spec (.of k)) :=
      GeometricallyIrreducible.of_smooth_of_geometricallyConnected (C ↘ Spec (.of k))
    letI : GeometricallyIntegral (C ↘ Spec (.of k)) :=
      GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
        (C ↘ Spec (.of k))
    letI := functionFieldAlgebra k C
    letI := isFunctionFieldAlgebra_functionFieldAlgebra k C
    letI := functionFieldAlgebra K (C.baseChangeField k K)
    letI := isFunctionFieldAlgebra_functionFieldAlgebra K (C.baseChangeField k K)
    ∀ (x : C), IsClosed ({x} : Set C) → ∀ η : KaehlerDifferential k C.functionField,
      (∑ᶠ y : {y : C.baseChangeField k K //
          pullback.fst (C ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) y = x},
        TateResidue.localRes (localSubalgebra K (C.baseChangeField k K) y.1)
          (tateRationalDifferentialMap k K C (C.baseChangeField k K)
            (pullback.fst (C ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            pullback.condition η)) =
      algebraMap k K (TateResidue.localRes (localSubalgebra k C x) η) := by
  sorry

end AlgebraicGeometry.Scheme
