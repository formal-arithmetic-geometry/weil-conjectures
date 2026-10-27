/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.FieldExtensionLimit

/-! # Clopen triviality locus for a doubly rigidified affine family

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 5.2,
proof of Claim 5.2.1, printed pp.12-13, smooth affine specialization
(blueprint: lem-sfb-birigidified-affine-triviality-locus).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- After a finite extension of the ground field, the residue-field fibre triviality locus
of an invertible module trivial on both rational-point axes is open and closed.

Source: Guo, Proposition 5.2, proof of Claim 5.2.1, printed pp.12-13
(blueprint: lem-sfb-birigidified-affine-triviality-locus).

Proof following the DAG:
1. Pass to an algebraic closure k of F. Smooth base change and composition, geometric
irreducibility of products, and smooth geometric normality show that X = U_k × V_k
and T_k are geometrically integral and normal. Finite type over a field gives local
Noetherianity. The projection X × T_k → T_k is flat, of finite type, with nonempty
integral fibres, and (u,v) gives a section (lem-pc-proper-base-change,
lem-trf-smooth-composition, lem-sc-geometrically-irreducible-product,
lem-trf-smooth-geometrically-normal, pqf-lem-locnoeth-lft, lem-pc-smooth-flat,
lem-sfb-finite-type-composition-base-change).
2. If there is no trivial fibre after any algebraically closed extension of k, the
original locus is empty, and K = F works. Otherwise choose such a fibre a and a common
algebraically closed extension of its field and the generic field Q of T_k. Over it,
a and the generic point b belong to the connected smooth separated parameter scheme.
Thus M_b is algebraically equivalent to M_a = O. The affine product algebraic-equivalence
lemma writes M_b as the exterior tensor product of two invertible modules
(lem-sfb-affine-product-algebraic-equivalence).
3. Restriction to the two axes makes both exterior factors trivial. Constant-variety
Picard detection descends this triviality from the common field to Q
(lem-sfb-constant-variety-picard-detection, lem-weil-pbc-invertible-pullback-tensor).
4. Generic-line pullback gives M_k as the pullback of an invertible module on T_k.
The section factors through a trivial axis, so that module, and hence M_k, is trivial
(lem-sfb-normal-noetherian-generic-line-pullback).
5. The algebraic closure is the directed union of finite intermediate extensions.
The spectra, and their products with U × V × T, form the corresponding inverse limit.
The stages are quasi-compact and quasi-separated with affine transition maps. Both M
and O are finitely presented. Descend the global trivialization and its inverse to
one finite extension K/F. Every residue-field fibre is then trivial, so the locus is
all of T_K (lem-kun-algebraic-subextensions-spec-limit,
lem-trf-fp-module-limit-isomorphism-descent, lem-weil-pbc-proper-fp-permanence).

The product is ((U ×_F V) ×_F T). After forming T_K, we base change its projection
to T along T_K → T; this is canonically U_K ×_K V_K ×_K T_K. The composite in the
set below maps its residue-field fibre back to the original product. Thus one tensor
pullback along this composite is exactly (M_K)_t, by tensor-pullback composition. -/
theorem exists_finite_extension_isClopen_birigidified_affine_triviality_locus
    {F : Type u} [Field F] (U V T : Over (Spec (.of F)))
    [IsAffine U.left] [IsAffine V.left]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [Smooth U.hom] [Smooth V.hom]
    [GeometricallyIntegral U.hom] [GeometricallyIntegral V.hom]
    [Smooth T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [GeometricallyIntegral T.hom]
    (u : 𝟙_ (Over (Spec (.of F))) ⟶ U) (v : 𝟙_ (Over (Spec (.of F))) ⟶ V)
    (M : ((U ⊗ V) ⊗ T).left.Modules) [M.IsInvertible]
    (hu : Nonempty
      ((Scheme.Modules.tensorPullback
        (lift (lift (toUnit (V ⊗ T) ≫ u) (fst V T)) (snd V T)).left).obj M ≅
        SheafOfModules.unit _))
    (hv : Nonempty
      ((Scheme.Modules.tensorPullback
        (lift (lift (fst U T) (toUnit (U ⊗ T) ≫ v)) (snd U T)).left).obj M ≅
        SheafOfModules.unit _)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K), Module.Finite F K ∧
      IsClopen {t : pullback (C := Scheme.{u}) T.hom
        (Spec.map (CommRingCat.ofHom (algebraMap F K))) |
        Nonempty
          ((Scheme.Modules.tensorPullback
            ((pullback.snd (snd (U ⊗ V) T).left
              (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap F K))))).fiberι t ≫
              pullback.fst (snd (U ⊗ V) T).left
                (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))))).obj M ≅
            SheafOfModules.unit _)} := by
  sorry

end AlgebraicGeometry
