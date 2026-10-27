module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Defs.Filter
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Compatible opens exhaust after a finite extension

Source: Milne, Algebraic Groups (iAG2017), Appendix B, Lemma B.36, printed p.604
(blueprint: lem-sfb-finite-extension-open-exhaustion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- A compatible family of opens containing all rational points over finite intermediate
extensions exhausts a finite-type scheme at some finite extension.

Source: Milne, Algebraic Groups (iAG2017), Appendix B, Lemma B.36, printed p.604
(blueprint: lem-sfb-finite-extension-open-exhaustion).

Proof (the node's alternative algebraic-closure argument):
1. Pull every open back to `Z_Ω`, obtaining opens `W_K`. Finite-type base change makes
   `Z_Ω` quasi-compact (lem-sfb-finite-type-composition-base-change).
2. Every closed point of `Z_Ω` is Ω-rational by
   lem-weil-pbc-closed-point-residue-field-base. Compose its section with `Z_Ω → Z`.
3. In a finite-type affine neighbourhood, the finitely many coordinates of this map
   generate a finite intermediate field K, by
   lem-weil-pbc-algebraic-generators-finite-extension. Factoring the coordinate map
   through K gives a K-rational point of `Z_K`. Its image lies in `U K`, so the original
   closed point lies in `W_K` (def-pc-fibre-product, def-pc-rational-point).
4. The closed complement of the union of the `W_K` contains no closed points. It is empty
   by lem-sc-lft-over-field-jacobson-space, so the `W_K` cover `Z_Ω`.
5. Choose a finite subcover. Adjoin the union of finite k-bases of its fields to k to
   obtain a finite common extension L (lem-weil-pbc-algebraic-generators-finite-extension).
   Compatibility puts the whole subcover inside `W_L`, hence `W_L = Z_Ω`. If the subcover
   is empty, take L = k; the same conclusion holds.
6. The map `Z_Ω → Z_L` is surjective by lem-pc-field-extension-surjective and
   lem-weil-pbc-surjective-base-change. Its inverse image of `U L` is all of `Z_Ω`,
   so `U L` is all of `Z_L`.
-/
theorem exists_finiteExtension_open_eq_top
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Z : Scheme.{u}) (f : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (U : (K : {K : IntermediateField k Ω // FiniteDimensional k K}) →
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K.val)))).Opens)
    (hpoints : ∀ (K : {K : IntermediateField k Ω // FiniteDimensional k K})
      (p : (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap k K.val)))).fieldPoints K.val),
      p.val.base default ∈ U K)
    (hmono : ∀ (K L : {K : IntermediateField k Ω // FiniteDimensional k K})
      (h : K.val ≤ L.val),
      (baseChangeMap f
        (Over.homMk
          (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L.val))))
          (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K.val))))
          (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
          (by
            change Spec.map _ ≫ Spec.map _ = Spec.map _
            rw [← Spec.map_comp]
            congr 1))) ⁻¹ᵁ U K ≤ U L) :
    ∃ K : {K : IntermediateField k Ω // FiniteDimensional k K}, U K = ⊤ := by
  sorry

end AlgebraicGeometry
