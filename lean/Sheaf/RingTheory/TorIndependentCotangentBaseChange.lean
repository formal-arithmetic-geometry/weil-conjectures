/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.TraceFormula.OnePointDerivedRingIdentification
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit

/-!
# Polynomial resolutions under Tor-independent base change

Source: Stacks Project, cotangent.tex, Tags 08QP and 08QI
(blueprint: lem-trf-tor-independent-cotangent-base-change).

Ring pushouts are the tensor products of commutative algebras. The simplicial
pushout below retains the specified tensor augmentation, rather than choosing
an unrelated polynomial resolution of the tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wA wS

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Algebra.CotangentResolution

/-- The ring map `A' → B ⊗_A A'`, using the categorical tensor-product model.
Source: Stacks, Tag 08QP
(blueprint: lem-trf-tor-independent-cotangent-base-change). -/
def tensorBaseArrow (f : Arrow CommRingCat.{u}) {S : CommRingCat.{u}}
    (α : f.left ⟶ S) : Arrow CommRingCat.{u} :=
  Arrow.mk (pushout.inr f.hom α)

/-- Tensor the whole augmented simplicial algebra with `A'`. Colimits in a
functor category are pointwise, so its terms are exactly `P_n ⊗_A A'`.
The augmentation is induced by `ε ⊗ 1` through the pushout universal property.
Source: Stacks, Tag 08QP
(blueprint: lem-trf-tor-independent-cotangent-base-change). -/
def tensorAugmentation {f : Arrow CommRingCat.{u}} (P : Augmentation f)
    {S : CommRingCat.{u}} (α : f.left ⟶ S) : Augmentation (tensorBaseArrow f α) where
  algebra := pushout P.base ((SimplicialObject.const CommRingCat).map α)
  base := pushout.inr P.base ((SimplicialObject.const CommRingCat).map α)
  augmentation := pushout.desc
    (P.augmentation ≫ (SimplicialObject.const CommRingCat).map (pushout.inl f.hom α))
    ((SimplicialObject.const CommRingCat).map (pushout.inr f.hom α)) (by
      apply NatTrans.ext
      funext n
      obtain ⟨n⟩ := n
      obtain ⟨n⟩ := n
      change P.base.app (op ⦋n⦌) ≫
        (P.augmentation.app (op ⦋n⦌) ≫ pushout.inl f.hom α) =
          α ≫ pushout.inr f.hom α
      rw [← Category.assoc, P.triangle n, pushout.condition])
  triangle := by
    intro n
    change ((pushout.inr P.base ((SimplicialObject.const CommRingCat).map α)) ≫
      pushout.desc _ _ _).app (op ⦋n⦌) = _
    rw [pushout.inr_desc]
    rfl

/-- A polynomial resolution remains a polynomial resolution after Tor-independent
scalar extension, with its prescribed tensor augmentation. The pair `(L, ε)` is
any universal left derived pair for ordinary extension of scalars. By
lem-trf-one-point-derived-ring-identification this is exactly the transport of
lem-pur-derived-change-of-rings, with the same canonical counit; it is unique up
to the unique counit-compatible isomorphism. Thus `hTor` is the canonical
`B ⊗_A^L A' → (B ⊗_A A')[0]` comparison, not a chosen map.
Source: Stacks, cotangent.tex, Tags 08QP and 08QI
(blueprint: lem-trf-tor-independent-cotangent-base-change).

Proof: (1) The polynomial terms are free A-modules, by the monomial basis
of def-weil-pbc-mv-polynomial-ring and def-weil-pbc-module-tensor-product.
The alternating-face complex is zero in positive degrees and its augmentation
is a quasi-isomorphism by lem-trf-cotangent-resolution-coherence.
(2) Its terms are flat, so lem-pc-module-bounded-flat-kflat makes it K-flat,
in the sense of def-pc-module-kflat-complex.
(3) Polynomial scalar extension (lem-weil-pbc-polynomial-scalar-extension)
identifies each tensor term with the polynomial A'-algebra on the same
variables; tensoring the surjective augmentation remains surjective, by
right exactness of def-weil-module-base-change.
(4) Tensor commutes with the finite alternating sums of face maps. Hence
s(P tensor A') is s(P) tensor A', and its augmentation is the actual tensor
augmentation, including in degree zero.
(5) lem-trf-one-point-derived-ring-identification transports the universal
pair of lem-pur-derived-change-of-rings to ordinary modules; the natural
counit is that of lem-pur-left-derived-from-kflat-class.
(6) Let q : s(P) → B[0]. The K-flat counit theorem
lem-pc-kflat-scalar-extension-counit makes ε_s(P) invertible. Naturality says
L(Q(q)) followed by ε_B[0] equals ε_s(P) followed by Q(q tensor 1).
The left side is invertible by hTor and the quasi-isomorphism q; cancel the
K-flat counit. Thus q tensor 1 is a quasi-isomorphism. Together with (3),
this is precisely IsPolynomialResolution for the given tensor augmentation.
No flatness of the ring map or finiteness of the variable sets is required. -/
theorem isPolynomialResolution_tensor_of_torIndependent
    {f : Arrow CommRingCat.{u}} {S : CommRingCat.{u}} (α : f.left ⟶ S)
    (P : Augmentation f) (hP : IsPolynomialResolution P)
    [HasDerivedCategory.{wA} (ModuleCat.{u} f.left)]
    [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
    (L : DerivedCategory (ModuleCat.{u} f.left) ⥤ DerivedCategory (ModuleCat.{u} S))
    (ε : DerivedCategory.Q ⋙ L ⟶
      (ModuleCat.extendScalars α.hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (ModuleCat.{u} f.left) (.up ℤ)))
    (hTor : IsIso (ε.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} f.left) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars f.hom.hom).obj (ModuleCat.of f.right f.right))))) :
    IsPolynomialResolution (tensorAugmentation P α) := by
  sorry

end Algebra.CotangentResolution
