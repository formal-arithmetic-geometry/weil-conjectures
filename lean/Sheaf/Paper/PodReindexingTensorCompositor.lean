/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Tensor normalization of the reindexing composition

Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI.
(blueprint: lem-pod-reindexing-tensor-compositor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical site and localized tensor composition comparison.
Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI
(blueprint: lem-pod-reindexing-tensor-compositor).

Proof: For a module M and a pro-etale object U of Z, define the ordinary comparison by the
restriction of M along (siteComp g h).inv.app U. Define its inverse using siteComp.hom. The two
composites are identities by functoriality of restriction and the site isomorphism identities.
These section maps commute with restriction by naturality of siteComp. They are linear: the
coefficient restriction along this site map is the identity on the finite-stage constant
coefficients; at the completed stage the same assertion holds after every quotient projection,
which jointly detect equality. Thus these maps assemble to the ordinary natural module isomorphism
and give the required sections field.

For each cochain complex P use this ordinary comparison in degree i. Naturality with respect to
P.d proves commutation with the differential. The degree field is then the defining equation, and
naturality in chain maps is inherited degreewise. Both exact reindexing functors invert quasi-
isomorphisms. Descend this natural chain isomorphism through the localization functor. Whiskering
with the localization is fully faithful, so the descended isomorphism has exactly the model
equation with the three recorded podReindexingDerivedFactors. This constructs every field of
Compositor, without choosing an arbitrary natural isomorphism.

First prove the tensor square on the actual total complexes. In the summand of bidegree (p,q),
both routes send a pure section x tensor y over U to the tensor of their restrictions along
siteComp.inv.app U. This uses the tensorChain_pure fields of cg, ch and cgh; there is no
interchange of degrees and hence no sign. The sheafified pure generators and total-summand
inclusions detect equality, so the chain square follows. Reindexing along a scheme isomorphism
preserves K-flat complexes: use the inverse exact reindexing equivalence to transport an acyclic
tensor test, and the normalized tensorChain isomorphism to identify its tensor. Apply the three
tensor_model equations to independently K-flat representatives P,Q. Substitute the chain square
and the compositor model equation, and cancel the comparison isomorphisms. This proves the
displayed derived tensor square on Q(P),Q(Q). Finally take independent K-flat resolutions of
arbitrary M,N; naturality of the tensor comparisons and compositor transports that square across
their invertible augmentations. No Hom equation is assumed or asserted here.
-/
theorem tensor_compositor_exists {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    [EssentiallySmall.{u + 1} Z.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s) (SZ : Closed l E Z s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) (TZ : Models l E Z s SZ)
    (cg : Comparison l E g s SX SY TX TY) (ch : Comparison l E h s SZ SX TZ TX)
    (cgh : Comparison l E (h ≫ g) s SZ SY TZ TY) :
    ∃ k : Compositor l E g h s,
      (∀ M N : podReindexingDerived l E Y s,
        cgh.tensor.hom.app (M, N) ≫ SZ.tensor.map
          (Prod.mkHom (k.derived.hom.app M) (k.derived.hom.app N)) =
        k.derived.hom.app (SY.tensor.obj (M, N)) ≫
          (podReindexingDerivedFunctor l E h s).map (cg.tensor.hom.app (M, N)) ≫
          ch.tensor.hom.app ((podReindexingDerivedFunctor l E g s).obj M,
            (podReindexingDerivedFunctor l E g s).obj N)) := by
  sorry

end WeilConjectures.PodReindexingCoherence
