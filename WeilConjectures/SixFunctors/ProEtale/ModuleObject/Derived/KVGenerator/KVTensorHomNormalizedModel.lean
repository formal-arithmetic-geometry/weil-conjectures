/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps

/-! # Tensor-Hom exchange for a supplied compactification and exceptional adjunction

Source: sk-thm-sf-tensor-hom, first exchange and its evaluation normalization;
sk-thm-sf-kunneth-verdier.proof.md, generator calculation, step 1.
(blueprint: lem-sf-kv-tensor-hom-normalized-model).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator
open CompactificationReindexing RelativeKunneth ProductComparisons

/-- The tensor-Hom exchange uses exactly the supplied projection and both supplied
counits, for every compactification model and constructible exceptional adjunction.
Source: sk-thm-sf-tensor-hom, (11.1) and evaluation compatibility;
sk-thm-sf-kunneth-verdier.proof.md, generator calculation, step 1
(blueprint: lem-sf-kv-tensor-hom-normalized-model).

Proof in words:
1. Use H.ell, its primality and characteristic inequalities, its finite-or-algebraically
closed base, and its coefficient admissibility to apply the first tensor-Hom exchange.
The base-field cohomological-dimension theorem supplies the finite-cd hypothesis.
2. The fixed compactification and the theorem's chosen compactification have the
canonical common-refinement comparison of compact-support functors. It preserves the
projection transformation, because that transformation is the pasted proper/open
projection transformation and refinements preserve its ordinary counits.
3. Transport the exceptional adjunction along this lower-functor comparison. Uniqueness
of right adjoints on the established localizing categories identifies it with S.right,
with the counit equation. Restriction to the full constructible finite-Tor categories
retains this equation; no ambient exceptional right adjoint is assumed.
4. Uncurry the first exchange, then take the ordinary adjunction transpose. Evaluation
compatibility in tensor-Hom identifies its value with projection, ordinary counit,
internal-Hom evaluation and exceptional counit, in precisely the displayed order.
Naturality and the counit equation from step 3 transport this equality to c and S.
5. Both transposes are injective. Thus this displayed curry is the transported
evaluation-normalized exchange component. The exchange and all transport maps are invertible,
so the displayed morphism is invertible. Empty schemes and zero objects satisfy the
same adjunction identities. -/
theorem tensorHom_exchange_isIso (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (H : CanonicalCompositionData Λ.X k)
    (X Y : SepFinType k) (f : X ⟶ Y) (c : Compactification f.hom.left)
    (S : SixOperationsLocalizingAdjunction Λ.X c)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :
    IsIso (MonoidalClosed.curry
      (pf Λ.X c K.obj _ ≫
        (F Λ.X c).map
          ((K.obj ◁ (derivedUpperStarLowerStarAdjunction Λ.X f.hom.left).counit.app _) ≫
            (ihom.ev K.obj).app ((exceptional Λ S).obj L).obj) ≫
        ((adjunction Λ S).counit.app L).hom)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator
