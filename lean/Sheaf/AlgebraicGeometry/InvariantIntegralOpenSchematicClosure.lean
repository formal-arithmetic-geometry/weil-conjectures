/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks

/-!
# The schematic closure of an invariant integral open

Source: Stacks Project, Morphisms, Tags 056B, 01R8, 01RV and 01RW; the equivariant
factorization argument in the DAG proof
(blueprint: lem-sfb-invariant-integral-open-schematic-closure).

The closure and its factor map are the canonical `j.image` and `j.toImage`.
Ideal preservation is expressed on every open by transport of the kernel of the
closed immersion's section map. The function-field equivalence is required to
be the actual generic stalk map, transported along the equality of generic points.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The schematic closure of the invariant integral common open is integral, inherits
uniquely the action on its ambient Noetherian scheme, and has the same function field
via the actual stalk map. Source: Stacks Project, Morphisms, Tags 056B, 01R8, 01RV,
01RW; translated closed-factor action descent as in the node's proof.
(blueprint: lem-sfb-invariant-integral-open-schematic-closure)

Proof plan:
1. Put W = r⁻¹(U). The inverse of r restricted to U identifies U with W and defines
   j. Density in the integral X makes U nonempty and integral. Every open of the
   Noetherian P is quasi-compact (lem-weil-pbc-noetherian-open-subscheme-noetherian),
   so j is quasi-compact, including on preimages of affine opens of P.
2. By def-nagata-scheme-theoretic-image its ideal is the ordinary sheaf kernel.
   Apply lem-trf-reduced-scheme-image (056B): j.image is the reduced closed scheme
   on the closure of j(U). The closure of a nonempty irreducible space is nonempty
   and irreducible, hence this scheme is integral. The canonical factor j.toImage
   is a dense open immersion by lemma-nagata-immersion-open-in-scheme-image.
3. Set c = j.imageι and q = c followed by r. Then q followed after j.toImage is
   the inclusion of U in X. Since c is injective and c composed with j.toImage is
   j, q⁻¹(U) is precisely the image of j.toImage. Thus q restricted to U is an
   isomorphism inverse to this open identification.
4. Invariance of U and equivariance of r imply A_h j = j u_h. The closed immersion
   c_h = c followed by A_(h⁻¹) is a closed factor of j, with factor u_h followed by
   j.toImage. The minimal closed-factor property
   (lemma-nagata-scheme-image-universal, 01R6) supplies v_h with c_h v_h = c,
   equivalently c v_h = A_h c.
5. Cancel the monomorphism c to prove the identity, multiplication and inverse
   laws for v_h, and uniqueness of these lifts. Composing with r and f proves
   both equivariance assertions. The same square on section rings identifies
   the kernel ideals under A_h's isomorphism on sections, on every open of P
   (def-sbc-closed-immersion-ideal-sheaf).
6. Scheme sobriety (lem-sc-scheme-sober) gives unique generic points. The generic
   point of U maps to the generic points of both X and j.image: its closure
   contains the dense open in each. Evaluating q j.toImage = U.ι gives q(η_T)=η_X.
7. Both dense open immersions induce stalk isomorphisms at the generic point of U.
   Functoriality of stalk maps makes q's actual stalk map their quotient, hence
   an isomorphism. The generic stalks are fields by
   lem-sc-rational-functions-generic-stalks (01RV), and are the function fields by
   def-sc-function-field (01RW). This yields the specified ring equivalence.
-/
theorem invariant_integral_open_schematic_closure
    (k : Type u) [Field k] (X P : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian P] [CompactSpace P]
    (r : P ⟶ X) (H : Type v) [Group H] [Finite H]
    (rho : H →* (k ≃+* k)) (a : H →* Aut X) (A : H →* Aut P)
    (b : H →* Aut (Spec (.of k)))
    (hb : ∀ h : H, (b h).hom = Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom))
    (hf : ∀ h : H, (a h).hom ≫ f = f ≫ (b h).hom)
    (hr : ∀ h : H, (A h).hom ≫ r = r ≫ (a h).hom)
    (U : X.Opens) (hU : Dense (U : Set X))
    (hUinv : ∀ h : H, (a h).hom ⁻¹ᵁ U = U) [IsIso (r ∣_ U)]
    (j : U.toScheme ⟶ P) (hj : j = inv (r ∣_ U) ≫ (r ⁻¹ᵁ U).ι) :
    j.ker = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.mk (closure (Set.range j)) isClosed_closure) ∧
      Set.range j.imageι = closure (Set.range j) ∧
      IsReduced j.image ∧ Nonempty j.image ∧ IrreducibleSpace j.image ∧
      ∃ (_ : IsIntegral j.image),
        IsOpenImmersion j.toImage ∧ DenseRange j.toImage ∧
        IsIso ((j.imageι ≫ r) ∣_ U) ∧
        (∀ (h : H) (V : P.Opens),
          Ideal.map ((A h).hom.app V).hom (RingHom.ker (j.imageι.app V).hom) =
            RingHom.ker (j.imageι.app ((A h).hom ⁻¹ᵁ V)).hom) ∧
        (∃ aT : H →* Aut j.image,
          (∀ h : H, (aT h).hom ≫ j.imageι = j.imageι ≫ (A h).hom) ∧
          (∀ aT' : H →* Aut j.image,
            (∀ h : H, (aT' h).hom ≫ j.imageι = j.imageι ≫ (A h).hom) → aT' = aT) ∧
          (∀ h : H, (aT h).hom ≫ (j.imageι ≫ r) = (j.imageι ≫ r) ≫ (a h).hom) ∧
          (∀ h : H, (aT h).hom ≫ (j.imageι ≫ r ≫ f) =
            (j.imageι ≫ r ≫ f) ≫ (b h).hom)) ∧
        ∃ hη : (j.imageι ≫ r) (genericPoint j.image) = genericPoint X,
          IsIso ((j.imageι ≫ r).stalkMap (genericPoint j.image)) ∧
          ∃ e : X.functionField ≃+* j.image.functionField,
            e.toRingHom =
              (X.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
                (j.imageι ≫ r).stalkMap (genericPoint j.image)).hom := by
  sorry

end AlgebraicGeometry
