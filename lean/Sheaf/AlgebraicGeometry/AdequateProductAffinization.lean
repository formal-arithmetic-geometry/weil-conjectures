module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism

/-! # Adequate affinization of a product stack

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, Theorem 8.3.2, proof of (3) implies (1), pp.39--40;
Proposition 4.2.1(1),(6), Lemma 4.2.3 and Remark 5.1.2
(blueprint: lem-sfb-adequate-product-affinization).

The section ring is a compatible-family ring in a larger universe. A small ring `B`
is identified with that ring by `e`; this is a presentation of the same ring, not a
smallness hypothesis. The affinization is specified on every scheme object by the
pullback of each function. The theorem supplies both this map and its adequacy.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The self-product over the base is the existing 2-fibre product of structural maps.
Source: Alper, arXiv:1005.2398v3, Theorem 8.3.2, product construction
(blueprint: lem-sfb-adequate-product-affinization). -/
abbrev moduliSelfProduct {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) :=
  moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F)

/-- Evaluate a map to a representable stack on a scheme object. The equality transport
comes from the based functor's projection equality; the map is the Yoneda preimage.
Source: Alper, arXiv:1005.2398v3, Remark 5.1.2, canonical relative-Spec map
(blueprint: lem-sfb-adequate-product-affinization). -/
def moduliRepresentableSchemeMap {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {Z : Over S}
    (ψ : BasedFunctor F (discreteModuli (yoneda.obj Z))) (x : F.obj) :
    (moduliSchemeForget F).obj x ⟶ Z.left :=
  eqToHom (congrArg (fun T : Over S ↦ T.left) (ψ.w_obj x)).symm ≫
    (yoneda.preimage (ψ.obj x).hom).left

/-- The canonical affinization of the self-product of a finite-type algebraic stack
with an affine adequate moduli space is adequate. The small presentation `B` of its
actual global-function ring is supplied in the conclusion. For every scheme object
`x`, the displayed equality identifies the pullback of `b` with evaluation of `e b`.
It therefore characterizes the canonical affinization, including its restrictions
on smooth affine charts. There is no condition on the diagonal.

Source: Alper, arXiv:1005.2398v3, Theorem 8.3.2, proof of (3) implies (1), pp.39--40;
Proposition 4.2.1(1),(6), Lemma 4.2.3, Definition 5.1.1 and Remark 5.1.2
(blueprint: lem-sfb-adequate-product-affinization).

Proof:
1. The identity affine etale chart of the adequate moduli space gives global power
   lifting. The affine-target adequacy criterion makes the given map adequately
   affine. The structural map to Spec k is then adequately affine, by composition
   with the affine structural map of the affine target.
2. Base change that structural map by itself. Algebraic-stack fibre products show
   that the self-product is algebraic; adequate affineness is preserved by this
   base change over the affine scheme Spec k, without a diagonal hypothesis.
3. Compose its second projection with the structural map. Composition of adequately
   affine morphisms gives a qcqs adequately affine structural map of the product.
   The affine-target criterion supplies global positive-power lifting.
4. Stack affinization for a qcqs stack supplies the canonical map to Spec of global
   functions; the ring has a small presentation by descent along a qc scheme atlas.
   Its map on global functions is the identity, and it is qcqs. The global
   power-lifting adequacy criterion therefore proves this affinization adequate.
-/
theorem adequate_product_affinization (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k)))) (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom)
    (Y : Over (Spec (.of k))) [IsAffine Y.left]
    (φ : BasedFunctor F (discreteModuli (yoneda.obj Y)))
    (hφ : IsAdequateModuliSpace F hF (AlgebraicSpace.schemeSpace Y) φ) :
    ∃ (hW : IsAlgebraicModuliStack (moduliSelfProduct F)) (B : CommRingCat.{u})
      (e : B ≃+* moduliGlobalSectionsRing
        (moduliStructureSheaf (moduliSelfProduct F) hW.1.1))
      (q : Spec B ⟶ Spec (.of k))
      (ψ : BasedFunctor (moduliSelfProduct F) (discreteModuli (yoneda.obj (Over.mk q)))),
      (∀ (x : (moduliSelfProduct F).obj) (b : B),
        (((Scheme.ΓSpecIso B).inv ≫
          Scheme.Γ.map (moduliRepresentableSchemeMap ψ x).op).hom b) =
            ((e b).1 (op x)).down) ∧
      IsAdequateModuliSpace (moduliSelfProduct F) hW
        (AlgebraicSpace.schemeSpace (Over.mk q)) ψ := by
  sorry

end CategoryTheory
