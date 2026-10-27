module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-! # Adequate affinization after arbitrary base change

Source: Alper, Adequate moduli spaces, Proposition 5.2.9(3), printed p.509
(blueprint: lem-sfb-adequate-base-change-affinization).

The chart ring equivalences express the direct image in the coefficient universe used
by relative Spec. Their restriction and structure equations retain the actual algebra.
The final section equation specifies the canonical factorization, on all scheme tests.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The actual 2-base change, with no restriction on the map of spaces.
Source: Alper, Proposition 5.2.9(3)
(blueprint: lem-sfb-adequate-base-change-affinization). -/
abbrev adequateBaseChangeCategory {k : Type u} [Field k]
    {F : BasedCategory.{v, w} (Over (Spec (.of k)))}
    {Y T : AlgebraicSpace (Spec (.of k))}
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (g : T ⟶ Y) :=
  moduliTwoFiberProduct φ (discreteModuliMap g.hom.hom)

/-- The projection of the actual 2-base change to the new base space.
Source: Alper, Proposition 5.2.9(3)
(blueprint: lem-sfb-adequate-base-change-affinization). -/
abbrev adequateBaseChangeProjection {k : Type u} [Field k]
    {F : BasedCategory.{v, w} (Over (Spec (.of k)))}
    {Y T : AlgebraicSpace (Spec (.of k))}
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (g : T ⟶ Y) :=
  moduliTwoFiberSnd φ (discreteModuliMap g.hom.hom)

/-- Arbitrary base change has quasi-coherent direct-image structure algebra and its
canonical relative-Spec factorization is adequate, followed by a universal homeomorphism.
The equivalences `e` commute with restriction and the structural ring maps; the equation
on `i`, `r`, and `b` says that pullback through `a` is evaluation of that same section.
This removes any freedom to replace the canonical affinization map by another factorization.
Source: Alper, Proposition 5.2.9(3), Remark 5.1.2 and Definition 3.3.1
(blueprint: lem-sfb-adequate-base-change-affinization).

Proof:
1. The algebraic-stack fibre-product lemma gives algebraicity of the 2-base change.
   Quasi-compactness and quasi-separatedness survive arbitrary base change by
   lem-sfb-stack-etale-local-qcqs-homeomorphism. Apply
   lem-sfb-stack-qcqs-algebra-direct-image to the structure algebra. The relative-Spec
   correspondence supplies its affine spectrum, with the specified chart ring maps.
2. Choose affine etale charts of Y, then affine etale charts of their pullbacks to T,
   using lem-a1-space-affine-etale-cover and lem-trf-space-fibre-products-etale-covers.
   By lem-sfb-adequate-moduli-etale-locality and lem-sfb-affine-target-adequacy-criterion,
   the original map on each chart is adequately affine. Apply
   lem-sfb-adequately-affine-affine-target-base-change to get the power-lifting criterion
   on each resulting chart W of T, for all quasi-coherent algebra surjections.
3. By lem-sfb-stack-qcqs-composition-affine the stack over W is qcqs over k. Apply
   lem-sfb-stack-affinization-qcqs to get its canonical map to Spec Gamma(O).
   Its composite to W is the original projection, by
   lem-weil-pbc-morphism-into-affine-scheme and equality on regular functions.
4. On affine etale refinements of overlaps, restriction of compatible functions makes
   these maps agree on every scheme object, by the same affine-target correspondence.
   The algebraic-space sheaf condition glues them uniquely, giving a over T. This
   proves the displayed normalization equation as well as the factorization.
5. The local map is qcqs, power lifting holds, and its structure map on functions is
   the identity. The affine criterion in lem-sfb-adequate-moduli-etale-locality makes
   it adequate. Establish qcqs for a by target locality first, then descend adequacy
   on the etale cover of its target with the same lemma.
6. By lem-sfb-stack-affine-algebra-direct-image the ring on W = Spec C is
   Gamma(X_i, O tensor_R C), and its structural map sends c to 1 tensor c.
   Apply lem-sfb-adequate-algebra-unit-power-kernel: every extension C' has nilpotent
   kernel and all target elements have positive powers in the image. By
   lem-pur-all-element-powers-spectrum-homeomorphism its spectrum is a homeomorphism.
7. Relative-Spec base change gives this homeomorphism over every affine scheme test.
   For a stack test choose a smooth atlas, refined by affine schemes. The point-space
   fibre-product surjectivity and relation description in
   lem-sfb-smooth-presentation-closed-subsets show the induced map is bijective.
   A closed subset pulls back to a closed subset on the atlas; the chart homeomorphism
   makes its image closed there, hence closed in the quotient topology. Thus the
   continuous map is a homeomorphism on every test.
8. Descend universal homeomorphism along the etale cover of T by
   lem-sfb-stack-etale-local-qcqs-homeomorphism. In particular this gives every
   algebraic-space base change asserted below. No flatness or finiteness was used. -/
theorem adequate_base_change_affinization {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (Y T : AlgebraicSpace (Spec (.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ) (g : T ⟶ Y) :
    ∃ (hFT : IsAlgebraicModuliStack (adequateBaseChangeCategory φ g))
      (B : T.QCAlg)
      (e : ∀ W : T.EtaleSite, B.obj.right.obj.obj (op W) ≃+*
        (moduliDirectImage hFT.1.1 T (adequateBaseChangeProjection φ g)
          (moduliStructureSheaf (adequateBaseChangeCategory φ g) hFT.1.1)).obj.obj (op W)),
      (∀ (W V : T.EtaleSite) (j : W ⟶ V) (s : B.obj.right.obj.obj (op V)),
        e W (B.obj.right.obj.map j.op s) =
          (moduliDirectImage hFT.1.1 T (adequateBaseChangeProjection φ g)
            (moduliStructureSheaf (adequateBaseChangeCategory φ g) hFT.1.1)).obj.map j.op
              (e V s)) ∧
      (∀ (W : T.EtaleSite) (s : Scheme.Γ.obj (op (T.etaleForget.obj W))),
        e W (B.obj.hom.hom.app (op W) s) =
          moduliStructureMapApp hFT.1.1 T (adequateBaseChangeProjection φ g) W s) ∧
      ∃ (C : RelativeSpecData T), C.HasChartFormula ∧
        ∃ a : BasedFunctor (adequateBaseChangeCategory φ g)
            (discreteModuli (C.relativeSpec B).obj.left.obj.obj),
          Nonempty (ModuliTwoIso
            (a.comp (discreteModuliMap (C.relativeSpec B).obj.hom.hom.hom))
            (adequateBaseChangeProjection φ g)) ∧
          IsAdequateModuliSpace (adequateBaseChangeCategory φ g) hFT
            (C.relativeSpec B).obj.left a ∧
          (∀ (T' : AlgebraicSpace (Spec (.of k))) (t : T' ⟶ T),
            @IsHomeomorph _ _
              (moduliSmoothPointTopology (moduliTwoFiberProduct
                (discreteModuliMap (C.relativeSpec B).obj.hom.hom.hom)
                (discreteModuliMap t.hom.hom)))
              (moduliSmoothPointTopology (discreteModuli T'.obj.obj))
              (moduliPointMap (moduliTwoFiberSnd
                (discreteModuliMap (C.relativeSpec B).obj.hom.hom.hom)
                (discreteModuliMap t.hom.hom)))) ∧
          ∀ (W : T.EtaleSite) (q : ModuleChart (C.relativeSpec B).obj.hom W)
            (i : ModuliPushforwardIndex T (adequateBaseChangeProjection φ g) W)
            (r : ModuliPushforwardIndex (C.relativeSpec B).obj.left a q.left)
            (b : i.left ⟶ r.left),
            (moduliSchemeForget (adequateBaseChangeCategory φ g)).map b ≫
                moduliChartSchemeMap (C.relativeSpec B).obj.left a q.left r ≫
                q.hom.left.left =
              moduliChartSchemeMap T (adequateBaseChangeProjection φ g) W i →
            ∀ s : B.obj.right.obj.obj (op W),
              (e W s).1 (op i) = ULift.up
                ((Scheme.Γ.map
                  ((moduliSchemeForget (adequateBaseChangeCategory φ g)).map b ≫
                    moduliChartSchemeMap (C.relativeSpec B).obj.left a q.left r).op)
                  (((C.directImage (C.relativeSpec B)).projection W q)
                    (((C.counitAlgebra B).hom.right.hom.app (op W)) s))) := by
  sorry

end CategoryTheory
