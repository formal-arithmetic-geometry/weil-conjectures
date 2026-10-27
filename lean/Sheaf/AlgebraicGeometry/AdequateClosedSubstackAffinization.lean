module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Mathlib.RingTheory.RingHom.Flat

/-! # Adequate affinization of a closed substack

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 5.2.11, printed p.510; Definition 3.3.1
(blueprint: lem-sfb-adequate-closed-substack-affinization).

The small quasi-coherent algebra is identified, naturally and over the structure sheaf,
with the existing direct-image section rings. The evaluation formula fixes the map to
relative Spec. The closed image retains its kernel ideal, including nilpotents.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w v' w'

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

namespace CategoryTheory

/-- The direct image of the structure sheaf of a closed substack is quasi-coherent.
Its relative spectrum is an adequate moduli space of that substack, and maps by a
universal homeomorphism to its closed scheme-theoretic image. The natural ring
isomorphisms `β` are the size transport of the same direct-image algebra, not a
replacement by unrelated algebra data. Their evaluation on every compatible scheme
chart specifies the canonical relative-Spec map `b`.
Source: Alper, Lemma 5.2.11, printed p.510; Definition 3.3.1
(blueprint: lem-sfb-adequate-closed-substack-affinization).

Proof:
1. Apply lem-sfb-disjoint-closed-substacks-algebra-quotient to Z and the empty closed
   substack. This gives the quasi-coherent quotient i_* O_Z of O_X. Its relative
   spectrum is Z, as follows on each scheme chart from Spec(D/J). Apply
   lem-sfb-adequate-relative-spectrum: its pushforward B is quasi-coherent and
   Z -> Spec_Y B is adequate. The section convention of
   def-sfb-stack-quasi-coherent-algebra identifies the pushforward with j_* O_Z.
   The adjunction evaluation gives exactly the displayed formula on every chart.
2. By lem-sfb-space-qcoh-affine-chart-calculus the kernel of O_Y -> B is
   quasi-coherent. By lem-sfb-space-closed-ideal-correspondence it cuts out W.
   The quotient O_Y/I injects into B, giving e by
   lem-sfb-space-relative-spec-correspondence. Composition is the structure map.
   Any closed factorization of j kills its ideal in B, so factors through W;
   thus W is the scheme-theoretic image, with precisely the stated kernel.
3. Over affine etale Spec R -> Y, use lem-sfb-adequate-moduli-etale-locality and
   lem-sfb-affine-target-adequacy-criterion. Polynomial algebras over R are free,
   hence flat by def-weil-pbc-flat-ring-map. Apply lem-sfb-stack-flat-scalar-sections
   and lem-sfb-adequately-affine-affine-target-base-change to the quotient above.
   Every polynomial over B has a positive power lifted from the polynomial ring
   over R, for every finite number of variables, including zero variables.
4. Put R_0 = R/ker(R -> B). The polynomial lifting descends to the injection
   R_0 -> B. By lem-sfb-polynomial-power-lifting-universal-homeomorphism every
   affine base change of Spec B -> Spec R_0 is a homeomorphism. The relative-Spec
   base-change formula identifies these with the base changes of e on this chart.
5. For a stack test T -> W_U choose a smooth surjective scheme atlas V -> T,
   a disjoint union of affines. Pull it back along e_U. The map V_E -> V is a
   homeomorphism. By lem-sfb-smooth-presentation-closed-subsets and
   lem-sfb-algebraic-stack-fibre-products the atlas maps are open surjections,
   their fibres are the classes of the relation, and points lift in 2-fibre
   products. Surjectivity descends from V_E -> V. For injectivity, lift two
   points to V_E and a relation point between their images to the base-changed
   relation. Singleton fibres over V force the lifted endpoints to be those
   two points, whose images in T_E therefore agree. Closedness follows by
   pulling a closed subset to V_E, transporting to V, and descending along
   the quotient atlas. Thus the canonical point map is a homeomorphism.
6. The W_U cover W etale-surjectively. Descend the universal homeomorphism by
   lem-sfb-stack-etale-local-qcqs-homeomorphism and apply it to every W' -> W.
   No reducedness or finiteness assumption occurs in any of these steps. -/
theorem adequate_closed_substack_affinization (k : Type u) [Field k]
    (X : BasedCategory.{v, w} (Over (Spec (.of k))))
    (Z : BasedCategory.{v', w'} (Over (Spec (.of k))))
    (hX : IsAlgebraicModuliStack X) (hZ : IsAlgebraicModuliStack Z)
    (Y : AlgebraicSpace (Spec (.of k)))
    (φ : BasedFunctor X (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace X hX Y φ)
    (i : BasedFunctor Z X) (hi : ModuliSchemeTest @IsClosedImmersion i) :
    ∃ (B : Y.QCAlg)
      (β : ∀ V : Y.EtaleSite, B.obj.right.obj.obj (op V) ≃+*
        (moduliDirectImage hZ.1.1 Y (i.comp φ)
          (moduliStructureSheaf Z hZ.1.1)).obj.obj (op V)),
      (∀ (V U : Y.EtaleSite) (a : V ⟶ U) (s : B.obj.right.obj.obj (op U)),
        β V (B.obj.right.obj.map a.op s) =
          (moduliDirectImage hZ.1.1 Y (i.comp φ)
            (moduliStructureSheaf Z hZ.1.1)).obj.map a.op (β U s)) ∧
      (∀ (V : Y.EtaleSite) (r : Y.commStructureSheaf.obj.obj (op V)),
        β V (B.obj.hom.hom.app (op V) r) =
          moduliStructureMapApp hZ.1.1 Y (i.comp φ) V r) ∧
      ∀ C : RelativeSpecData Y,
        ∃ (W : ClosedSubspace Y)
          (b : BasedFunctor Z (discreteModuli (C.relativeSpec B).obj.left.obj.obj))
          (e : (C.relativeSpec B).obj.left ⟶ (W.val : AlgebraicSpace (Spec (.of k))))
          (h : i.comp φ ≅ b.comp (discreteModuliMap (C.relativeSpec B).obj.hom.hom.hom)),
          IsAdequateModuliSpace Z hZ (C.relativeSpec B).obj.left b ∧
          e ≫ W.val.arrow = (C.relativeSpec B).obj.hom ∧
          (∀ (V : Y.EtaleSite) (r : Y.structureSheaf.obj.obj (op V)),
            (moduleStructureMap W.val.arrow).val.app (op V) r = 0 ↔
              B.obj.hom.hom.app (op V) r = 0) ∧
          (∀ (V : Y.EtaleSite) (q : ModuleChart (C.relativeSpec B).obj.hom V)
            (z : ModuliPushforwardIndex (C.relativeSpec B).obj.left b q.left)
            (s : B.obj.right.obj.obj (op V)),
            ((β V s).1 (op (CostructuredArrow.mk
              (h.hom.toNatTrans.app z.left ≫
                (discreteModuliMap (C.relativeSpec B).obj.hom.hom.hom).map z.hom ≫
                q.hom)))).down =
              (Scheme.Γ.map
                (moduliChartSchemeMap (C.relativeSpec B).obj.left b q.left z).op)
                ((C.directImage (C.relativeSpec B)).projection V q
                  ((C.counitAlgebra B).hom.right.hom.app (op V) s))) ∧
          (∀ (D : ClosedSubspace Y)
            (a : BasedFunctor Z (discreteModuli (D.val : AlgebraicSpace (Spec (.of k))).obj.obj)),
            Nonempty (i.comp φ ≅ a.comp (discreteModuliMap D.val.arrow.hom.hom)) →
              W.val ≤ D.val) ∧
          ∀ (W' : AlgebraicSpace (Spec (.of k)))
            (f : W' ⟶ (W.val : AlgebraicSpace (Spec (.of k)))),
            ∃ H : @Homeomorph
              (ModuliPoints (moduliTwoFiberProduct
                (discreteModuliMap e.hom.hom) (discreteModuliMap f.hom.hom)))
              (ModuliPoints (discreteModuli W'.obj.obj))
              (moduliSmoothPointTopology (moduliTwoFiberProduct
                (discreteModuliMap e.hom.hom) (discreteModuliMap f.hom.hom)))
              (moduliSmoothPointTopology (discreteModuli W'.obj.obj)),
              ∀ x, H x = moduliPointMap
                (moduliTwoFiberSnd (discreteModuliMap e.hom.hom)
                  (discreteModuliMap f.hom.hom)) x := by
  sorry

end CategoryTheory
