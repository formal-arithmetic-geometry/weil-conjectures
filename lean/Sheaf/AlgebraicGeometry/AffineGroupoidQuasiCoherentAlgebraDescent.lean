module

public import Sheaf.AlgebraicGeometry.AffineGroupoidAlgebra
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Algebra descent and invariant sections for a finite flat affine groupoid

Source: Stacks Project, stacks-sheaves.tex, Tags 06WT and 06WV(1);
Alper, arXiv:1005.2398v3, Proposition 8.2.1, first two paragraphs
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent).

The equivalence is normalized on the atlas, including its transport along the specified
arrow two-isomorphism. Hence its forward functor is the canonical pullback, up to the
specified natural isomorphism. All algebras in the common ambient universe are allowed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- All quasi-coherent algebra sheaves, with all algebra-sheaf morphisms.
Source: Stacks Tag 06WT
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent). -/
abbrev GroupoidQuasiCoherentAlgebras {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :=
  ObjectProperty.FullSubcategory
    (IsQuasicoherentModuliAlgebra (F := F) (hF := hF))

/-- The canonical comparison between chart coordinates and the structure sheaf value.
It only transports the equality of underlying schemes of a based functor.
Source: Stacks Tags 06TV and 06WT
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent). -/
def groupoidChartCoordinateComparison {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    {T : Over S} (x : yoneda.obj T ⟶ yoneda.obj U) :
    Scheme.groupoidAlgebraCoordinates.{u, max (u + 1) v w} T.left ⟶
      (moduliStructurePresheaf F).obj (op (a.obj (CostructuredArrow.mk x))) :=
  eqToHom (congrArg
    (fun Q : Over S ↦ Scheme.groupoidAlgebraCoordinates.{u, max (u + 1) v w} Q.left)
    (Functor.congr_obj a.w (CostructuredArrow.mk x)).symm)

/-- The chart arrow over a scheme map, before applying the algebra presheaf.
Source: Stacks Tag 06WT
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent). -/
def groupoidChartRestriction {S : Scheme.{u}} {U T : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) (f : T ⟶ U) :
    a.obj (CostructuredArrow.mk (yoneda.map f)) ⟶
      a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U))) :=
  a.map (CostructuredArrow.homMk f (by simp))

/-- Restrict to the atlas and take its coordinate algebra; maps are evaluated literally.
Source: Stacks Tag 06WT
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent). -/
def groupoidAtlasAlgebraEvaluation {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) :
    GroupoidQuasiCoherentAlgebras F hF ⥤
      Under (Scheme.groupoidAlgebraCoordinates.{u, max (u + 1) v w} U.left) where
  obj A := Under.mk (groupoidChartCoordinateComparison a (𝟙 (yoneda.obj U)) ≫
    A.obj.hom.hom.app (op (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U))))))
  map f := Under.homMk
    (f.hom.right.hom.app (op (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U))))))
    (by
      have h := congrArg
        (fun α ↦ α.hom.app (op (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U))))))
        (Under.w f.hom)
      simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        Under.mk_hom, Category.assoc] using
        congrArg (fun g ↦ groupoidChartCoordinateComparison a (𝟙 (yoneda.obj U)) ≫ g) h)
  map_id A := by apply Under.UnderMorphism.ext; rfl
  map_comp f g := by apply Under.UnderMorphism.ext; rfl

/-- The inverse presentation arrow has the exact source-to-target presheaf endpoints.
Source: Stacks Tag 06WT
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent). -/
def groupoidPresentationAlgebraTransport {S : Scheme.{u}} {U R : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (s t : R ⟶ U) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (eta : ModuliTwoIso ((discreteModuliMap (yoneda.map s)).comp a)
      ((discreteModuliMap (yoneda.map t)).comp a)) :
    a.obj (CostructuredArrow.mk (yoneda.map t)) ⟶
      a.obj (CostructuredArrow.mk (yoneda.map s)) := by
  have h := eta.val.inv.app (CostructuredArrow.mk (𝟙 (yoneda.obj R)))
  change a.obj ((CostructuredArrow.map (yoneda.map t)).obj
    (CostructuredArrow.mk (𝟙 (yoneda.obj R)))) ⟶
      a.obj ((CostructuredArrow.map (yoneda.map s)).obj
        (CostructuredArrow.mk (𝟙 (yoneda.obj R)))) at h
  simpa only [CostructuredArrow.map_mk, Category.id_comp] using h

/-- Pullback is an equivalence on arbitrary commutative quasi-coherent algebras,
identifies global sections with invariants, and sends local surjections to surjective
coordinate-algebra maps. The comparison `j` is normalized on the atlas and the three
formulas for `theta` specify the transport, including its direction. Source: Stacks
Tags 06WT, 06WV(1); Alper Proposition 8.2.1
(blueprint: lem-sfb-affine-groupoid-quasicoherent-algebra-descent).

Proof:
1. Apply lem-sfb-groupoid-module-descent-tensor-cokernel to this exact fppf presentation.
   It is fully faithful and essentially surjective on modules and preserves the structure
   module, tensor products, and cokernels. Invert the convention of Stacks 06WT to get
   the forward transport from source to target.
2. By lem-weil-pbc-affine-tilde-gamma-adjunction identify modules on Spec E with E-modules.
   The natural pullback-section maps of lem-weil-pbc-module-pullback-affine-sections and
   the tensor-section maps of lem-weil-pbc-quasi-coherent-tensor-product-affine-sections
   identify the pullback algebras with the two ring pushouts used here.
3. Descend multiplication and unit by fullness. Faithfulness proves associativity,
   the two unit laws, and commutativity from the corresponding equations on the atlas.
   The identity and composition equations are exactly the equations on all ring-valued
   points defining AffineGroupoidAlgebra. The three theta formulas follow from the
   pullback maps and the arrow two-isomorphism of the quotient presentation.
4. Fullness descends every compatible algebra map. Faithfulness checks products and
   units, and also identities and composition. The module-descent unit and counit are
   algebra isomorphisms by the same argument, giving the equivalence and its natural
   atlas comparison j.
5. A global section is a module map from the structure module, by evaluation at 1.
   Full faithfulness and the affine adjunction identify these with elements of the
   atlas algebra for which beta(a tensor 1)=a tensor 1. Operations restrict pointwise,
   giving the stated ring isomorphism rho, normalized by evaluation on the atlas.
6. A locally surjective sheaf-algebra map has zero module cokernel. Module descent
   identifies its cokernel on U with zero. The affine-section calculation of
   lem-weil-pbc-quasi-coherent-module-cokernel-image says that the quotient of the target
   algebra by the image is zero, proving surjectivity. Equivariance is built into the
   morphisms of AffineGroupoidAlgebra. None of these steps uses finite generation. -/
theorem affineGroupoid_quasiCoherent_algebra_descent
    (k E L : Type u) [Field k] [CommRing E] [CommRing L]
    [Algebra k E] [Algebra k L] (sigma tau : E →ₐ[k] L)
    (e : Spec (.of E) ⟶ Spec (.of L)) (i : Spec (.of L) ⟶ Spec (.of L))
    (c : pullback (Spec.map (CommRingCat.ofHom sigma.toRingHom))
      (Spec.map (CommRingCat.ofHom tau.toRingHom)) ⟶ Spec (.of L))
    [(Spec.map (CommRingCat.ofHom sigma.toRingHom)).IsFiniteLocallyFree]
    [(Spec.map (CommRingCat.ofHom tau.toRingHom)).IsFiniteLocallyFree]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (a : BasedFunctor (discreteModuli (yoneda.obj
      ((Spec (.of E)).asOver (Spec (.of k))))) F)
    (P : SchemeGroupoidQuotientPresentation
      ((Spec.map (CommRingCat.ofHom sigma.toRingHom)).asOver (Spec (.of k)))
      ((Spec.map (CommRingCat.ofHom tau.toRingHom)).asOver (Spec (.of k))) e i c F a) :
    ∃ D : GroupoidQuasiCoherentAlgebras F P.stack.1 ≌
        Scheme.AffineGroupoidAlgebra.{u, max (u + 1) v w}
          (Spec.map (CommRingCat.ofHom sigma.toRingHom))
          (Spec.map (CommRingCat.ofHom tau.toRingHom)) e i c P.groupoid,
      ∃ j : D.functor ⋙ Scheme.AffineGroupoidAlgebra.forget ≅
          groupoidAtlasAlgebraEvaluation P.stack.1 a,
        (∀ A : GroupoidQuasiCoherentAlgebras F P.stack.1,
          ∃ theta : pushout (D.functor.obj A).algebra.hom
              (Scheme.groupoidAlgebraCoordinateMap
                (Spec.map (CommRingCat.ofHom tau.toRingHom))) ⟶
            A.obj.right.obj.obj (op (a.obj (CostructuredArrow.mk
              (yoneda.map ((Spec.map (CommRingCat.ofHom tau.toRingHom)).asOver
                (Spec (.of k))))))),
            IsIso theta ∧
            pushout.inl _ _ ≫ theta = (j.app A).hom.right ≫
              A.obj.right.obj.map (groupoidChartRestriction a
                ((Spec.map (CommRingCat.ofHom tau.toRingHom)).asOver (Spec (.of k)))).op ∧
            pushout.inr _ _ ≫ theta = groupoidChartCoordinateComparison a
                (yoneda.map ((Spec.map (CommRingCat.ofHom tau.toRingHom)).asOver
                  (Spec (.of k)))) ≫ A.obj.hom.hom.app _ ∧
            pushout.inl (D.functor.obj A).algebra.hom
                (Scheme.groupoidAlgebraCoordinateMap
                  (Spec.map (CommRingCat.ofHom sigma.toRingHom))) ≫
              (D.functor.obj A).beta.hom ≫ theta = (j.app A).hom.right ≫
                A.obj.right.obj.map (groupoidChartRestriction a
                  ((Spec.map (CommRingCat.ofHom sigma.toRingHom)).asOver (Spec (.of k)))).op ≫
                A.obj.right.obj.map (groupoidPresentationAlgebraTransport
                  ((Spec.map (CommRingCat.ofHom sigma.toRingHom)).asOver (Spec (.of k)))
                  ((Spec.map (CommRingCat.ofHom tau.toRingHom)).asOver (Spec (.of k)))
                  a P.arrows).op) ∧
        (∀ A : GroupoidQuasiCoherentAlgebras F P.stack.1,
          ∃ rho : moduliGlobalSectionsRing A.obj.right ≃+*
              (D.functor.obj A).invariants,
            ∀ z : moduliGlobalSectionsRing A.obj.right,
              (j.app A).hom.right (rho z).val =
                z.val (op (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj
                  ((Spec (.of E)).asOver (Spec (.of k))))))))) ∧
        ∀ (A B : GroupoidQuasiCoherentAlgebras F P.stack.1) (f : A ⟶ B),
          IsSurjectiveModuliAlgebra f.hom →
            Function.Surjective (D.functor.map f).val.right := by
  sorry

end CategoryTheory
