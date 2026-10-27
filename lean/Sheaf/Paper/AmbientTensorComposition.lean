module

public import Sheaf.Paper.AmbientPullbackTensorData

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-normalized-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

/-- Ordinary tensor composition and its total and derived representative equations.
Source: Stacks 03EL, 06YN, 07A4, 0G7E and 0G7D
(blueprint: lem-sf-ambient-normalized-tensor-composition).
Proof: transpose the ordinary equality under the composite module adjunction and
test on sheafified pure tensors. The three normalization equations and hgen send
both routes to the tensor of the two composite generators, with the product of
intermediate scalars in the first factor and 1 in the second. Tensor balancing
and the sheafification universal property extend equality to module morphisms.
For complexes, invert the ordinary equality and use the model.summand equations.
The total tensor functor maps the two chain comparators degreewise. Its summand
inclusions reduce the displayed chain equality to that inverse ordinary equation;
naturality handles both signed differentials. Direct-sum universality proves the
chain equality. Resolve both inputs on the whole ringed site by flat-term K-flat
complexes. The normalization hypotheses preserve that representative class under
successive pullback. Substitute the model.derived equations and the exact
factorization of derivedComp into the localization of the chain equality, and
cancel the invertible representative comparisons. Cochain tensor rigidity, or
the resolving-subcategory localization universal property, extends the resulting
natural-transformation equality to all unbounded inputs. These steps are on the
sequence site itself and use no cartesian-system or flat-transition hypothesis. -/
theorem normalizedTensor_composition {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ)
    (A : Tensor ell E Z s) (B : Tensor ell E Y s) (C : Tensor ell E X s)
    (TA : TensorModels ell E Z s A) (TB : TensorModels ell E Y s B)
    (TC : TensorModels ell E X s C)
    (Kf : TensorData ell E f s B C TB TC) (Kg : TensorData ell E g s A B TA TB)
    (Kh : TensorData ell E (f ≫ g) s A C TA TC)
    (_hKf : Kf.Normalized ell E f s B C TB TC)
    (_hKg : Kg.Normalized ell E g s A B TA TB)
    (_hKh : Kh.Normalized ell E (f ≫ g) s A C TA TC)
    (_hgen : (∀ (M : Modules ell E Z s) (U : Site Z s) (V : Site Y s) (W : Site X s)
      (p : V ⟶ (base g s).obj U) (q : W ⟶ (base f s).obj V)
      (m : M.val.obj (op U)) (a : (coefficients ell E Y s).obj.obj (op V))
      (b : (coefficients ell E X s).obj.obj (op W)),
      ((comp ell E f g s).hom.app M).val.app (op W)
          (generator ell E f s ((pull ell E g s).obj M) V W q
            (generator ell E g s M U V p m a) b) =
        generator ell E (f ≫ g) s M U W
          (q ≫ (base f s).map p ≫ (baseComp f g s).inv.app U) m
          (scalar ell E f s V W q a * b))) :
    (∀ (M N : Modules ell E Z s),
      (pull ell E f s).map (Kg.model.ordinary M N).hom ≫
          (Kf.model.ordinary
            ((pull ell E g s).obj M) ((pull ell E g s).obj N)).hom ≫
          tensorHom ell E X s ((comp ell E f g s).hom.app M)
            ((comp ell E f g s).hom.app N) =
        (comp ell E f g s).hom.app (tensor ell E Z s M N) ≫
          (Kh.model.ordinary M N).hom) ∧
    (∀ P Q : CochainComplex (Modules ell E Z s) ℤ,
      FlatRepresentative ell E Z s P → FlatRepresentative ell E Z s Q →
      (total ell E X s).map (Prod.mkHom (chainComp ell E f g s P)
          (chainComp ell E f g s Q)) ≫
          Kh.model.chain P Q =
        Kf.model.chain
            (((pull ell E g s).mapHomologicalComplex (.up ℤ)).obj P)
            (((pull ell E g s).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          ((pull ell E f s).mapHomologicalComplex (.up ℤ)).map
            (Kg.model.chain P Q) ≫
          chainComp ell E f g s ((total ell E Z s).obj (P, Q))) ∧
    ∀ F G : Derived ell E Z s,
      (derivedPull ell E f s).map (Kg.mu.hom.app (F, G)) ≫
          Kf.mu.hom.app
            ((derivedPull ell E g s).obj F, (derivedPull ell E g s).obj G) ≫
          C.tensor.map (Prod.mkHom ((derivedComp ell E f g s).hom.app F)
            ((derivedComp ell E f g s).hom.app G)) =
        (derivedComp ell E f g s).hom.app (A.tensor.obj (F, G)) ≫
          Kh.mu.hom.app (F, G) := by sorry

end WeilConjectures.AmbientPullbackTensor
