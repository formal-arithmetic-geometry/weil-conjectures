module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
/-- Compatible ordinary tensor coordinates, pinned to the actual open restriction map.

Proof: use the inverse stalk maps of the four open inclusions, transporting
endpoints by the point equalities coming from hj and the restriction squares.
The stalkMap_comp and stalkMap_congr_hom identities prove the four ring-map
compatibilities. For alpha use the additive restriction-stalk natural isomorphism,
composed with overFunctorEquiv, in every degree. Represent a scalar and a module
element by germs on a common open. The inverse stalk ring map sends a ring germ
to the germ of the inverse section-ring map. The germ_smul and
germ_restrictStalkNatIso_hom_app formulas then give alpha's semilinearity.
Naturality for P.d proves that alpha is a chain isomorphism.
Define tau on pure tensors by c tensor q mapping to eC(c) tensor alpha(q).
Semilinearity and the A-to-C ring-map compatibility prove balancedness. Its
inverse uses the inverse ring equivalence and alpha inverse; tensor induction
proves the inverse equations. Naturality for the differential gives a chain iso.
For the last equation, use the defining degreewise formula of tensorStalkIso.
Expand openPinnedTensorRestrictionIso into its four adjunction comparisons.
Their units are pinned to the pulled-back section 1 tensor s. The mate equation
for pushforward composition and the open restriction adjunction therefore sends
a restricted pure germ tensor to its ambient germ tensor. Compose with
restrictStalkNatIso, whose germ formula is the same-germ map. Both sides of the
last equation are thus equal on c tensor q, and tensor induction gives equality
on the whole module in every degree. This is a chain-level construction; it
asserts no compatibility with derived homology factors.
Empty opens have no z; top opens give the identity germ maps. Zero complexes
and zero rings obey the same formulas, without a nonzero or flatness assumption.
Source: Stacks Project, Tags 0098 and 0096; Mathlib restrictStalkNatIso and its
same-germ formulas; the pinned tensor pullback unit and composition comparisons.
(blueprint: lem-pc-open-ordinary-tensor-germ-coordinates). -/
theorem exists_openOrdinaryTensor_germ_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let R₀ := R (f ∣_ V) j z
    let A₀ := A j z
    let B₀ := B (f' ∣_ V') z
    let C₀ := C z
    let R₁ := R f g' z.val
    let A₁ := A g' z.val
    let B₁ := B f' z.val
    let C₁ := C z.val
    letI := leftAlgebra (f ∣_ V) j z
    letI := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
    letI := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
    letI := leftAlgebra f g' z.val
    letI := rightAlgebra f f' g g' sq z.val
    letI := (tensorMap f f' g g' sq z.val).toAlgebra
    let K₀ := stalkComplex j z Q₀
    let K := stalkComplex g' z.val P
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    ∃ (eR : R₀ ≃+* R₁) (eA : A₀ ≃+* A₁) (eB : B₀ ≃+* B₁) (eC : C₀ ≃+* C₁),
      eA.toRingHom.comp (algebraMap R₀ A₀) = (algebraMap R₁ A₁).comp eR.toRingHom ∧
      eB.toRingHom.comp (algebraMap R₀ B₀) = (algebraMap R₁ B₁).comp eR.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        (algebraMap A₀ (A₀ ⊗[R₀] B₀))) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          (algebraMap A₁ (A₁ ⊗[R₁] B₁))).comp eA.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom ∧
      ∃ α : ((forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).obj K₀ ≅
          ((forget₂ (ModuleCat.{u} A₁) AddCommGrpCat.{u}).mapHomologicalComplex
            (.up ℤ)).obj K,
        (∀ (n : ℤ) (a : A₀) (q : K₀.X n),
          α.hom.f n (a • q) = eA a • (show K.X n from α.hom.f n q)) ∧
        ∃ τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
            (F.mapHomologicalComplex (.up ℤ)).obj T,
          (∀ (n : ℤ) (c : C₀) (q : K₀.X n),
            τ.hom.f n (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
                (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) =
              eC c ⊗ₜ[A₁,(algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
                (algebraMap A₁ (A₁ ⊗[R₁] B₁))] (show K.X n from α.hom.f n q)) ∧
          (∀ n : ℤ,
            τ.hom.f n ≫ F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n) =
              F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
                (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
                F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
                  (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
                γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))) := by sorry

end AlgebraicGeometry
