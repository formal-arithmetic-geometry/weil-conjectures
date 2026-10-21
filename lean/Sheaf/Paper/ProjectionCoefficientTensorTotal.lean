module
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport

/-! # The representative-normalized tensor comparison for projection

Source: main-20261015, projection-formula proof step 13
(blueprint: def-sf-projection-coefficient-tensor-total).
The ordinary comparison is fixed on homogeneous local pure tensors. Derived
descent and the specified quotient-completion unit then fix its integral and
rational constructible restrictions.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.ProjectionTensorCoefficient

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- Termwise scalar restriction along the quotient-normalized ring isomorphism.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def complexTransport :=
  (fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)

/-- Signed total tensor after coefficient restriction.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def totalTarget :=
  ((complexTransport l E X).prod (complexTransport l E X)) ⋙
    Functor.uncurry.obj
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map₂CochainComplex)

private theorem tensor_hom_ext
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N H : pbcModules X R)
    {f g : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H}
    (h : ∀ U x y, f.val.app U (proEtaleTensorPair X R M N U x y) =
      g.val.app U (proEtaleTensorPair X R M N U x y)) : f = g := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private def coefficientIso :
    pbcAdicCompletion X (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E X := by
  let lift : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
      ((adicLisseForget X).obj R ⟶ (adicLisseForget X).obj S) → (R ⟶ S) :=
    fun {R S} f ↦ ⟨{
      app := fun U ↦ CommRingCat.ofHom (f.hom.app U).hom
      naturality := by
        intro U V g
        apply (forget₂ CommRingCat RingCat).map_injective
        exact f.hom.naturality g }⟩
  let e : (adicLisseForget X).obj (pbcAdicCompletion X (pbcIntegralDatum l E)) ≅
      (adicLisseForget X).obj (completedIntegralCommRingSheafUnrestricted l E X) :=
    integralDetailedCoefficientComparison X l E
  let c : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E X := {
    hom := lift e.hom
    inv := lift e.inv
    hom_inv_id := by
      apply (adicLisseForget X).map_injective
      exact e.hom_inv_id
    inv_hom_id := by
      apply (adicLisseForget X).map_injective
      exact e.inv_hom_id }
  exact c

/-- The coefficient tensor comparison is fixed on local pure tensors.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: send x tensor y to the same tensor of the two restricted sections.
Restriction along the inverse ring isomorphism gives the inverse. Balancedness
and restriction compatibility descend through sheafification. Pure tensors
locally generate the tensor sheaf, proving naturality and uniqueness. -/
theorem module_existsUnique :
    ∃! mu : ∀ M N : integralTowerModules l E X,
      (fdCoefficientTransport l E X).obj
          (((constructibleTensorOrdinary l E X).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
          ((fdCoefficientTransport l E X).obj M)).obj
            ((fdCoefficientTransport l E X).obj N),
      (∀ (M M' N N' : integralTowerModules l E X) (f : M ⟶ M') (g : N ⟶ N'),
        (fdCoefficientTransport l E X).map
            (((constructibleTensorOrdinary l E X).map f).app N ≫
              ((constructibleTensorOrdinary l E X).obj M').map g) ≫ (mu M' N').hom =
          (mu M N).hom ≫
            ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map
              ((fdCoefficientTransport l E X).map f)).app
                ((fdCoefficientTransport l E X).obj N) ≫
            ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
              ((fdCoefficientTransport l E X).obj M')).map
                ((fdCoefficientTransport l E X).map g)) ∧
      ∀ (M N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (x : M.val.obj U) (y : N.val.obj U),
        (mu M N).hom.val.app U
          (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X) M N U x y) =
        proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
          ((fdCoefficientTransport l E X).obj M)
          ((fdCoefficientTransport l E X).obj N) U x y := by
  let c := coefficientIso l E X
  let t := (SheafOfModules.ringIso_tensor_transport c).some
  let := t.monoidal
  let mu := fun (M N : integralTowerModules l E X) ↦ asIso (Functor.OplaxMonoidal.δ
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom) M N)
  refine ⟨mu, ⟨?_, ?_⟩, ?_⟩
  · intro M M' N N' f g
    exact (Functor.OplaxMonoidal.δ_natural
      (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom) f g).symm
  · intro M N U x y
    exact t.pure_hom M N U x y
  · intro nu hnu
    funext M N
    apply Iso.ext
    apply (cancel_epi (mu M N).inv).1
    rw [Iso.inv_hom_id]
    apply tensor_hom_ext X (pbcAdicCompletion X (pbcIntegralDatum l E))
    intro U x y
    have hi : (mu M N).inv.val.app U
        (proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
          ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj M)
          ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj N) U x y) =
        proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X)
          M N U x y := by
      have hp : (mu M N).hom.val.app U
          (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X)
            M N U x y) =
          proEtaleTensorPair X (pbcAdicCompletion X (pbcIntegralDatum l E))
            ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj M)
            ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.hom).obj N) U x y :=
        t.pure_hom M N U x y
      rw [← hp]
      exact congrArg (fun f ↦ f.val.app U
        (proEtaleTensorPair X (completedIntegralCommRingSheafUnrestricted l E X)
          M N U x y)) (mu M N).hom_inv_id
    change (nu M N).hom.val.app U ((mu M N).inv.val.app U _) = _
    rw [hi]
    exact hnu.2 M N U x y

/-- The uniquely pure-tensor-normalized module comparison.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def moduleComparison (M N : integralTowerModules l E X) :
    (fdCoefficientTransport l E X).obj
        (((constructibleTensorOrdinary l E X).obj M).obj N) ≅
      ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
        ((fdCoefficientTransport l E X).obj M)).obj
          ((fdCoefficientTransport l E X).obj N) :=
  (module_existsUnique l E X).exists.choose M N

/-- Naturality of the specified ordinary coefficient tensor comparison.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: the first clause of the unique pure-tensor characterization gives this
identity; both sides send the generator x tensor y to f(x) tensor g(y). -/
theorem module_naturality
    {M M' N N' : integralTowerModules l E X} (f : M ⟶ M') (g : N ⟶ N') :
    (fdCoefficientTransport l E X).map
        (((constructibleTensorOrdinary l E X).map f).app N ≫
          ((constructibleTensorOrdinary l E X).obj M').map g) ≫
        (moduleComparison l E X M' N').hom =
      (moduleComparison l E X M N).hom ≫
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).map
          ((fdCoefficientTransport l E X).map f)).app
            ((fdCoefficientTransport l E X).obj N) ≫
        ((proEtaleOrdinaryTensor X (pbcAdicCompletion X (pbcIntegralDatum l E))).obj
          ((fdCoefficientTransport l E X).obj M')).map
            ((fdCoefficientTransport l E X).map g) := by
  exact (module_existsUnique l E X).exists.choose_spec.1 M M' N N' f g

/-- Naturality in the tensorHom coordinates used by the signed-total constructor.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: tensorHom is the first-variable tensor map followed by the
second-variable map. Thus this is precisely module_naturality, with the
same specified monoidal structures on both module categories. -/
theorem module_tensorHom_naturality
    {M M' N N' : integralTowerModules l E X} (f : M ⟶ M') (g : N ⟶ N') :
    (fdCoefficientTransport l E X).map
        (@MonoidalCategoryStruct.tensorHom (integralTowerModules l E X) _
          (SheafOfModules.monoidalCategory
            (completedIntegralCommRingSheafUnrestricted l E X)).toMonoidalCategoryStruct
          M M' N N' f g) ≫ (moduleComparison l E X M' N').hom =
      (moduleComparison l E X M N).hom ≫
        @MonoidalCategoryStruct.tensorHom
          (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) _
          (SheafOfModules.monoidalCategory
            (pbcAdicCompletion X (pbcIntegralDatum l E))).toMonoidalCategoryStruct
          _ _ _ _ ((fdCoefficientTransport l E X).map f)
          ((fdCoefficientTransport l E X).map g) := by
  exact module_naturality l E X f g

/-- The inverse module comparison summed over all bidegrees with the usual signs.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def total (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (totalTarget l E X).obj (P, Q) ⟶
      (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) :=
  letI : MonoidalCategory (integralTowerModules l E X) :=
    SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  letI : MonoidalPreadditive (integralTowerModules l E X) :=
    proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalPreadditive
      (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let F : integralTowerModules l E X ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
    fdCoefficientTransport l E X
  letI : F.Additive := fdCoefficientTransportAdditive l E X
  tensorPullbackTotal
    (A := integralTowerModules l E X)
    (B := pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
    F (moduleComparison l E X)
    (module_tensorHom_naturality l E X) P Q

/-- The signed total comparison is invertible.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total).
Proof: exact coefficient restriction along an isomorphism preserves direct sums;
each summand comparison is invertible. The same direct-sum formula with the
inverse summand maps is the two-sided inverse chain map. -/
theorem total_isIso (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    IsIso (total l E X P Q) := by
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E X)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  let := proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  let := proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let F : integralTowerModules l E X ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
    fdCoefficientTransport l E X
  let : F.Additive := fdCoefficientTransportAdditive l E X
  let t := (SheafOfModules.ringIso_tensor_transport (coefficientIso l E X)).some
  have : F.IsEquivalence := by
    change (SheafOfModules.scalarRestriction (coefficientIso l E X).hom).IsEquivalence
    rw [← t.functor_eq]
    exact t.equivalence.isEquivalence_functor
  exact tensorPullbackTotal_isIso
    (A := integralTowerModules l E X)
    (B := pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
    F (moduleComparison l E X) (module_tensorHom_naturality l E X)
    F.asEquivalence.inverse F.asEquivalence.toAdjunction P Q

/-- The signed total isomorphism with the derived-square orientation.
Source: step 13 (blueprint: def-sf-projection-coefficient-tensor-total). -/
def totalIso (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) ≅
      (totalTarget l E X).obj (P, Q) :=
  letI := total_isIso l E X P Q
  (asIso (total l E X P Q)).symm

end WeilConjectures.ProjectionTensorCoefficient
