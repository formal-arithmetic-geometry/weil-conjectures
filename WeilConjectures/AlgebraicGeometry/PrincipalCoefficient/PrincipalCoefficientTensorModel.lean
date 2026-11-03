/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientTensorEvaluation

/-! # An objectwise tensor/coinduction comparison with its chain model

Source: latest blueprint lem-fix-operation-reduction, perfect tensor/Hom comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry.PrincipalCoefficient

/-- Construct an ordinary evaluation map and identify its derived source and target.
This statement constructs a morphism; it does not assert its invertibility.
Source: latest blueprint lem-fix-operation-reduction; Stacks 06YY, 0A70 and 0A71
(blueprint: lem-principal-coefficient-tensor-model).

Proof: choose a K-injective resolution eta of the coefficient unit and write I for
its complex. For a K-flat P, extension is computed by ordinary sheafified scalar
extension, which is K-flat over B: the ordinary mixed-tensor balancing isomorphism
identifies tensoring it with an acyclic B-complex with P tensored with the exact
restriction of that complex. Thus the derived tensor source is computed by
E(P) tensor H(I). Resolve P tensor I by a K-injective J. The ordinary mixed
balancing isomorphism has inverse kappa: P tensor U(N) to U(E(P) tensor N),
namely the actual scalar unit tensored with U(N), followed by the lax tensorator
of U. This formula holds first on pure presheaf tensors and descends through the
sheafification units. Its naturality in both variables respects the two signed
total differentials. Restriction preserves the total coproducts, so this gives a
chain isomorphism. Transpose its inverse followed by P tensor the H-counit and p
along the chain adjunction U to H. This constructs t and proves the equation
CoinductionTensorEvaluation. On local generators its formula is
((b tensor x) tensor h)(b') = p(x tensor h(b' b)), which also checks balancing. The map
P to P tensor I to J is a quasi-isomorphism by K-flatness and eta, so the actual
coinduction derived counit identifies H(QP) with QH(J). This gives e and d and
the displayed counit equation. The isomorphisms e and d come from the actual
derived comparisons and the indicated quasi-isomorphisms; no fullness of derived
restriction is used.
An objectwise isomorphism suffices for the exceptional comparison, so no natural
transformation on the derived category or descent of such a transformation
through roofs is asserted. No perfectness is needed for this construction,
and its input is unbounded. -/
theorem tensorCoinduction_chainModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let E := Sheaf.extendScalars X.smallEtaleTopology φ
    let H := Etale.coextendScalars φ X
    let F := extension X.smallEtaleTopology φ ⋙
      tensorRight (H.rightDerivedFunctor.obj (𝟙_ (_root_.DerivedCategory C)))
    ∀ (P : CochainComplex C ℤ)
      (_ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P),
      ∃ (I : CochainComplex C ℤ) (_ : I.IsKInjective)
        (η : 𝟙_ (CochainComplex C ℤ) ⟶ I), QuasiIso η ∧
        ∃ (J : CochainComplex C ℤ) (_ : J.IsKInjective) (p : P ⊗ I ⟶ J), QuasiIso p ∧
          ∃ (_ : F.obj (_root_.DerivedCategory.Q.obj P) ≅
              _root_.DerivedCategory.Q.obj
                (((E.mapHomologicalComplex (.up ℤ)).obj P) ⊗
                  ((H.mapHomologicalComplex (.up ℤ)).obj I)))
            (_ : H.rightDerivedFunctor.obj (_root_.DerivedCategory.Q.obj P) ≅
              _root_.DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj J))
            (t : ((E.mapHomologicalComplex (.up ℤ)).obj P) ⊗
                ((H.mapHomologicalComplex (.up ℤ)).obj I) ⟶
              ((H.mapHomologicalComplex (.up ℤ)).obj J)),
            CoinductionTensorEvaluation φ X P I J p t := by
  sorry

end AlgebraicGeometry.PrincipalCoefficient
