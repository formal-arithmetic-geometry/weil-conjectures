module

public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-! # Poincare biduality and its naturality

Source: Milne, Abelian Varieties, I §8, pp.37–40, and I §9, p.41.
(blueprint: lem-sfb-abelian-poincare-biduality)

The evaluation and dual maps are characterized by the actual Poincare families.
Both identity-axis comparisons are included. The datum specifies its first-axis
rigidification, so the other-axis trivializations are normalized to agree at the
origin. All auxiliary definitions merely spell out these comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Transport a module trivialization across a specified commutative square, using
composition of tensor inverse images, equality transport, and the pullback of the unit.
Source: Milne AV I §8, p.37, normalization of families; Stacks Tag 0097.
(blueprint: lem-sfb-abelian-poincare-biduality) -/
def poincareRigidificationBaseChange {X Y X' Y' : Scheme.{u}}
    (j : X ⟶ Y) (j' : X' ⟶ Y') (f : X' ⟶ X) (g : Y' ⟶ Y)
    (h : j' ≫ g = f ≫ j) (P : Y.Modules)
    (r : (Scheme.Modules.pullback j).obj P ≅ 𝟙_ X.Modules) :
    (Scheme.Modules.pullback j').obj ((Scheme.Modules.pullback g).obj P) ≅
      𝟙_ X'.Modules :=
  (Scheme.Modules.pullbackComp j' g).app P ≪≫
    (Scheme.Modules.pullbackCongr h).app P ≪≫
    ((Scheme.Modules.pullbackComp f j).app P).symm ≪≫
    (Scheme.Modules.pullback f).mapIso r ≪≫ Scheme.Modules.pullbackObjUnitIso f

/-- The other identity axis of a Poincare family.
Source: Milne AV I §8, p.37, divisorial correspondences.
(blueprint: lem-sfb-abelian-poincare-biduality) -/
def poincareOtherIdentityAxis {k : Type u} [Field k]
    (A D : Over (Spec (.of k))) [GrpObj D] : A ⟶ A ⊗ D :=
  lift (𝟙 A) (toUnit A ≫ η[D])

/-- Restrict an axis trivialization to its origin, with the canonical composition
and unit comparisons. Source: Milne AV I §8, p.37, normalization.
(blueprint: lem-sfb-abelian-poincare-biduality) -/
def poincareRigidificationAtOrigin {X Y Z : Scheme.{u}} (e : Z ⟶ X) (j : X ⟶ Y)
    (P : Y.Modules) (r : (Scheme.Modules.pullback j).obj P ≅ 𝟙_ X.Modules) :
    (Scheme.Modules.pullback (e ≫ j)).obj P ≅ 𝟙_ Z.Modules :=
  ((Scheme.Modules.pullbackComp e j).app P).symm ≪≫
    (Scheme.Modules.pullback e).mapIso r ≪≫ Scheme.Modules.pullbackObjUnitIso e

/-- The two axis trivializations agree at the common origin. The second-axis
trivialization is not extra input to the dual datum: the proposition below quantifies
it and fixes its scalar by this equation. Source: Milne AV I §8, pp.37–38.
(blueprint: lem-sfb-abelian-poincare-biduality) -/
def PoincareAxesAgreeAtOrigin {k : Type u} [Field k]
    {A : Over (Spec (.of k))} [GrpObj A] (D : AbelianDualPoincareDatum A)
    (r : (Scheme.Modules.pullback (poincareOtherIdentityAxis A D.dual).left).obj
      D.poincare ≅ 𝟙_ A.left.Modules) : Prop :=
  ∃ h : (η[D.dual]).left ≫ (abelianIdentityAxis A D.dual).left =
      (η[A]).left ≫ (poincareOtherIdentityAxis A D.dual).left,
    (poincareRigidificationAtOrigin (η[D.dual]).left
      (abelianIdentityAxis A D.dual).left D.poincare D.rigidification).hom =
      ((Scheme.Modules.pullbackCongr h).app D.poincare).hom ≫
        (poincareRigidificationAtOrigin (η[A]).left
          (poincareOtherIdentityAxis A D.dual).left D.poincare r).hom

/-- The factor-switched Poincare identity, including compatibility with both normalized
identity axes. The square equalities express the actual restrictions of the factor switch
and `1 × delta`; they do not introduce arbitrary comparison maps.
Source: Milne AV I §8, pp.37–38, biduality consequence of Theorem 8.9.
(blueprint: lem-sfb-abelian-poincare-biduality) -/
def IsAbelianPoincareEvaluation {k : Type u} [Field k]
    {A : Over (Spec (.of k))} [GrpObj A] (D : AbelianDualPoincareDatum A)
    (E : AbelianDualPoincareDatum D.dual) (delta : A ⟶ E.dual) : Prop :=
  ∃ rD : (Scheme.Modules.pullback (poincareOtherIdentityAxis A D.dual).left).obj
      D.poincare ≅ 𝟙_ A.left.Modules,
    ∃ rE : (Scheme.Modules.pullback (poincareOtherIdentityAxis D.dual E.dual).left).obj
        E.poincare ≅ 𝟙_ D.dual.left.Modules,
      PoincareAxesAgreeAtOrigin D rD ∧ PoincareAxesAgreeAtOrigin E rE ∧
      ∃ hA : (abelianIdentityAxis D.dual A).left ≫ (β_ D.dual A).hom.left =
          (𝟙 A.left) ≫ (poincareOtherIdentityAxis A D.dual).left,
        ∃ hE : (poincareOtherIdentityAxis D.dual A).left ≫ (D.dual ◁ delta).left =
            (𝟙 D.dual.left) ≫ (poincareOtherIdentityAxis D.dual E.dual).left,
          ∃ hD : (poincareOtherIdentityAxis D.dual A).left ≫ (β_ D.dual A).hom.left =
              (𝟙 D.dual.left) ≫ (abelianIdentityAxis A D.dual).left,
            ∃ i : (Scheme.Modules.pullback (D.dual ◁ delta).left).obj E.poincare ≅
                (Scheme.Modules.pullback (β_ D.dual A).hom.left).obj D.poincare,
              (Scheme.Modules.pullback (abelianIdentityAxis D.dual A).left).map i.hom ≫
                  (poincareRigidificationBaseChange
                    (poincareOtherIdentityAxis A D.dual).left
                    (abelianIdentityAxis D.dual A).left (𝟙 A.left)
                    (β_ D.dual A).hom.left hA D.poincare rD).hom =
                (abelianRigidificationPullback D.dual E.dual A E.poincare
                  E.rigidification delta).hom ∧
              (Scheme.Modules.pullback (poincareOtherIdentityAxis D.dual A).left).map i.hom ≫
                  (poincareRigidificationBaseChange (abelianIdentityAxis A D.dual).left
                    (poincareOtherIdentityAxis D.dual A).left (𝟙 D.dual.left)
                    (β_ D.dual A).hom.left hD D.poincare D.rigidification).hom =
                (poincareRigidificationBaseChange
                  (poincareOtherIdentityAxis D.dual E.dual).left
                  (poincareOtherIdentityAxis D.dual A).left (𝟙 D.dual.left)
                  (D.dual ◁ delta).left hE E.poincare rE).hom

/-- A map of dual varieties classifies the Poincare family pulled back along `f × 1`,
with the pulled-back specified rigidification. Source: Milne AV I §9, p.41.
(blueprint: lem-sfb-abelian-poincare-biduality) -/
def ClassifiesAbelianDualHom {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    (D : AbelianDualPoincareDatum A) (F : AbelianDualPoincareDatum B)
    (f : A ⟶ B) (fDual : F.dual ⟶ D.dual) : Prop :=
  ∃ h : (abelianIdentityAxis A F.dual).left ≫ (f ▷ F.dual).left =
      (𝟙 F.dual.left) ≫ (abelianIdentityAxis B F.dual).left,
    ∃ i : (Scheme.Modules.pullback (A ◁ fDual).left).obj D.poincare ≅
        (Scheme.Modules.pullback (f ▷ F.dual).left).obj F.poincare,
      (Scheme.Modules.pullback (abelianIdentityAxis A F.dual).left).map i.hom ≫
          (poincareRigidificationBaseChange (abelianIdentityAxis B F.dual).left
            (abelianIdentityAxis A F.dual).left (𝟙 F.dual.left)
            (f ▷ F.dual).left h F.poincare F.rigidification).hom =
        (abelianRigidificationPullback A D.dual F.dual D.poincare
          D.rigidification fDual).hom

/-- Unique Poincare evaluation isomorphisms, and naturality with respect to the uniquely
classifying dual homomorphisms, over every field.

Source: Milne AV I §8, pp.37–40, the biduality consequence of Theorem 8.9;
I §9, p.41, the dual map and Theorem 9.1.
(blueprint: lem-sfb-abelian-poincare-biduality)

Proof plan:
1. For D = A^vee, classify the switched family Q = s^*P_A with parameter A using
D's universal property. Its geometric fibres are algebraically trivial: over each
algebraically closed extension the connected smooth parameter A joins
every fibre to the fibre at zero. Choose its first-axis rigidification from the
other-axis triviality of P_A and normalize at the origin. Uniqueness gives delta
and delta(0) = 0. Global units on the proper geometrically integral D are scalars,
so agreement at the origin also gives the second-axis compatibility.
2. A pointed map g between abelian varieties is a homomorphism: its defect
h(x,y) = g(x+y)-g(x)-g(y) vanishes on each axis. Rigidity makes h factor through
its second parameter, and the other axis makes it zero. Apply this to delta.
3. Choose an ample line L on A and classify its normalized difference N_L, with
the constant identity-line factor, to obtain the polarization lambda : A -> D.
The ample-line polarization lemma makes lambda an isogeny. Classify the pulled-back
Poincare family to obtain its dual mu : E -> D. Pullback preserves algebraic
equivalence and rigidification, and step 2 gives the homomorphism law. The dual
isogeny degree lemma gives deg(mu) = deg(lambda).
4. Pullback composition, the defining identities of delta and mu, and symmetry of
N_L give (1 x mu delta)^*P_A = N_L as rigidified families. Normalize intermediate
comparisons by parameter units; scalar units give the other axis. Universality
therefore gives mu delta = lambda.
5. Finite permanence over a separated target makes delta finite. The generic fibres
of A and E over D are spectra of fields of the same degree over k(D), since lambda
and mu are finite flat of the same rank. The field homomorphism induced by delta
is consequently an isomorphism, so delta is birational. This does not require
separability or a count of geometric points.
6. E is smooth, hence regular and normal. The finite birational normal-target
criterion makes delta an isomorphism; its inverse preserves the group operation.
Its uniqueness follows already from the universal property in step 1.
7. For any homomorphism f : A -> B, classifying (f x 1)^*P_B gives the unique dual
fDual. Repeating this gives fDoubleDual. Pull back their defining identities and
the two switched evaluation identities on B^vee x A. Composition identifies the
families for delta_A followed by fDoubleDual and for f followed by delta_B,
with their rigidifications; uniqueness identifies the maps. All maps are over k;
geometric extensions served only to test algebraic triviality of fibres.
-/
theorem IsAbelianVariety.poincare_biduality {k : Type u} [Field k] :
    (∀ (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
      (D : AbelianDualPoincareDatum A) (E : AbelianDualPoincareDatum D.dual),
      ∃! delta : A ≅ E.dual,
        IsMonHom delta.hom ∧ IsAbelianPoincareEvaluation D E delta.hom) ∧
    (∀ (A B : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
      [GrpObj B] [IsAbelianVariety B]
      (D : AbelianDualPoincareDatum A) (E : AbelianDualPoincareDatum D.dual)
      (F : AbelianDualPoincareDatum B) (G : AbelianDualPoincareDatum F.dual)
      (f : A ⟶ B), IsMonHom f →
      ∃ fDual : F.dual ⟶ D.dual,
        (IsMonHom fDual ∧ ∀ g : F.dual ⟶ D.dual,
          ClassifiesAbelianDualHom D F f g ↔ g = fDual) ∧
        ∃ fDoubleDual : E.dual ⟶ G.dual,
          (IsMonHom fDoubleDual ∧ ∀ g : E.dual ⟶ G.dual,
            ClassifiesAbelianDualHom G E fDual g ↔ g = fDoubleDual) ∧
          ∀ (deltaA : A ≅ E.dual) (deltaB : B ≅ G.dual),
            IsMonHom deltaA.hom → IsAbelianPoincareEvaluation D E deltaA.hom →
            IsMonHom deltaB.hom → IsAbelianPoincareEvaluation F G deltaB.hom →
            deltaA.hom ≫ fDoubleDual = f ≫ deltaB.hom) := by
  sorry

end AlgebraicGeometry
