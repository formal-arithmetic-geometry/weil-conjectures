module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Sheaf.AlgebraicGeometry.RhoSectionModuleData
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
import Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition
import Sheaf.Algebra.Lie.RationalHighestWeightModules
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.SemisimpleCentralIsogenyMultiplicative
import Sheaf.AlgebraicGeometry.GroupScheme.CentralIsogenyBorelRootCompatibility
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.LinearAlgebra.Trace
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Integration of split semisimple rational Lie algebras

Source: Milne, Algebraic Groups (2017), Theorems 22.53 and 23.70(a)--(e),
printed pp.481 and 507--508
(blueprint: lem-sfb-split-charzero-lie-group-integration).

The lattices are actual group-scheme Hom groups. Their identification with the
integral weight lattice is normalized by the canonical tangent differentials.
Representations on arbitrary finite-dimensional spaces are written in an arbitrary
finite basis; all character eigenvector conditions are tested on every algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

open Classical in
/-- A split semisimple rational Lie algebra integrates to a split simply connected
semisimple group, with its full integral weight lattice and all representations.
Source: Milne, Algebraic Groups (2017), Theorems 22.53 and 23.70(a)--(e),
printed pp.481 and 507--508
(blueprint: lem-sfb-split-charzero-lie-group-integration).

Proof plan (the steps of the DAG node):
1. Apply split root decomposition, the rational root-base theorem and rational
   highest-weight existence. Fundamental weights give a basis of P. The category
   of finite-dimensional rational Lie modules is abelian rigid symmetric tensor:
   kernels and cokernels are invariant linear ones, the tensor action is the sum
   of actions on the factors, and the dual action is minus the transpose. Actions
   on rational coordinate spaces give a skeleton for the neutral tensor envelope.
2. The unit and fundamental highest-weight modules tensor-generate: tensor the
   highest vectors, use complete reducibility, then highest-weight uniqueness.
   The envelope gives an affine finite-type G and its faithful representation.
3. The family of actions defines j. The adjoint action is faithful because the
   semisimple Lie algebra has zero centre; its trace form is nondegenerate by the
   faithful semisimple trace-form theorem.
4. A tensor derivation acts on the adjoint module as a Lie derivation, hence is
   inner. Subtract this inner family. Naturality for the action makes the remaining
   family scalar on every simple module. Perfectness makes traces zero, so the
   determinant form is a Lie intertwiner to the unit. Tensor naturality gives
   n times that scalar equal to zero; characteristic zero kills it. Complete
   reducibility then makes the family zero on every module. Thus j is onto.
5. Cartier gives smoothness. The tensor equivalence differentiates to the original
   action. Essential surjectivity and naturality show uniqueness on the same vector
   space. Zero-differential representations are trivial, giving geometric
   connectedness by the connected differential test; the semisimple-Lie converse
   gives semisimplicity. The Borel-pair theorem gives geometric reductivity.
6. Take T = Spec Q[P]. Character antiduality identifies its characters with P.
   The integral Lie weight gradings act tensor naturally, giving T -> G.
   Fundamental weights occur in the faithful module; their Laurent coordinates
   generate Q[P], so this map is a closed immersion.
7. Tangent characters are 1 + epsilon times evaluation on H. This identifies Lie(T)
   with j(H) and identifies differentiation of characters exactly with P. A larger
   geometric torus centralizes H; the root decomposition gives its Lie algebra H.
   Smooth-subgroup tangent generation makes that larger torus equal to T.
8. The adjoint Lie module integrates uniquely to Ad. Thus j identifies every root
   space with its actual torus-character space. The rank-one SL2 homomorphisms
   preserve brackets and give coroot tangent vectors with root evaluation two.
   The bracket line and normalization characterize c(alpha), hence identify these
   coroots; their integral coordinates show descent to Q.
9. Character antiduality identifies cocharacters with the integer dual of P. The
   root decomposition gives rational spanning, normalization, reducedness and the
   simultaneous reflection formulas. These preserve P and its dual; the finite
   rational reflection group is therefore the displayed lattice reflection group.
10. Over the algebraic closure, choose a Borel containing T by torus conjugacy.
    A central isogeny onto G lifts the Borel and torus and preserves coroots.
    Its character lattice embeds into P since every coroot evaluation is integral,
    while it already contains P. The torus map and its kernel are therefore trivial
    isogenies. Faithful flatness and representable fpqc descent give the inverse
    of the group map, proving simple connectedness.
11. Diagonalizable representation weight grading gives a finite internal direct
    sum on every module. Its character spaces are the original ordinary H-weight
    spaces by construction. All constructions include empty roots, zero modules
    and the zero Lie algebra. -/
theorem exists_splitCharZero_lieGroup_integration
    (g : Type u) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    [LieAlgebra.HasTrivialRadical ℚ g]
    (H : LieSubalgebra ℚ g) [IsLieAbelian H]
    (hmax : ∀ A : LieSubalgebra ℚ g, H ≤ A → IsLieAbelian A → A = H)
    (hsplit : ∀ h : H, (⨆ a : ℚ, (LieAlgebra.ad ℚ g (h : g)).eigenspace a) = ⊤)
    (R : Set (Module.Dual ℚ H))
    (hR : ∀ α : Module.Dual ℚ H, α ∈ R ↔
      α ≠ 0 ∧ LieModule.weightSpace g (α : H → ℚ) ≠ ⊥)
    (c : R → H)
    (hc : ∀ α : R,
      (c α : g) ∈ Submodule.span ℚ {z : g | ∃ x y : g,
        x ∈ LieModule.weightSpace g (α.1 : H → ℚ) ∧
        y ∈ LieModule.weightSpace g ((-α.1) : H → ℚ) ∧ ⁅x, y⁆ = z} ∧ α.1 (c α) = 2)
    (P : Submodule ℤ (Module.Dual ℚ H))
    (hP : ∀ mu : Module.Dual ℚ H, mu ∈ P ↔
      ∀ α : R, ∃ n : ℤ, mu (c α) = (n : ℚ)) :
    R.Finite ∧ ∃ (G T : Grp (Over (Spec (.of ℚ)))) (i : T ⟶ G)
      (j : g ≃ₗ⁅ℚ⁆ GrpObj.Lie G.X),
      IsAffine G.X.left ∧ Smooth G.X.hom ∧ ConnectedSpace G.X.left ∧
      IsSemisimpleGroupScheme
        ((MultiplicativeType.baseChange (K := AlgebraicClosure ℚ)).obj G).X ∧
      (∀ (G' : Over (Spec (.of (AlgebraicClosure ℚ)))) [GrpObj G'],
        IsSemisimpleGroupScheme G' →
        ∀ (f : G' ⟶ ((MultiplicativeType.baseChange (K := AlgebraicClosure ℚ)).obj G).X)
          [IsMonHom f], Surjective f.left → IsFinite (GrpObj.ker f).hom →
          (∀ (A : Type) [CommRing A] [Algebra (AlgebraicClosure ℚ) A]
            (x : StandardGroupSchemes.affine (AlgebraicClosure ℚ) A ⟶ GrpObj.ker f)
            (y : StandardGroupSchemes.affine (AlgebraicClosure ℚ) A ⟶ G'),
            (x ≫ GrpObj.kerι f) * y = y * (x ≫ GrpObj.kerι f)) → IsIso f) ∧
      IsClosedSubgroupScheme i.hom.hom ∧
      (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus ℚ r)) ∧
      ReductiveTorusCentralizer.IsMaximalTorus
        ((MultiplicativeType.baseChange (K := AlgebraicClosure ℚ)).map i) ∧
      ∃ (_ : IsCommMonObj T.X)
        (_ : IsCommMonObj (StandardGroupSchemes.multiplicative ℚ))
        (aG : ModObj T.X G.X)
        (jH : H ≃ₗ[ℚ] GrpObj.Lie T.X)
        (e : GrpObj.Lie (StandardGroupSchemes.multiplicative ℚ) ≃ₗ[ℚ] ℚ)
        (d : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)) ≃ₗ[ℤ] P)
        (D : RootDatum R
          (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative ℚ) ⟶ T))),
        aG.smul = (i.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X ∧
        (∀ h : H, GrpObj.differential i.hom.hom (jH h) = j (h : g)) ∧
        (∀ z : GrpObj.Lie (StandardGroupSchemes.multiplicative ℚ),
          e z = (RhoSection.characterValue (A := DualNumber ℚ)
            (GrpObj.tangentPoint z)).snd) ∧
        (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)))
          (h : H), (d χ : Module.Dual ℚ H) h =
            e (GrpObj.differential χ.toMul.hom.hom (jH h))) ∧
        Module.Finite ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ))) ∧
        Module.Free ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ))) ∧
        Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative ℚ) ⟶ T)) ∧
        Module.Free ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative ℚ) ⟶ T)) ∧
        (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)))
          (eta : Additive (Grp.mk (StandardGroupSchemes.multiplicative ℚ) ⟶ T)),
          eta.toMul.hom.hom ≫ χ.toMul.hom.hom =
            (𝟙 (StandardGroupSchemes.multiplicative ℚ)) ^ (D.toLinearMap χ eta)) ∧
        (∀ α : R, (d (D.root α) : Module.Dual ℚ H) = α.1) ∧
        (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)),
          (∃ α : R, D.root α = χ) ↔
            χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace ℚ _ T G aG χ.toMul ≠ ⊥) ∧
        (∀ α : R,
          Submodule.map j.toLinearEquiv.toLinearMap
            (LieModule.weightSpace g (α.1 : H → ℚ)).toSubmodule =
              @TorusCharacterTangent.weightSpace ℚ _ T G aG (D.root α).toMul) ∧
        (∀ α : R,
          GrpObj.differential (D.coroot α).toMul.hom.hom (e.symm 1) = jH (c α)) ∧
        (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)))
          (α : R), (D.toLinearMap χ (D.coroot α) : ℚ) =
            (d χ : Module.Dual ℚ H) (c α)) ∧
        D.IsReduced ∧
        Submodule.span ℚ (Set.range (fun α : R ↦
          (1 : ℚ) ⊗ₜ[ℤ] D.root α)) = ⊤ ∧
        Submodule.span ℚ (Set.range (fun α : R ↦
          (1 : ℚ) ⊗ₜ[ℤ] D.coroot α)) = ⊤ ∧
        Finite (Subgroup.closure (Set.range D.reflection)) ∧
        ∀ (V : Type v) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
          [LieRingModule g V] [LieModule ℚ g V]
          (n : ℕ) (b : Module.Basis (Fin n) ℚ V),
          ∃ (r : GeneralLinearGroup.RationalHom G.X (Fin n)) (_ : IsMonHom r),
            (∀ (x : g) (v : V),
              b.repr ⁅x, v⁆ = (r.differential (j x)).mulVec (b.repr v)) ∧
            (∀ (s : GeneralLinearGroup.RationalHom G.X (Fin n)) [IsMonHom s],
              (∀ (x : g) (v : V),
                b.repr ⁅x, v⁆ = (s.differential (j x)).mulVec (b.repr v)) → s = r) ∧
            ∃ W : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)) →
                Submodule ℚ V,
              {χ | W χ ≠ ⊥}.Finite ∧ DirectSum.IsInternal W ∧
              ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)),
                W χ = (LieModule.weightSpace V ((d χ : Module.Dual ℚ H) : H → ℚ)).toSubmodule ∧
                ∀ v : V, v ∈ W χ ↔
                  ∀ (A : Type) [CommRing A] [Algebra ℚ A] (t : points T.X A),
                    ((r.points A (t ≫ i.hom.hom) : Matrix (Fin n) (Fin n) A).mulVec
                      (fun k : Fin n ↦ algebraMap ℚ A (b.repr v k))) =
                        RhoSection.characterValue (t ≫ χ.toMul.hom.hom) •
                          (fun k : Fin n ↦ algebraMap ℚ A (b.repr v k)) := by
  sorry

end AlgebraicGeometry
