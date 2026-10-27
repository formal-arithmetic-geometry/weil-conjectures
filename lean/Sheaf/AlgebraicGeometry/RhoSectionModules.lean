module

public import Sheaf.AlgebraicGeometry.RhoSectionModuleData
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Borel pairs and actual rho section modules

Source: Milne, Algebraic Groups (2017), Definitions 17.6, 19.22 and 22.21,
Theorems 17.9--17.10, 22.11, Proposition 22.27 and 22.48--22.49; Alper, Section 9.7,
immediately preceding Lemma 9.7.2 (positive right-semi-invariance convention)
(blueprint: lem-sfb-rho-section-modules).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A split maximal torus contained in a Borel subgroup, with the inclusion maps retained.
Source: Milne, Definitions 17.6 and 19.22
(blueprint: lem-sfb-rho-section-modules). -/
def IsRhoBorelPair {F : Type u} [Field F] [IsAlgClosed F]
    {S T B : Grp (Over (Spec (.of F)))}
    (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B) : Prop :=
  ReductiveTorusCentralizer.IsMaximalTorus i ∧
    (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) ∧
    IsBorelGroupScheme j.hom.hom ∧ k ≫ j = i

/-- Borel pairs exist, and for every such pair the integral half-sum character
extends to B, vanishes on its unipotent radical, and gives nonzero finite-dimensional
actual regular-function section modules with their rational left-translation action.
The equation rho squared = product of positive roots is in the character group,
so no division in the coefficient field is used.

Source: Milne, Definitions 17.6, 19.22, 22.21, Theorems 17.9--17.10 and 22.11,
Proposition 22.27 and 22.48--22.49; Alper, Section 9.7 before Lemma 9.7.2
(blueprint: lem-sfb-rho-section-modules).

Proof plan:
1. By lem-sfb-reductive-borel-pair-structure semisimple implies reductive, so
   choose T inside B inside S. The same input gives the root datum, positive
   system, B = U semidirect T with projection p, and the proper flag quotient S/B.
2. In X tensor Q, each simple reflection permutes the other positive roots,
   so its action on the half-sum is rho minus that simple root. Every simple
   coroot pairing is therefore 1. By lem-sfb-simply-connected-character-lattice,
   rho is the sum of the fundamental weights and is an actual character.
   Extend by p. It is trivial on U and m rho is dominant for every m positive.
   The empty sum in rank zero is zero, also in characteristic 2.
3. By lem-sfb-dominant-character-highest-line choose v nonzero of weight m rho
   in a rational S-module and a linear form ell with ell(v)=1. The regular matrix
   coefficient f(g)=ell(gv) lies in the actual section subspace over every algebra,
   and f(1)=1 proves it is nonzero.
4. By lem-sfb-homogeneous-line-bundle-sections this subspace is the global
   sections of the coherent homogeneous line bundle for -m rho on proper S/B.
   The degree-zero affine-base clause of lem-pc-coherent-hi gives finiteness over F.
5. Right semi-invariance is the kernel of f mapping to r*f minus f tensor rho^m.
   Left translation commutes with this map, since (s inverse g)b=s inverse(gb).
   Tensoring over a field preserves kernels, so the regular left coaction restricts
   to this very subspace. Coassociativity and the counit restrict too. Choose a
   basis to express the resulting rational action by RationalHom; its columns
   give exactly the displayed left-translation identity over every test algebra. -/
theorem exists_rho_section_modules {F : Type u} [Field F] [IsAlgClosed F]
    (S : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f) :
    (∃ (T B : Grp (Over (Spec (.of F))))
      (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B), IsRhoBorelPair i j k) ∧
    ∀ (T B : Grp (Over (Spec (.of F))))
      (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B), IsRhoBorelPair i j k →
      ∃ a : ModObj T.X B.X,
        (∀ (Z : Over (Spec (.of F))) (t : Z ⟶ T.X) (b : Z ⟶ B.X),
          lift t b ≫ a.smul =
            (t ≫ k.hom.hom) * b * (t ≫ k.hom.hom)⁻¹) ∧
        ∃ (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
          (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          Φ.Nodup ∧ (∀ α, α ∈ Φ ↔ α.hom.hom ≠ 1 ∧
            @TorusCharacterTangent.weightSpace F _ T B a α ≠ ⊥) ∧
          ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod ∧ k ≫ ρB = ρ ∧
          (∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ B),
            IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
            ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
              l.hom.hom ≫ ρB.hom.hom = 1) ∧
          ∀ (m : ℕ), 0 < m →
            RhoSection.sectionModule S B j ρB m ≠ ⊥ ∧
            Module.Finite F (RhoSection.sectionModule S B j ρB m) ∧
            RhoSection.HasRationalLeftTranslation S (RhoSection.sectionModule S B j ρB m) := by
  sorry

end AlgebraicGeometry
