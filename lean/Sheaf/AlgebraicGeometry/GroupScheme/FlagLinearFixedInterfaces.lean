/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalProjectiveAction
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace

/-! # Linear projective actions, fixed points, and rational tangent weight bases

Source: Milne, Algebraic Groups (2017), Theorem 4.27, Theorem 13.1, Lemma 13.51,
and the paragraphs preceding Proposition 21.70 and proof of Theorem 21.73.
(blueprint: def-sfb-flag-linear-fixed-interfaces)

The projective coordinate substitution is the action on lines, not its dual.
Fixedness is tested after every algebra extension. A tangent basis uses the existing
residue-field tangent space and its actual postcomposition action, so no action or
vector-space structure can be chosen independently of the geometry.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.FlagGeometry

/-- Fixedness under a group-scheme map after every algebra extension.
Source: Milne, Theorem 13.1 (blueprint: def-sfb-flag-linear-fixed-interfaces). -/
def IsFixed {F : Type u} [Field F]
    {S G : Grp (Over (Spec (.of F)))} (i : S ⟶ G)
    (X : Over (Spec (.of F))) (a : ModObj G.X X)
    (A : CommAlgCat.{u} F) (x : (algSpec (.of F)).obj (op A) ⟶ X) : Prop :=
  ∀ (A' : CommAlgCat.{u} F) (f : A ⟶ A')
    (s : (algSpec (.of F)).obj (op A') ⟶ S.X),
    lift (s ≫ i.hom.hom) ((algSpec (.of F)).map f.op ≫ x) ≫ a.smul =
      (algSpec (.of F)).map f.op ≫ x

/-- The projective action induced by a rational representation, specified by
`X_i ↦ ∑_j ρ(g)_{ij} X_j` over every test algebra. The two projection equalities
pin the projective base-change isomorphism. Thus this is the projective space of
lines in F^(n+1), with the given representation acting on those lines.
Source: Milne, Theorem 4.27 and Lemma 13.51
(blueprint: def-sfb-flag-linear-fixed-interfaces). -/
def IsLinearProjectiveAction {F : Type u} [Field F]
    (G : Grp (Over (Spec (.of F)))) (n : ℕ)
    (ρ : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F)
    (a : ModObj G.X (DiagonalProjectiveAction.space F n)) : Prop :=
  ∀ (A : CommAlgCat.{u} F) (g : (Spec (.of A)).asOver (Spec (.of F)) ⟶ G.X),
    ∃ φ ψ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) F →+*ᵍ
        MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A,
      φ.toRingHom = MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap F A))
        (fun i ↦ ∑ j, MvPolynomial.C
          ((GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin (n + 1))) F A (g ≫ ρ)) i j) *
            MvPolynomial.X j) ∧
      ψ.toRingHom = MvPolynomial.map (algebraMap F A) ∧
      ∃ (hφ : HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) F)).map φ)
        (hψ : HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) F)).map ψ),
        ∃ e : Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A ≅
            (((Spec (.of A)).asOver (Spec (.of F))) ⊗
              DiagonalProjectiveAction.space F n).left,
          e.hom ≫ (fst ((Spec (.of A)).asOver (Spec (.of F)))
            (DiagonalProjectiveAction.space F n)).left =
              Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A ∧
          e.hom ≫ (snd ((Spec (.of A)).asOver (Spec (.of F)))
            (DiagonalProjectiveAction.space F n)).left = Proj.map ψ hψ ∧
          e.hom ≫ ((g ▷ DiagonalProjectiveAction.space F n) ≫ a.smul).left =
            Proj.map φ hφ

/-- A tangent character basis at a rational point. Its vectors form a basis of the
existing residue-field tangent space, one vector for each character in S. The residue
identification is required to induce the given rational point. Translation by each
rational torus point is postcomposition on dual-number vectors and multiplies the
corresponding basis vector by its character value. For a split torus over an
algebraically closed field this is the character-weight decomposition, in every
characteristic, including an empty basis.
Source: Milne, proof of Theorem 21.73, p.447; Stacks Tag 0B2C
(blueprint: def-sfb-flag-linear-fixed-interfaces). -/
def HasTangentWeightBasis {F : Type u} [Field F]
    {T G : Grp (Over (Spec (.of F)))} (i : T ⟶ G)
    (X : Over (Spec (.of F))) (a : ModObj G.X X)
    (e : 𝟙_ (Over (Spec (.of F))) ⟶ X) (S : Set (RankOneRoots.Character T)) : Prop :=
  ∃ (x : X.left) (ε : X.left.residueField x ≅ CommRingCat.of F),
    e.left = Spec.map ε.hom ≫ X.left.fromSpecResidueField x ∧
    ∃ b : Module.Basis S (X.left.residueField x)
        (schemeTangentSpace F X.left X.hom x),
      ∀ (χ : S) (t : 𝟙_ (Over (Spec (.of F))) ⟶ T.X),
        (b χ).val ≫ (lift (toUnit X ≫ t ≫ i.hom.hom) (𝟙 X) ≫ a.smul).left =
          (ε.inv.hom ((Scheme.ΓSpecIso (.of F)).hom
            ((t ≫ χ.val.hom.hom).left.appTop
              ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
                (LaurentPolynomial.T 1)))) • b χ).val

end AlgebraicGeometry.FlagGeometry
