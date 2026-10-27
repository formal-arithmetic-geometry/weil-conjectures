module

public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalHom
public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

import Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.LocallySeparatedGroupSpaceScheme
import Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-! # Polarization calculus over an arbitrary field

Source: Milne, Abelian Varieties, I §§8–10 and §14 opening.
(blueprint: lem-sfb-polarization-calculus-over-field)

Rational composition is specified by its values on pure tensors. This uniquely
specifies the usual composition, rather than postulating an unrelated operation.
The Poincare families specify the dual maps as actual scheme morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme.Modules

/-- Polarization, duality, the Rosati involution and the symmetric rational kernel,
over any field. The point formulas use all algebraically closed field-valued points.
Source: Milne AV I Proposition 8.4, Remark 8.5, pp.35–41, Lemma 10.6,
and §14 opening (blueprint: lem-sfb-polarization-calculus-over-field).

Proof:
1. Regard A as a group algebraic space (def-trf-scheme-algebraic-space).
By lem-sc-av-commutative, lem-sc-abelian-variety-characterization and
lem-sfb-abelian-field-extension it is a proper smooth commutative abelian family.
Apply lem-sfb-abelian-space-poincare-calculus over Spec k and represent its dual
by lem-sfb-locally-separated-group-space-scheme. The ordinary/etale line comparison
lem-trf-scheme-etale-invertible-comparison gives the normalized dual datum and
classifiers, including their point formulas.
2. Distribute pullback over tensor (lem-weil-pbc-module-pullback-tensor) in the
explicit normalized difference. Its tensor and unit identities, and the representing
tensor law, give additivity and the zero formula.
3. Substituting b times b in that difference, using pullback composition
(lem-pc-module-pullback-identity-composition), gives the pullback formula. The
pulled-back universal family specifies the dual map and its point formula.
4. First-variable biadditivity of the Poincare family gives additive duality.
The tensor universal property extends it rationally and extends composition
bilinearly, with exactly the displayed pure-tensor formulas.
5. By lem-sfb-ample-line-polarization-isogeny, phi_L is an isogeny. The quasi-inverse
in lem-sfb-simple-isogeny-decomposition divided by its positive integer gives mu.
6. Swap the two factors of the normalized difference of L. Commutativity and
lem-sfb-abelian-poincare-biduality give lambda-dual composed with the bidual
identification equal to lambda; L itself need not be symmetric.
7. Define dagger as mu composed with rational duality composed with lambda.
Additivity, rational linearity and the two inverse identities prove reversal and
fixing of rational scalars.
8. Dualize the inverse identities, then use naturality of biduality and step 6.
Cancellation gives dagger squared equal to the identity.
9. The integral Hom group is torsion-free by lem-sfb-abelian-hom-finite-free.
Apply lem-trf-torsionfree-rationalization-injective to deduce phi_N = 0 from its
vanishing rational image.
10. Its normalized difference is therefore trivial. Pull back along x ↦ (x,-x).
The constant identity line is trivial over k; symmetry of N cancels the remaining
factors to give N tensor N isomorphic to O_A. This works in characteristic two
and in dimension zero, and all isomorphisms are over k. -/
theorem IsAbelianVariety.polarization_calculus_over_field
    {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety A] :
    ∃ c : ∀ (B C E : Over (Spec (.of k)))
        [GrpObj B] [GrpObj C] [GrpObj E]
        [IsAbelianVariety B] [IsAbelianVariety C] [IsAbelianVariety E],
        abelianRationalHom B C →ₗ[ℚ]
          abelianRationalHom C E →ₗ[ℚ] abelianRationalHom B E,
      (∀ (B C E : Over (Spec (.of k)))
        [GrpObj B] [GrpObj C] [GrpObj E]
        [IsAbelianVariety B] [IsAbelianVariety C] [IsAbelianVariety E]
        (r s : ℚ) (f : abelianHom B C) (g : abelianHom C E),
          c B C E (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) = (r * s) ⊗ₜ[ℤ] abelianHomComp f g) ∧
      ∃ (D : AbelianDualPoincareDatum A)
        (φ : (N : A.left.Modules) → N.IsInvertible → abelianHom A D.dual)
        (d : ∀ (B C : Over (Spec (.of k))) [GrpObj B] [GrpObj C]
          [IsAbelianVariety B] [IsAbelianVariety C]
          (DB : AbelianDualPoincareDatum B) (DC : AbelianDualPoincareDatum C),
          abelianHom B C →+ abelianHom DC.dual DB.dual)
        (dQ : ∀ (B C : Over (Spec (.of k))) [GrpObj B] [GrpObj C]
          [IsAbelianVariety B] [IsAbelianVariety C]
          (DB : AbelianDualPoincareDatum B) (DC : AbelianDualPoincareDatum C),
          abelianRationalHom B C →ₗ[ℚ] abelianRationalHom DC.dual DB.dual),
        (∀ (N : A.left.Modules) (hN : N.IsInvertible) (f : A ⟶ D.dual),
          ClassifiesAbelianDifference D N f ↔ f = abelianHomMap (φ N hN)) ∧
        (∀ (N : A.left.Modules) (hN : N.IsInvertible)
          (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s : Spec (.of Ω) ⟶ Spec (.of k)) (x : Over.mk s ⟶ A),
          Nonempty
            ((tensorPullback (A ◁ (x ≫ abelianHomMap (φ N hN))).left).obj D.poincare ≅
              (tensorPullback
                ((fst A (Over.mk s) * (snd A (Over.mk s) ≫ x)).left)).obj N ⊗
                (tensorPullback (fst A (Over.mk s)).left).obj (Scheme.Modules.dual N))) ∧
        (∀ (N P : A.left.Modules) [hN : N.IsInvertible] [hP : P.IsInvertible],
          φ (N ⊗ P) inferInstance = φ N hN + φ P hP) ∧
        φ (𝟙_ A.left.Modules) inferInstance = 0 ∧
        (∀ (B C : Over (Spec (.of k))) [GrpObj B] [GrpObj C]
          [IsAbelianVariety B] [IsAbelianVariety C]
          (DB : AbelianDualPoincareDatum B) (DC : AbelianDualPoincareDatum C)
          (f : abelianHom B C) (g : DC.dual ⟶ DB.dual),
          Nonempty
            ((Scheme.Modules.pullback (abelianHomMap f ▷ DC.dual).left).obj DC.poincare ≅
              (Scheme.Modules.pullback (B ◁ g).left).obj DB.poincare) ↔
            g = abelianHomMap (d B C DB DC f)) ∧
        (∀ (B C : Over (Spec (.of k))) [GrpObj B] [GrpObj C]
          [IsAbelianVariety B] [IsAbelianVariety C]
          (DB : AbelianDualPoincareDatum B) (DC : AbelianDualPoincareDatum C)
          (f : abelianHom B C) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s : Spec (.of Ω) ⟶ Spec (.of k)) (q : Over.mk s ⟶ DC.dual),
          Nonempty
            ((tensorPullback (B ◁ (q ≫ abelianHomMap (d B C DB DC f))).left).obj
                DB.poincare ≅
              (tensorPullback (abelianHomMap f ▷ Over.mk s).left).obj
                ((tensorPullback (C ◁ q).left).obj DC.poincare))) ∧
        (∀ (B C : Over (Spec (.of k))) [GrpObj B] [GrpObj C]
          [IsAbelianVariety B] [IsAbelianVariety C]
          (DB : AbelianDualPoincareDatum B) (DC : AbelianDualPoincareDatum C)
          (r : ℚ) (f : abelianHom B C),
          dQ B C DB DC (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] d B C DB DC f) ∧
        (∀ (N : A.left.Modules) [hN : N.IsInvertible] (b : abelianHom A A),
          φ ((Scheme.Modules.pullback (abelianHomMap b).left).obj N) inferInstance =
            abelianHomComp (abelianHomComp b (φ N hN)) (d A A D D b)) ∧
        (∀ (L : A.left.Modules) [hL : L.IsInvertible], IsAmple A.left L →
          ∃ (invLambda : abelianRationalHom D.dual A)
            (dagger : abelianRationalHom A A →ₗ[ℚ] abelianRationalHom A A),
            c A D.dual A (abelianHomToRational (φ L hL)) invLambda =
              abelianHomToRational (abelianHomId A) ∧
            c D.dual A D.dual invLambda (abelianHomToRational (φ L hL)) =
              abelianHomToRational (abelianHomId D.dual) ∧
            (∀ v : abelianRationalHom A A,
              dagger v = c A D.dual A
                (c A D.dual D.dual (abelianHomToRational (φ L hL)) (dQ A A D D v)) invLambda) ∧
            Function.Involutive dagger ∧
            (∀ v w : abelianRationalHom A A,
              dagger (c A A A v w) = c A A A (dagger w) (dagger v)) ∧
            ∀ r : ℚ, dagger (r • abelianHomToRational (abelianHomId A)) =
              r • abelianHomToRational (abelianHomId A)) ∧
        ∀ (N : A.left.Modules) (hN : N.IsInvertible),
          Nonempty ((tensorPullback (ι[A]).left).obj N ≅ N) →
          abelianHomToRational (φ N hN) = 0 →
          Nonempty (N.tensorPow 2 ≅ 𝟙_ A.left.Modules) := by
  sorry

end AlgebraicGeometry
