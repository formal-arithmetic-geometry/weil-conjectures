module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorBijective
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure

/-! # Eventual detection by rho tensor squares

Source: Alper, Adequate moduli spaces, Lemma 9.7.2(2), applying Property I(b)
of Seshadri, p.247, to the constant group over F[[t]] and reducing modulo t.
(blueprint: lem-sfb-rho-tensor-square-eventual-detection)

Rational representations are expressed by group-scheme maps to GL after choosing
finite bases. Invariance and equivariance are imposed after every algebra extension,
including nonreduced algebras, so these are identities of rational coactions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry

/-- The scalar-extended action of a rational representation, transported from its finite basis.
This is the actual A-linear operator on A tensor V, not an arbitrary replacement action.
Source: Milne, Algebraic Groups, Section 4a, pp.83--84; Alper, Section 9.7
(blueprint: lem-sfb-rho-tensor-square-eventual-detection). -/
def RhoSection.scalarAction {F : Type u} [Field F]
    {S : Grp (Over (Spec (.of F)))} {V : Type v} [AddCommGroup V] [Module F V]
    {I : Type u} [Fintype I] [DecidableEq I] (e : (I → F) ≃ₗ[F] V)
    (r : GeneralLinearGroup.RationalHom S.X I)
    {A : Type u} [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ S.X) :
    A ⊗[F] V ≃ₗ[A] A ⊗[F] V :=
  (Matrix.GeneralLinearGroup.toLin' (((Pi.basisFun F I).map e).baseChange A)
    (GeneralLinearGroup.homMulEquiv I F A (s ≫ r))).toLinearEquiv

/-- Every nonzero invariant vector is detected by every sufficiently large rho tensor square.
The existential bases and GL maps specify precisely the canonical left-translation
representations on the actual section subspaces. The tensor intertwining equation uses
the canonical scalar-extension comparison and the diagonal action.

Source: Alper, Lemma 9.7.2(2), Seshadri Property I(b), p.247, specialized to F via F[[t]].
(blueprint: lem-sfb-rho-tensor-square-eventual-detection)

Proof plan:
1. Apply lem-sfb-double-flag-invariant-boundary to obtain the integral separated
   double flag X, its linearized line bundle D, invariant section d, and dense stable
   open U. Its functions identify equivariantly with the right-T-invariants of F[S].
2. Project the restricted T-coaction onto its zero Laurent-monomial coefficient.
   Coassociativity makes this the trivial-weight projection, and counitality gives
   the weight decomposition. Choose a functional on that weight space taking v to 1.
   Composing gives a T-invariant functional lambda on V. This uses characters,
   not differentials, and therefore works in positive characteristic too.
3. The matrix coefficient c(u)(g)=lambda(g inverse u) is right-T-invariant,
   regular and S-equivariant on U, with c(v)=1. Verify these at universal points.
4. By lem-sc-invert-s-cohomology in degree zero, clear denominators of c on a
   finite basis. If c(e_i)=b_i/d^{n_i}, set N=max(1,n_i). For every m>=N put
   b_m(e_i)=d^{m-n_i}b_i. Thus b_m restricts to d^m c on U, for every such m.
5. Restriction of sections of D^m to U is injective since X is integral and U
   dense. Tensoring this injection with F[S] stays injective over F. Hence the
   coaction identity on U proves b_m equivariant on X. Its value on v restricts
   to d^m, which is nonzero on U, so b_m(v) is nonzero.
6. By lem-sfb-homogeneous-line-bundle-sections, sections of L^m are the actual
   W_m, using the inverse homogeneous character to get the positive exponent.
   Apply lem-sc-external-global-sections-tensor-bijective to the two factors of
   the flag variety, proper and finite type by lem-sfb-reductive-borel-pair-structure.
   This identifies W_m tensor W_m with sections of D^m equivariantly: pullback
   and multiplication commute with translation. Transport b_m through its inverse.
   Choose finite bases for the already rational left-translation actions. Their
   scalar extensions give exactly the displayed diagonal intertwining equation. -/
theorem rho_tensor_square_eventual_detection
    {F : Type u} [Field F] [IsAlgClosed F]
    (S : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F))))
    (i : T ⟶ S) (j : B ⟶ S) (k : T ⟶ B) (hTB : IsRhoBorelPair i j k)
    (aB : ModObj T.X B.X)
    (hconj : ∀ (Z : Over (Spec (.of F))) (t : Z ⟶ T.X) (b : Z ⟶ B.X),
      lift t b ≫ aB.smul = (t ≫ k.hom.hom) * b * (t ≫ k.hom.hom)⁻¹)
    (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hΦ : Φ.Nodup)
    (hpos : ∀ α, α ∈ Φ ↔ α.hom.hom ≠ 1 ∧
      @TorusCharacterTangent.weightSpace F _ T B aB α ≠ ⊥)
    (hρ : ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod)
    (hext : k ≫ ρB = ρ)
    (hrad : ∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ B),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
        l.hom.hom ≫ ρB.hom.hom = 1)
    {V : Type v} [AddCommGroup V] [Module F V]
    (I : Type u) [Fintype I] [DecidableEq I] (eV : (I → F) ≃ₗ[F] V)
    (rV : GeneralLinearGroup.RationalHom S.X I) [IsMonHom rV]
    (v : V) (hv : v ≠ 0)
    (hinv : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (s : StandardGroupSchemes.affine F A ⟶ S.X),
      RhoSection.scalarAction eV rV s (1 ⊗ₜ[F] v) = 1 ⊗ₜ[F] v) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
        (eW : (J → F) ≃ₗ[F] RhoSection.sectionModule S B j ρB m)
        (rW : GeneralLinearGroup.RationalHom S.X J) (_ : IsMonHom rW),
        (∀ (A : Type u) [CommRing A] [Algebra F A]
          (s g : StandardGroupSchemes.affine F A ⟶ S.X) (q : J),
          ∑ p, (GeneralLinearGroup.homMulEquiv J F A (s ≫ rW) : Matrix J J A) p q *
            RhoSection.evaluate g (eW (Pi.single p 1)).val =
              RhoSection.evaluate (s⁻¹ * g) (eW (Pi.single q 1)).val) ∧
        ∃ a : V →ₗ[F]
          (RhoSection.sectionModule S B j ρB m) ⊗[F] (RhoSection.sectionModule S B j ρB m),
          a v ≠ 0 ∧ ∀ (A : Type u) [CommRing A] [Algebra F A]
            (s : StandardGroupSchemes.affine F A ⟶ S.X) (x : A ⊗[F] V),
            TensorProduct.AlgebraTensorModule.distribBaseChange F A
                (RhoSection.sectionModule S B j ρB m) (RhoSection.sectionModule S B j ρB m)
                (a.baseChange A (RhoSection.scalarAction eV rV s x)) =
              TensorProduct.map (RhoSection.scalarAction eW rW s).toLinearMap
                (RhoSection.scalarAction eW rW s).toLinearMap
                (TensorProduct.AlgebraTensorModule.distribBaseChange F A
                  (RhoSection.sectionModule S B j ρB m) (RhoSection.sectionModule S B j ρB m)
                  (a.baseChange A x)) := by
  sorry

end AlgebraicGeometry
