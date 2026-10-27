module

public import Sheaf.AlgebraicGeometry.StackVersalFiniteResidueExtension
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.FormalModuliQuotient
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra

/-! # Smooth atlas lifts and versal completed local rings

Source: Stacks Project, stacks-geometry.tex, Tags 0DQZ and 0DZS;
stacks-morphisms.tex, Tag 0DZR (blueprint: lem-sfb-stack-atlas-versal-completion).

The completion is identified with the actual maximal-ideal completion of the stalk.
The arrows to the atlas object specify its induced formal object, including all
markings and transition comparisons. Positive levels are indexed by n + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.StackVersal

/-- The canonical map from the spectrum of the identified completion to the scheme.
The ring isomorphism is used inversely because Spec is contravariant.
Source: Stacks, Tag 0DQZ (blueprint: lem-sfb-stack-atlas-versal-completion). -/
def completionToScheme {X : Scheme.{u}} (z : X) (C : CommRingCat.{u})
    (e : C ≃+* AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z)) : Spec C ⟶ X :=
  Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk z)
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
        (X.presheaf.stalk z)))) ≫ X.fromSpecStalk z

/-- A finite common-field atlas lift, its induced versal completion, and smoothness
at that lift. The arrows from the formal levels to the atlas object retain the canonical
atlas pullback, rather than asserting only existence of an unrelated versal object.
Source: Stacks, Tags 0DQZ, 0DZS and 0DZR
(blueprint: lem-sfb-stack-atlas-versal-completion).

Proof:
1. The representable diagonal makes the atlas representable by spaces
(lem-sfb-stack-diagonal-space-source-representability). Base change along x using
lem-sfb-stack-chartwise-smooth-etale-calculus. Etale sections of this smooth
surjection (lem-sfb-smooth-space-cover-etale-sections) have a finite type point
(lem-sfb-finite-type-points-detect-open). Its residue field l is finite over k by
lem-sfb-finite-type-field-point-characterization and the finite-type composition
clause of lem-weil-pbc-proper-fp-permanence.
2. Factor the resulting field-valued map to U through its image u and kappa(u), by
lem-weil-pbc-morphism-from-spec-field. Both kappa(u) and l are finite over the
base residue field, and l is finite over kappa(u). Choose an affine neighbourhood
with finite type coordinate R-algebra by def-weil-finite-type-morphism.
3. Apply lem-sfb-scheme-completion-artinian-points. Its natural Artinian-point
bijection gives the complete Noetherian local ring, its canonical residue marking,
and the tower pulled back from p. It also identifies evaluations of this tower
with the maps Spec A to U reducing to u.
4. Factor each surjection of test algebras into small extensions by
lem-sfb-artin-local-test-algebra and def-sfb-artin-deformation-test-category.
Their kernels have square zero. The given deformation and prescribed marked
isomorphism give a section of the smooth space U times_X Spec A' over Spec A.
Apply lem-sfb-smooth-space-affine-infinitesimal-lift successively, retaining the
whole section and its isomorphism component. The natural bijection of step 3
returns a local map of the completion lifting the original one, with exactly the
prescribed isomorphism. An isomorphism of test rings uses its inverse directly.
5. Use lem-sfb-stack-maximal-smooth-open for the largest smooth open. Smoothness
of its structural map is independent of the smooth atlas: compare two atlases
through their space fibre product using lem-sfb-stack-chartwise-smooth-etale-calculus
and lem-sfb-space-smooth-source-point-locality.
6. If x lies in this open, the common-field identification and the one-point
open-pullback argument put u in its atlas pullback; step 5 gives smoothness near u.
Conversely a smooth open neighbourhood of u has an open stack image by
lem-sfb-smooth-atlas-open-image. Its atlas is smooth over R, so maximality puts
this image in the smooth open. The common-field isomorphism and the same one-point
open-pullback argument descend membership to x.
-/
theorem exists_atlas_versal_completion
    (R k : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field k] [Algebra R k] [Algebra (IsLocalRing.ResidueField R) k]
    [IsScalarTower R (IsLocalRing.ResidueField R) k]
    [Module.Finite (IsLocalRing.ResidueField R) k]
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (T : Over (Spec (.of R)))
      (a : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      IsSmoothModuliAtlas F T a ∧ LocallyOfFiniteType T.hom)
    (x : Object F k) (U : Over (Spec (.of R)))
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (hp : IsSmoothModuliAtlas F U p) :
    ∃ Ω : OpenModuliSubstack F, IsSmoothModuliStack Ω.category ∧
      (∀ W : OpenModuliSubstack F, IsSmoothModuliStack W.category → W.IsContainedIn Ω) ∧
      ∃ (V : U.left.Opens) (B : CommAlgCat.{u} R) (eV : Spec (.of B) ≅ V.toScheme),
        Algebra.FiniteType R B ∧
        eV.hom ≫ V.ι ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
        ∃ (z : U.left) (hz : z ∈ V)
          (_ : Algebra R (U.left.residueField z))
          (_ : Algebra (IsLocalRing.ResidueField R) (U.left.residueField z))
          (_ : IsScalarTower R (IsLocalRing.ResidueField R) (U.left.residueField z)),
          Module.Finite (IsLocalRing.ResidueField R) (U.left.residueField z) ∧
          ∃ (j₀ : affine (R := R) (U.left.residueField z) ⟶ U),
            j₀.left = U.left.fromSpecResidueField z ∧
            ∃ (x₁ : Object F (U.left.residueField z)) (s : x₁.val ⟶ (moduliChartPoint p).val),
              F.p.IsHomLift j₀ s ∧
              ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra R l)
                (_ : IsScalarTower R k l), Module.Finite k l ∧
                ∃ (i : U.left.residueField z →ₐ[R] l), i.toRingHom.Finite ∧
                  ∃ (xl : Object F l)
                    (_ : Arrow (IsScalarTower.toAlgHom R k l) xl x)
                    (_ : Arrow i xl x₁),
                    ∃ (C : CompleteLocalAlgebra R (U.left.residueField z))
                      (e : C.ring ≃+* AdicCompletion
                        (IsLocalRing.maximalIdeal (U.left.presheaf.stalk z))
                        (U.left.presheaf.stalk z))
                      (j : affine (R := R) C.ring ⟶ U),
                      j.left = completionToScheme z (.of C.ring) e ∧
                      Spec.map (CommRingCat.ofHom
                        (C.residueEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ R _)).toRingHom) ≫
                          j.left = j₀.left ∧
                      ∃ (η : FormalObject F x₁ C)
                        (a : ∀ n : ℕ, affine (R := R) (Level C n) ⟶ U)
                        (t : ∀ n : ℕ, (η.obj n).val ⟶ (moduliChartPoint p).val),
                        (∀ n : ℕ, (a n).left =
                          Spec.map (CommRingCat.ofHom
                            (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal C.ring ^
                              (n + 1))).toRingHom) ≫ j.left) ∧
                        (∀ n : ℕ, F.p.IsHomLift (a n) (t n)) ∧
                        (∀ (m n : ℕ) (h : n ≤ m),
                          (η.transition h).val ≫ t m = t n) ∧
                        (∀ n : ℕ, (η.mark n).val ≫ t n = s) ∧ η.IsVersal ∧
                        (Ω.property x.val ↔ ∃ W : V.toScheme.Opens,
                          (⟨z, hz⟩ : V) ∈ W ∧ Smooth (W.ι ≫ V.ι ≫ U.hom)) := by
  sorry

end CategoryTheory.StackVersal
