/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests
public import Sheaf.TraceFormula.EtaleGradedModuleAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.SchemeProjVeroneseQuotientFunctor
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-! # Quotient closed immersions of relative Proj over algebraic spaces

Source: Stacks Project, spaces-divisors.tex, Tags 085F, 085H (1)-(2), and 085G;
constructions.tex, Tag 07ZI
(blueprint: lem-sfb-space-relative-proj-quotient-closed-immersion).

The conclusion is a system of uniquely specified arrows for the existing scheme-test
realizations. The test coefficient map is fixed by its action on each homogeneous section
of the actual tensor pullback, not by an arbitrary map of graded algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The existing induced scheme relative-Proj map, regarded as a morphism over S.
Source: Stacks, Constructions, 07ZI and spaces-divisors, 085F
(blueprint: lem-sfb-space-relative-proj-quotient-closed-immersion). -/
def spaceProjQuotientSchemeMap (W : Over S) {A B : W.left.GradedAlgebraData}
    (f : A ⟶ B) (hf : ∀ V, Function.Surjective (f.app V)) :
    spaceProjScheme W B ⟶ spaceProjScheme W A :=
  Over.homMk (Scheme.GradedAlgebraData.relProjMap f
    (Scheme.GradedAlgebraData.irrelevantLE_of_surjective f hf)) (by
      change Scheme.GradedAlgebraData.relProjMap f _ ≫ (A.relProjHom ≫ W.hom) =
        B.relProjHom ≫ W.hom
      rw [← Category.assoc, Scheme.GradedAlgebraData.relProjMap_relProjHom])

/-- The scheme-test characterization of the quotient arrow. Surjectivity is sheaf
surjectivity (Epi); affine-section surjectivity is separately asserted for the Zariski
quasi-coherent graded algebra. The equation with compare is precisely the transported
base-change map, since the two comparison squares are cartesian.
Source: Stacks, spaces-divisors, 085F and 085H; Constructions, 07ZI
(blueprint: lem-sfb-space-relative-proj-quotient-closed-immersion). -/
def IsSpaceProjQuotientMap (C : SpaceProjCoefficients S) (R : SpaceProjSystem C)
    {X : AlgebraicSpace S} {A B : SpaceProjInput X}
    (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
    (r : (R.realization B).space ⟶ (R.realization A).space) : Prop :=
  r ≫ (R.realization A).projection = (R.realization B).projection ∧
    ∀ (W : Over S) (g : schemeSpace W ⟶ X),
      (∀ n : ℕ, Epi ((moduleTensorPullback g).map (φ.degree n))) ∧
      ∃ (f : (C.scheme A W g).affine ⟶ (C.scheme B W g).affine)
        (hf : ∀ V, Function.Surjective (f.app V)),
        (∀ (V : W.left.affineOpens) (n : ℕ) (s : (C.scheme A W g).affine.grading V n),
          (C.scheme B W g).sections V n ⟨f.app V s, (f.app V).map_mem s.property⟩ =
            ((evaluationZariskiRestriction W).map
              ((moduleTensorPullback g).map (φ.degree n))).val.app (op V.1)
                ((C.scheme A W g).sections V n s)) ∧
        (R.realization B).compare W g ≫ r.hom.hom =
          yoneda.map (spaceProjQuotientSchemeMap W f hf) ≫ (R.realization A).compare W g

/-- The conclusion for every graded surjection, including uniqueness, all scheme base
changes as closed immersions, identities, and composition. The last two fields express
identity/composition through their homogeneous module maps, avoiding a second definition
of homogeneous algebra homomorphisms.
Source: Stacks, spaces-divisors, 085F, 085H (1)-(2), and 085G
(blueprint: lem-sfb-space-relative-proj-quotient-closed-immersion). -/
structure SpaceProjQuotientSystem (C : SpaceProjCoefficients S) (R : SpaceProjSystem C) where
  map {X : AlgebraicSpace S} {A B : SpaceProjInput X}
      (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n)) :
    (R.realization B).space ⟶ (R.realization A).space
  specification {X : AlgebraicSpace S} {A B : SpaceProjInput X}
      (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n)) : IsSpaceProjQuotientMap C R φ (map φ hφ)
  unique {X : AlgebraicSpace S} {A B : SpaceProjInput X}
      (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n))
      (r : (R.realization B).space ⟶ (R.realization A).space) :
    IsSpaceProjQuotientMap C R φ r → r = map φ hφ
  closedImmersion {X : AlgebraicSpace S} {A B : SpaceProjInput X}
      (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n)) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (map φ hφ).hom.hom
  identity {X : AlgebraicSpace S} (A : SpaceProjInput X)
      (φ : EtaleGradedModuleAlgebra.Hom A.algebra A.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n)) (h : ∀ n : ℕ, φ.degree n = 𝟙 (A.piece n)) :
    map φ hφ = 𝟙 (R.realization A).space
  composition {X : AlgebraicSpace S} {A B D : SpaceProjInput X}
      (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
      (ψ : EtaleGradedModuleAlgebra.Hom B.algebra D.algebra)
      (χ : EtaleGradedModuleAlgebra.Hom A.algebra D.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n)) (hψ : ∀ n : ℕ, Epi (ψ.degree n))
      (hχ : ∀ n : ℕ, Epi (χ.degree n))
      (h : ∀ n : ℕ, χ.degree n = φ.degree n ≫ ψ.degree n) :
    map χ hχ = map ψ hψ ≫ map φ hφ

/-- A degreewise surjection induces the unique quotient closed immersion of relative Proj
spaces, characterized on every scheme test by the ordinary induced scheme-Proj map.
It respects identity and composition, including empty Proj spaces.

Source: Stacks Project, spaces-divisors.tex, Tags 085F, 085H (1)-(2), and 085G;
constructions.tex, Tag 07ZI
(blueprint: lem-sfb-space-relative-proj-quotient-closed-immersion).

Proof:
1. The tensor adjunction (def-trf-space-etale-module-functors) and preservation of colimits
   (lem-weil-pbc-left-adjoint-preserves-colimits) preserve the cokernel presentation of
   each surjection in the abelian module-sheaf category (def-weil-sheaf-of-modules-category).
   Pullback preserves quasi-coherence (lem-sfb-space-module-pullback-quasicoherent), and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence transports the cokernels and
   homogeneous operations. The normalized compositor def-sfb-space-module-tensor-composition
   identifies successive pullbacks, naturally in each homogeneous map.
2. In lem-sfb-scheme-proj-veronese-quotient-functor send a B-quotient (d,f,L,psi) to
   (d,f,L,psi composed with f-star phi). Degree-one surjectivity is preserved; common-power
   witnesses remain witnesses after precomposition. The compositor def-pc-module-pullback
   identifies restriction of this formula with its formula after pullback. Extend from
   quasi-compact tests to compatible families on quasi-compact opens. Yoneda
   (lem-pc-yoneda) gives the unique representing scheme morphism.
3. On an affine base, lem-sfb-space-qcoh-affine-chart-calculus gives surjections on sections.
   For b of positive degree lift b to a of that degree. The opens D_+(b) cover by
   prop-nagata-proj-standard-open. The canonical twisting quotient
   (def-weil-pbc-proj-twisting-sheaf) makes b a basis of O(deg b) on this open. Thus the
   induced comorphism is x/a^m mapped to phi(x)/b^m, the homogeneous localization map
   (def-nagata-homogeneous-localization-degree-zero). It equals the ordinary Proj map;
   prop-nagata-relative-proj-functoriality makes it a closed immersion.
4. Pulling back psi composed with f-star phi commutes with arbitrary further scheme tests,
   by naturality of def-pc-module-pullback. Hence the representing maps commute with
   arbitrary scheme base change and the algebra comparisons of
   lem-sfb-space-relative-proj-scheme-tests, without flatness assumptions.
5. For q in P_X(B)(T), apply the scheme map over f = p_B q to the section (id_T,q) of
   T times_X P_X(B), and project its image to P_X(A). Step 4 makes this natural in T.
   Thus it is a morphism of algebraic spaces (def-trf-algebraic-space), over X, and its
   base change is the required scheme map. Evaluating any candidate on (id_T,q) proves
   uniqueness on all sections, hence uniqueness of the morphism.
6. Pull an etale scheme atlas U of X back to P_X(A). It is a surjective etale scheme cover
   by lem-trf-space-fibre-products-etale-covers and the scheme-test comparisons. The
   pulled-back quotient morphism is the closed immersion of step 3. The locality theorem
   lem-sfb-space-closed-immersion-atlas-locality proves representability and closed
   immersion on every scheme test of P_X(A). On an affine etale chart this is exactly
   Proj(B(U)) to Proj(A(U)), using the direct sum of the component sections.
7. Associativity of precomposition and precomposition by identity give composition and
   identity on quotient data, hence on scheme maps and the sectionwise space map.
   No point is selected: empty sources have their unique map; if the target Proj is
   empty the scheme-test construction forces the source to be empty too. -/
theorem space_relativeProj_quotient_closedImmersion (C : SpaceProjCoefficients S)
    (R : SpaceProjSystem C) : Nonempty (SpaceProjQuotientSystem C R) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
