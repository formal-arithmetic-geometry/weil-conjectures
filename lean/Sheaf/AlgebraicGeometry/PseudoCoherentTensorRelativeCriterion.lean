module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorPreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded

/-! # Pseudo-coherent tensor tests imply relative pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 0CSL,
`lemma-characterize-pseudo-coherent`
(blueprint: lem-sfb-pseudocoherent-tensor-relative-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u w wΓ wA

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- If every pseudo-coherent tensor test has pseudo-coherent derived global sections
over A, a quasi-coherent derived object on a separated finitely presented A-scheme
is pseudo-coherent relative to Spec A. No flatness, properness or Noetherian assumption
is imposed. The section functor is the existing affine derived section construction,
spelled out to retain independent localization universes for the two module categories.
Source: Stacks Project, More on Morphisms, Tag 0CSL,
`lemma-characterize-pseudo-coherent`
(blueprint: lem-sfb-pseudocoherent-tensor-relative-criterion).

Proof:
1. For each point x choose the derived Chow neighbourhood U, n, V, Z, z, E
(lem-sfb-derived-chow-neighbourhood). Set T = X ×_A P with P = projective n-space,
and write p : T → X and q : T → P for its projections.
2. Projective-space properness and base change make p proper. The standard affine
charts are polynomial projections, so p is flat and locally finitely presented;
it is therefore of finite presentation. The same chart calculation makes V → Spec A
flat and locally finitely presented. Separated finite-type base change makes q qcqs.
3. Put F = Rq_*(Lp^*K ⊗ E). Pseudo-coherent complexes have quasi-coherent cohomology;
affine-component pullback and tensor preservation and qcqs direct-image preservation
show that F has quasi-coherent cohomology. K-flat resolutions compute the tensor.
4. For d = 0,...,n put B_d = E ⊗ Lq^*O_P(d) and G_d = Rp_*B_d. The pulled-back
invertible twist is locally free of rank one, so B_d is pseudo-coherent. Flat proper
finitely presented direct-image preservation makes G_d pseudo-coherent on X.
5. The two qcqs projection formulas and composition of derived direct images identify
RΓ(P,F ⊗ O_P(d)) with RΓ(T,Lp^*K ⊗ B_d), and then with RΓ(X,K ⊗ G_d).
Associativity and symmetry put the factors in the test order. The hypothesis makes
this object pseudo-coherent over A; invariance under isomorphism follows by composing
its bounded-above finite-free representative with these isomorphisms. The finite-twist
projective-space criterion makes F pseudo-coherent on P.
6. The graph-kernel restriction comparison identifies F restricted to V with
Rj_*(K restricted to U), for the closed immersion j : U → V. Restriction preserves
pseudo-coherence. Since V → Spec A is flat and locally finitely presented, the
flat-ambient criterion makes K restricted to U relatively pseudo-coherent over A.
These neighbourhoods cover X. Relative pseudo-coherence is local on the source
(lem-sfb-relative-pseudocoherence-local-on-source), proving the conclusion. -/
theorem isPseudoCoherentRelativeTo_of_pseudoCoherent_tensor_tests
    (A : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec A)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{wΓ}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (hTests : ∀ E : schemeDerivedCategory X, Scheme.IsPseudoCoherent X E →
      DerivedCategory.IsPseudoCoherent
        ((schemeDerivedGlobalSections X ⋙
          (affineGlobalSectionsRestriction f).mapDerivedCategory).obj (E ⊗ K))) :
    Scheme.IsPseudoCoherentRelativeTo f K := by
  sorry

end AlgebraicGeometry
