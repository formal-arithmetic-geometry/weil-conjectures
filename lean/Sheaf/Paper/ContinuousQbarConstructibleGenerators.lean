/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Paper.FiniteModelStratumFiltration
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels
import Sheaf.Paper.TAdmissibleDualizableTruncations
import WeilConjectures.ConstructibleSheaf.Refinement
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Finite generation for all-continuous algebraic-closure coefficients

Source: blueprint main-20261015, sk-thm-sf-pf-field-tensor.proof.md, (1),
opening lisse-generator reduction; Hemo--Richarz--Scholbach, Theorems 4.13 and 6.2(2)
(blueprint: lem-sfb-continuous-qbar-constructible-generators).

The continuous coefficient ring is the full continuous-map ring. Its existing
`continuousCoefficientRingObj` presentation agrees definitionally with
`continuousMapRingObjOfUniverse` at the common scheme/coefficient universe.
The two auxiliary predicates spell out the generators and finite construction expressions
of this node; neither closes under retracts, coproducts, or completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Ω : Type u) [NormedField Ω]

/-- A degree-zero locally closed extension of a lisse module, up to isomorphism.
The quantified open-then-closed factorization gives exactly `a_! = i_* j_!`;
constructibility is imposed on the image of the composite immersion.
Source: blueprint sk-thm-sf-pf-field-tensor.proof.md, (1), opening reduction
(blueprint: lem-sfb-continuous-qbar-constructible-generators). -/
def continuousQbarLisseGenerator (X : Scheme.{u}) : ObjectProperty
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) X))) := fun K ↦
  ∃ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
    (_hj : IsOpenImmersion j) (_hi : IsClosedImmersion i),
    Topology.IsConstructible (Set.range (j ≫ i)) ∧
    ∃ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) S),
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) L ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj
        (((CondensedRing.openImmersionLowerShriek
          (Profinite.continuousCoefficientRingObj Ω) j) ⋙
            CondensedRing.lowerStar (Profinite.continuousCoefficientRingObj Ω) i).obj L))

/-- A finite list of zero objects, generators, shifts of earlier entries, and extensions
with earlier ends, whose last entry is isomorphic to the specified complex.
Source: blueprint sk-thm-sf-pf-field-tensor.proof.md, (1), finite devissage expansion
(blueprint: lem-sfb-continuous-qbar-constructible-generators). -/
def continuousQbarFiniteConstruction (X : Scheme.{u}) : ObjectProperty
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) X))) := fun K ↦
  ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) X))),
    Nonempty (F (Fin.last N) ≅ K) ∧ ∀ r : Fin (N + 1),
      IsZero (F r) ∨ continuousQbarLisseGenerator Ω X (F r) ∨
      (∃ (i : Fin (N + 1)) (n : ℤ), i < r ∧ Nonempty (F r ≅ (F i)⟦n⟧)) ∨
      (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
        ∃ (f : F i ⟶ F r) (g : F r ⟶ F j) (h : F j ⟶ (F i)⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang _)

/-- Bounded constructible complexes are precisely the smallest full replete triangulated
subcategory containing the locally closed lisse extensions, equivalently precisely the
finite constructions just specified. The normed algebra structure says that the norm
on the algebraic closure extends the ell-adic norm; no completeness is assumed on Ω.

Source: blueprint sk-thm-sf-pf-field-tensor.proof.md, (1), opening reduction, and
Hemo--Richarz--Scholbach, Definition 6.1 and Theorems 4.13 and 6.2(2)
(blueprint: lem-sfb-continuous-qbar-constructible-generators).

Proof plan, following the twelve steps of the node:
1. The scalar ring is Ω. Finite presentations over this field are finite free, so the
finite constant local models of sk-def-sfb-constructible are exactly the lisse modules.
The Noetherian-space lemma and finite-irreducible-components lemma apply to every stratum.
2. Ideals over the field are finitely presented; finitely presented modules have
length-zero finite projective resolutions. Every C(P,Ω) is Ω-flat. Thus the ring is
t-admissible in lem-zl-t-admissible-dualizable-truncations, without finite-field descent.
3. By lem-zl-condensed-dualizable-local-perfect-models, lisse degree-zero objects and
cones between them are dualizable. The cone has kernel and cokernel cohomology in
degrees -1 and 0. Step 2 makes both finite constant local models, hence lisse.
4. Trivialize the two ends of a short exact sequence of lisse modules on a common
cover. The free-epi-local-splitting lemma splits the quotient after a further cover;
the middle term is then their finite free direct sum, including rank-zero ends.
5. Use lemma-constructible-common-refinement, exact pullback and lem-sfb-alpha-iso to
restrict kernels, cokernels and extensions to common strata. Steps 3 and 4 imply that
the constructible modules form an isomorphism-closed weak Serre class containing zero.
6. Apply lem-sbc-cohomology-in-weak-serre-subcategory, bounded version, to get the full
replete triangulated subcategory of bounded constructible cohomology complexes.
7. The proetale-ringed-open-closed identities restrict i_*j_!L to L, zero and zero on
S, Z minus S and X minus Z. The complementary opens are quasi-compact by the
Noetherian-space compact-subsets lemma. Exactness puts the generator in degree zero.
8. lem-sfb-finite-model-stratum-filtration gives a finite filtration of every
constructible sheaf with quotients v_!t_*L, with L a finite constant local model.
9. Each vt is quasi-compact, so the immersion-factorization lemma gives an open-then-
closed factorization. lem-sfb-locally-closed-extension-coherence and lem-sfb-alpha-iso
identify that quotient with the stated i_*j_!L, without changing coefficients.
10. lem-weil-pbc-complex-ses-triangle puts each degree-zero filtration step in a
distinguished triangle with the previous step and its quotient. Induct from zero.
11. For cohomological bounds a,b, use truncation cohomology and the truncation triangles
to build tau_le b K from zero through the finitely many H^q(K)[-q], a ≤ q ≤ b.
Localization identifies the initial truncation with zero and the last with K.
12. Steps 7 and 11 give exactly the finite construction predicate. Induction on its
finite list gives inclusion in every full replete triangulated subcategory containing
the generators. Step 6 supplies the reverse inclusion and minimality. An acyclic K
is zero up to isomorphism; on the empty scheme the zero construction suffices. -/
theorem continuousQbar_constructible_generators (ℓ : ℕ) [Fact ℓ.Prime]
    [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj Ω) X
      ).IsClosedUnderIsomorphisms ∧
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj Ω) X
      ).IsTriangulated ∧
    (∀ K, continuousQbarLisseGenerator Ω X K →
      constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj Ω) X K) ∧
    (∀ P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) X))),
      P.IsClosedUnderIsomorphisms → P.IsTriangulated →
      (∀ K, continuousQbarLisseGenerator Ω X K → P K) →
      ∀ K, constantModelBoundedConstructible
        (Profinite.continuousCoefficientRingObj Ω) X K → P K) ∧
    (∀ K, constantModelBoundedConstructible
      (Profinite.continuousCoefficientRingObj Ω) X K ↔ continuousQbarFiniteConstruction Ω X K) := by
  sorry

end AlgebraicGeometry.ProEtale
