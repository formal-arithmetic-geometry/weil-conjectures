/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.FiniteConstantLocalModelTree
import Sheaf.Paper.SupportedThreeTermScalarCd
import Sheaf.Paper.QcqsTreeFiniteExtensions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# The affine cohomological bound for finite constructible complex hearts

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph, agent coefficient-transfer
obligation (blueprint: lem-sfb-finite-constructible-complex-heart-cd).
Compare Hemo--Richarz--Scholbach, Section 8, (8.1), Lemmas 5.3 and 8.6, and Proposition 8.2.
An exact reference in the stated coefficient and geometric generality remains WANTED.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The zeroth cohomology module of a finite complex of finite constant scalar-model
constructible modules has ordinary module-derived cohomology zero above `d + 2` on
all affine pro-etale objects, under the uniform affine etale local torsion bound `d`.
The maps of the complex are arbitrary module-sheaf maps. No constructibility or
completeness of its cohomology module is assumed.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
agent coefficient-transfer obligation; compare Hemo--Richarz--Scholbach, Section 8,
(8.1), Lemmas 5.3 and 8.6, and Proposition 8.2. Exact full-generality reference WANTED.
(blueprint: lem-sfb-finite-constructible-complex-heart-cd)

Proof:
1. Apply the common finite local-model tree to the three terms of `K.sc 0`.
   Their constructibility follows from the termwise hypothesis. Only these three
   terms are used; the finite-support hypothesis is unnecessary for this argument.
2. On each leaf pull back this short complex. Its terms have finite constant
   local models. Apply the supported three-term estimate, using the original X
   and its given uniform torsion bound. Exact pullback commutes with short-complex
   homology. Extend this homology comparison along the support path, pull it to U,
   and apply derived sections and degree-q homology to obtain leaf vanishing.
3. The property that degree-q derived section cohomology vanishes is closed under
   isomorphisms and distinguished-triangle extensions: derived sections is
   triangulated, and degree-q homology sends a distinguished triangle to an exact
   same-degree sequence. Zero outer objects force its middle object to be zero.
4. The coefficient-independent tree reconstruction theorem expresses the root
   module, after exact pullback to U and placement in degree zero, as a finite
   extension of its supported leaf restrictions. Closure under finite extensions
   proves the assertion with the same bound d + 2, including empty schemes and
   zero complexes and coefficients. The reconstruction theorem reuses the proved
   general helper in QcqsLatticeTreeReconstruction, with no lattice assumption.
-/
theorem finite_constructible_complex_heart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (hfinite : ∃ s : Finset ℤ, ∀ n : ℤ, n ∉ s → IsZero (K.X n))
    (hconstructible : ∀ n : ℤ, IsConstantModelConstructible Λ X (K.X n))
    (U : X.ProEt) [IsAffine U.left] (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((condensedModuleSections Λ U.left).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar Λ U.hom).obj (K.homology 0))))) := by
  obtain ⟨s, hs⟩ := hfinite
  clear s hs
  let F := CondensedRing.upperStar Λ U.hom
  let H := (condensedModuleSections Λ U.left).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor Ab.{u + 1} q
  let P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj Λ U.left))) := fun C ↦ IsZero (H.obj C)
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ h.of_iso (H.mapIso e.symm)⟩
  have : P.IsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    (H.map_distinguished_exact T hT).isZero_of_both_zeros
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  let M : Fin 3 → _ := ![(K.sc 0).X₁, (K.sc 0).X₂, (K.sc 0).X₃]
  have hM : ∀ a : Fin 3, IsConstantModelConstructible Λ X (M a) := by
    intro a
    fin_cases a <;> exact hconstructible _
  obtain ⟨tree, htree⟩ := exists_finite_constant_local_model_tree Λ X 3 M hM
  have hleaf : ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf →
      P ((DerivedCategory.singleFunctor _ 0).obj
        (F.obj ((p.extension Λ).obj
          ((CondensedRing.upperStar Λ p.toRoot).obj (K.homology 0))))) := by
    intro S p hp
    let G := CondensedRing.upperStar Λ p.toRoot
    let L := (K.sc 0).map G
    have h₁ := htree S p hp 0
    have h₂ := htree S p hp 1
    have h₃ := htree S p hp 2
    have hv := supported_three_term_scalar_cohomology_vanishes ℓ Λ hΛ X d hcd
      tree p L h₁ h₂ h₃ U q hq
    let e := (K.sc 0).mapHomologyIso G
    change IsZero (H.obj ((DerivedCategory.singleFunctor _ 0).obj
      (F.obj ((p.extension Λ).obj (G.obj (K.homology 0))))))
    change IsZero (H.obj ((DerivedCategory.singleFunctor _ 0).obj
      (F.obj ((p.extension Λ).obj L.homology)))) at hv
    exact hv.of_iso (H.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (F.mapIso ((p.extension Λ).mapIso e)))).symm
  obtain ⟨n, hn⟩ := qcqs_tree_finite_extensions Λ tree F P (K.homology 0) hleaf
  have hz := P.extensionProductIter_le_of_isTriangulatedClosed₂ (fun _ h ↦ h) n _ hn
  dsimp only [P, H, F, Functor.comp_obj] at hz
  exact hz

end AlgebraicGeometry.ProEtale
