/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.CategoryTheory.SiteCoveringsCommonRefinement
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Serre closure for constructible condensed field module sheaves

Source: upstream `ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`, Sorried input;
Bhatt--Scholze, Section 6.8, Lemma 6.8.7 and Corollary 6.8.9
(blueprint: lem-weil-pbc-condensed-constructible-serre).

The coefficients are pulled back from condensed abelian groups. Algebraic-closure sections
have image in a single finite intermediate field, as in `Profinite.padicAlgClRingObj`.
Constructibility is stratified local finite presentation, with no completeness condition.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Kernels, cokernels and extensions of constructible modules over the finite intermediate field
coefficient sheaf are constructible.
Source: upstream ProEtaleModule/DerivedCategory.lean, Sorried input; Bhatt--Scholze 6.8.7,
6.8.9 (blueprint: lem-weil-pbc-condensed-constructible-serre).

Proof: coefficient pullback comparisons identify restriction with inverse image with an
invertible coefficient map. Exact abelian inverse image and exact forgetfulness therefore
make restriction exact and preserve finite presentations and free modules. Base change
preserves weakly etale arrows and fpqc coverings, so presentation covers restrict along
arbitrary stratum immersions. Refine the two finite stratifications by their scheme fibre
products; the images are intersections (affine locally Spec of the quotient by the sum of
the two ideals), and their spaces remain noetherian. On each stratum, local finite
presentation implies pro-etale local finite freeness, using the finite-field and
algebraic-closure local-triviality lemmas respectively. Combine finitely many covers.
For a matrix between finite free modules its cokernel has a finite presentation; trivialize
this globally defined cokernel and lift its finitely many basis sections locally. This
splits the quotient of the target, and its image is presented as the cokernel of the
complement of the resulting idempotent. Trivialize that globally defined image and lift
its basis into the source. If t splits the source-to-image map p, the kernel is the
cokernel of tp on the finite free source, so is locally finitely presented. For an extension,
trivialize the outer terms and lift the quotient basis locally; this splits the extension
as their direct sum. Exact restriction identifies these constructions with the global
kernel, cokernel and middle term on each stratum. Thus the refined stratification proves
all three conclusions. Local triviality is applied only on the noetherian strata, never
on arbitrary covering schemes. Empty schemes, empty strata and rank zero require no basis
lifts and satisfy the same formulas. -/
theorem isConstructibleModuleObject_serre_padicSubfield
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicSubfieldRingObj T ℓ E)) (f : M ⟶ N),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) N →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) (kernel f) ∧
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicSubfieldRingObj T ℓ E)),
      S.ShortExact →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) S.X₁ →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) S.X₃ →
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) S.X₂) := by
  sorry

/-- Kernels, cokernels and extensions of constructible modules over the bounded-image
algebraic-closure coefficient sheaf are constructible.
Source: upstream ProEtaleModule/DerivedCategory.lean, Sorried input; Bhatt--Scholze 6.8.7,
6.8.9 (blueprint: lem-weil-pbc-condensed-constructible-serre).

Proof: coefficient pullback comparisons identify restriction with inverse image with an
invertible coefficient map. Exact abelian inverse image and exact forgetfulness therefore
make restriction exact and preserve finite presentations and free modules. Base change
preserves weakly etale arrows and fpqc coverings, so presentation covers restrict along
arbitrary stratum immersions. Refine the two finite stratifications by their scheme fibre
products; the images are intersections (affine locally Spec of the quotient by the sum of
the two ideals), and their spaces remain noetherian. On each stratum, local finite
presentation implies pro-etale local finite freeness, using the finite-field and
algebraic-closure local-triviality lemmas respectively. Combine finitely many covers.
For a matrix between finite free modules its cokernel has a finite presentation; trivialize
this globally defined cokernel and lift its finitely many basis sections locally. This
splits the quotient of the target, and its image is presented as the cokernel of the
complement of the resulting idempotent. Trivialize that globally defined image and lift
its basis into the source. If t splits the source-to-image map p, the kernel is the
cokernel of tp on the finite free source, so is locally finitely presented. For an extension,
trivialize the outer terms and lift the quotient basis locally; this splits the extension
as their direct sum. Exact restriction identifies these constructions with the global
kernel, cokernel and middle term on each stratum. Thus the refined stratification proves
all three conclusions. Local triviality is applied only on the noetherian strata, never
on arbitrary covering schemes. Empty schemes, empty strata and rank zero require no basis
lifts and satisfy the same formulas. -/
theorem isConstructibleModuleObject_serre_padicAlgCl
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicAlgClRingObj T ℓ)) (f : M ⟶ N),
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) M →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) N →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) (kernel f) ∧
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (padicAlgClRingObj T ℓ)),
      S.ShortExact →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) S.X₁ →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) S.X₃ →
      IsConstructibleModuleObject (padicAlgClRingObj T ℓ) S.X₂) := by
  sorry

end AlgebraicGeometry.ProEtale
