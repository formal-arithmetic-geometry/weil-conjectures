/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.OrientedConstructibleSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.CategoryTheory.Sites.CoherentObjectApproximation
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization
import Sheaf.Paper.CoherentSetCriterion
import Sheaf.Paper.FinitarySiteEnoughPoints
import Sheaf.Paper.OrientedClosedBaseRestriction
import Sheaf.Paper.OrientedConstructibleCoherent
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.Paper.OrientedMaximalPointFiniteness
import Sheaf.Paper.OrientedSourceLocalization
import Sheaf.Paper.QcqsOrientedTriplePresentation
import Sheaf.TraceFormula.FinitarySiteCoherentGenerators

/-!
# Constructible subobjects on a Noetherian vanishing topos

Source: Orgogozo, “Modifications et cycles proches sur une base générale”,
Section 8.1 and Lemma 8.3.3, printed p. 19 (author draft)
(blueprint: lem-trf-oriented-constructible-subquotients).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles
open AlgebraicGeometry.OrientedConstructibleSheaf

namespace AlgebraicGeometry.OrientedConstructibleSubquotients

/-- Every subobject, quotient, and finite extension of a constructible finite-coefficient
module sheaf on a Noetherian vanishing topos is constructible, including the exact-sequence
formulation and the resulting kernel, cokernel, and image closures. The proof follows
Orgogozo, Section 8.1 and Lemma 8.3.3: coherent finite-set approximation and Noetherian
induction give constructible subobjects; the finite locally constant Serre property on
rectangular strata gives kernels, cokernels, and extensions; the remaining clauses are the
abelian-category consequences.
Source: Orgogozo, “Modifications et cycles proches sur une base générale”, Section 8.1 and
Lemma 8.3.3, printed p. 19 (author draft)
(blueprint: lem-trf-oriented-constructible-subquotients).

Proof (the node's steps).

1. Finite presentation implies finite type, so $X$ is Noetherian
   [lem-weil-pbc-finite-type-over-noetherian]; $X$, $S$ are quasi-compact and quasi-separated
   [lem-weil-pbc-locally-noetherian-quasi-separated], and $f$ is qcqs. By
   [lem-trf-qcqs-oriented-triple-presentation], [lem-trf-finitary-site-coherent-generators] and
   [lem-trf-finitary-site-enough-points], $V_f$ is coherent and its points detect isomorphisms;
   likewise for finite-presentation maps over closed subschemes of $S$.

2. Ascending chains of constructible finite-set sheaves $A_0\subseteq A_1\subseteq\cdots\subseteq F$
   on $E_{Z,T}=Z_{\mathrm{Et}}\overleftarrow\times_{S_{\mathrm{Et}}}T_{\mathrm{Et}}$ stabilize.
   Induct on pairs of closed subsets $(Z,T)$, well founded by
   [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal]; an empty coordinate is trivial.
   [lem-trf-oriented-closed-base-restriction] gives $E_{Z,T}\simeq V_{Z_T/T}$, with $Z_T\to T$ of
   finite presentation ([def-weil-closed-immersion], [def-weil-pbc-noetherian-ring],
   [lem-weil-pbc-qcqs-morphism-permanence], [lem-weil-pbc-proper-fp-permanence](d)), so Step 1
   and [lem-trf-oriented-maximal-point-finiteness] apply.

3. Using finitely many components [lem-weil-pbc-noetherian-finitely-many-components], choose
   dense opens $U_0\subseteq Z$, $V_0\subseteq T$ on whose rectangle $E'_0$ the sheaf $F$ is
   finite locally constant. Let $p_1,\dots,p_r$ be the finitely many maximal point classes in
   $E'_0$ [lem-trf-oriented-maximal-point-finiteness]; each $F_{p_i}$ is finite, so some $N$ has
   $(A_n)_{p_i}=(A_N)_{p_i}$ for $n\ge N$. Shrink to dense opens $U$, $V$ on whose rectangle $E'$
   both $A_N$ and $F$ are finite locally constant; rectangles are open subtopoi by
   [lem-trf-oriented-product-universal] and [lem-trf-oriented-slice-localization].

4. For $n\ge N$ and a point $p$ of $E'$, a maximal generization $q$ lies in $E'$ and is some
   $p_i$. Specialization is bijective on stalks of locally constant sheaves
   [def-trf-geometric-morphism], so $(A_n)_p=(A_N)_p$; conservativity (Step 1) gives
   $A_n=A_N$ on $E'$.

5. The remaining points lie on $E_{Z\setminus U,T}$ ([lem-trf-oriented-source-localization]) or
   $E_{Z,T\setminus V}$ ([lem-trf-oriented-closed-base-restriction]); restriction preserves
   constructibility [def-constructible-stratification]. Induction there and the maximum of the
   indices give stabilization on all points, hence equality.

6. For any set subsheaf $G\subseteq F$ with $F$ constructible: $F$ is coherent
   [lem-trf-coherent-set-criterion]; $G$ is a filtered colimit of coherent objects
   [lem-trf-coherent-object-approximation], whose images in $F$ form a directed family of
   constructible subobjects with union $G$. By Step 5 it has a maximal member, which equals $G$.
   All families are small [def-weil-size-convention].

7. For a constructible module sheaf $B$ and a module subsheaf $A$,
   [lem-trf-oriented-constructible-coherent] and [lem-trf-coherent-set-criterion] make $|B|$ a
   constructible set sheaf; Step 6 makes $|A|$ constructible, and the converse direction makes
   $A$ constructible as a module sheaf.

8. On each rectangular stratum [lem-weil-pbc-locally-constant-derived-serre] applies to the finite
   (hence Noetherian, [def-weil-pbc-noetherian-ring]) ring $\Lambda$: finite locally constant
   module sheaves are closed under kernels, cokernels and extensions. Inverse image to strata is
   exact with $u^{-1}\Lambda=\Lambda$; on common refinements of the stratifications
   ([def-trf-oriented-constructible-sheaf], [def-constructible-stratification]) this gives
   closure under kernels, cokernels and middle terms of extensions.

9. A quotient $B\twoheadrightarrow C$ is the cokernel of its constructible kernel (Steps 7, 8).
   Images are subobjects of their target (Step 7); iterating the extension clause gives finite
   extensions. -/
theorem orientedConstructibleSubquotients
    {S X : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (F : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ)
    (hF : IsConstructible f (𝟙 S) Λ F) :
    (∀ {A : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ} (i : A ⟶ F) [Mono i],
      IsConstructible f (𝟙 S) Λ A) ∧
    (∀ {C : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ} (p : F ⟶ C) [Epi p],
      IsConstructible f (𝟙 S) Λ C) ∧
    (∀ (T : ShortComplex (Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ)), T.ShortExact →
      IsConstructible f (𝟙 S) Λ T.X₁ → IsConstructible f (𝟙 S) Λ T.X₃ →
      IsConstructible f (𝟙 S) Λ T.X₂) ∧
    (∀ {A B : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ} (g : A ⟶ B),
      IsConstructible f (𝟙 S) Λ A → IsConstructible f (𝟙 S) Λ B →
      ∃ K : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ,
        ∃ (ι : K ⟶ A) (hι : ι ≫ g = 0), Nonempty (IsLimit (KernelFork.ofι ι hι)) ∧
          IsConstructible f (𝟙 S) Λ K) ∧
    (∀ {A B : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ} (g : A ⟶ B),
      IsConstructible f (𝟙 S) Λ A → IsConstructible f (𝟙 S) Λ B →
      ∃ C : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ,
        ∃ (π : B ⟶ C) (hπ : g ≫ π = 0), Nonempty (IsColimit (CokernelCofork.ofπ π hπ)) ∧
          IsConstructible f (𝟙 S) Λ C) ∧
    (∀ {A B : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ} (g : A ⟶ B),
      IsConstructible f (𝟙 S) Λ A → IsConstructible f (𝟙 S) Λ B →
      ∃ I : Modules (X := X) (Y := S) (S := S) f (𝟙 S) Λ,
        ∃ (e : A ⟶ I) (m : I ⟶ B), e ≫ m = g ∧ StrongEpi e ∧ Mono m ∧
          IsConstructible f (𝟙 S) Λ I) := by
  sorry

end AlgebraicGeometry.OrientedConstructibleSubquotients
