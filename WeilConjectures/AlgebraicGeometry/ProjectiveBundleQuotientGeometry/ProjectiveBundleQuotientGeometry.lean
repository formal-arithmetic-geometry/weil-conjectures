/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjTautologicalCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInversePullback
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSeparated
import WeilConjectures.AlgebraicGeometry.Line.LineQuotientTrivializedCoefficients

/-!
# Projective bundles classify invertible quotients

Source: Stacks Project, Constructions, Tags 01OA, 01OB, 01O4, 01O9, 01OD and 01OE
(blueprint: lem-trf-projective-bundle-quotient-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry

open Scheme.Modules

/-- Projective bundles of arbitrary quasi-coherent modules represent invertible
quotients, naturally under arbitrary scheme pullback, with the prescribed twists,
open-base identifications, separated projection and free-module polynomial models.

Source: Stacks Project, Constructions, Tags 01OA, 01OB, 01O4, 01O9, 01OD and 01OE
(blueprint: lem-trf-projective-bundle-quotient-geometry).

Proof:
1. On an affine base U, the canonical symmetric grading is generated in degree one
(def-trf-canonical-symmetric-graded-algebra). The standard opens D_+(iota(m)) cover
relative Proj by lemma-nagata-relative-proj-exists and prop-nagata-proj-standard-open;
refine base intersections with lem-weil-pbc-affine-opens-basis.
2. On D_+(e), multiplication by e trivializes the degree-one twist, with inverse
x/e^k mapping to x/e^(k+1). On overlaps e=(e/f)f and (e/f)(f/g)=e/g. These are the
homogeneous-localization restrictions of def-weil-pbc-proj-twisting-sheaf and
lem-weil-pbc-proj-basic-open-intersection. Base restrictions preserve them. Glue by
lem-weil-pbc-site-module-sheaf-gluing, obtaining an invertible line.
3. The local section m maps to iota(m)/1. Adjunction
lem-pc-module-pullback-adjunction gives the quotient. It hits the frame e on each
D_+(e), hence is surjective. Its arbitrary tensor pullbacks remain surjective onto
invertible modules (def-pc-module-pullback).
4. Given q, extend its degree-one map by
lem-weil-pbc-quasi-coherent-symmetric-algebra to the graded map into powers of L.
The generation locus is all T, so lem-trf-space-line-module-proj-map supplies its
canonical map. The next steps explicitly verify its quotient and inverse property.
5. Trivialize L on affine W over affine U. By
lem-weil-pbc-module-pullback-affine-sections write q(m)=b_m l. The opens D(b_m)
cover W. On D(b_m), a/e^d maps to b(a)/b_m^d. This is a ring map by localization
and gives a scheme map by def-weil-affine-spectrum.
6. The fraction maps agree on overlaps by lem-weil-pbc-proj-basic-open-intersection.
Replacing l by u*l scales degree d by u^(-d), which cancels in every degree-zero
fraction. Canonical algebra restrictions and relative-Proj charts give the same
maps on base refinements. Glue by lem-weil-pbc-scheme-morphism-gluing. These are
exactly the maps of lem-trf-space-line-module-proj-map, proving IsCanonicalMap.
7. Send the pulled-back frame e to b_m*l. The coefficient of v is b_v/b_m, so this
isomorphism carries the universal quotient to q. Transition equations agree,
including on base refinements; hence these line isomorphisms glue.
8. Starting from a map a, use its pulled-back e frame. The coefficients of the
quotient are a^*(v/e), recovering a on all homogeneous fractions. Equality on
affine charts (def-weil-affine-spectrum) and scheme gluing prove uniqueness.
A compatible isomorphism of quotient pairs preserves all these coefficients.
Thus the correspondence is exactly the claimed bijection on isomorphism classes.
9. Pullback by u sends b(a)/b_m^d to u^*b(a)/(u^*b_m)^d. Thus the composite u;a
classifies the pulled-back quotient, with its pulled-back line isomorphism. Open
base restriction identifies both canonical affine algebras, hence their relative
Projs by lemma-nagata-relative-proj-exists. The twist and quotient agree on each
chart; def-pc-fibre-product identifies this restriction with the fibre product.
10. Apply lem-trf-projective-bundle-separated without a finiteness assumption.
11. For the ordered free basis, the symmetric algebra is the standard polynomial
algebra. Def-nagata-relative-projective-space supplies the same relative charts.
Their twist frames T_i have transitions T_i=(T_i/T_j)T_j, giving exactly
def-pc-projective-space-twist. The affine model is Proj of the polynomial algebra
with twist the shifted module. This includes r=0 and empty charts. -/
theorem projective_bundle_quotient_geometry (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] :
    ∃ D : TautologicalQuotient E,
      IsSeparated (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L),
        L.IsInvertible → Epi q →
        ∃! a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          Classifies D h L q a) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
        (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h),
        ((Scheme.Modules.tensorPullback a).obj D.line).IsInvertible ∧
          Epi (pulledQuotient D h a ha)) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        L.IsInvertible → Epi q → Classifies D h L q a → IsCanonicalMap h L q a) ∧
      (∀ (T T' : Scheme.{u}) (h : T ⟶ S) (u : T' ⟶ T) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        L.IsInvertible → Epi q → Classifies D h L q a →
          Classifies D (u ≫ h) ((Scheme.Modules.tensorPullback u).obj L)
            ((Scheme.Modules.tensorPullbackSectionComp u h).hom.app E ≫
              (Scheme.Modules.tensorPullback u).map q) (u ≫ a)) ∧
      HasOpenCompatibility D ∧ HasFreeCompatibility D := by
  obtain ⟨D, hDopen, hDfree, _⟩ :=
    SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing S E
  obtain ⟨hback, hforward⟩ := line_quotient_chart_inverse_pullback E D
  have hclassifies (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
      (q : (tensorPullback h).obj E ⟶ L) [L.IsInvertible] [Epi q] :
      ∃! a, Classifies D h L q a := by
    obtain ⟨ψ, hψ, _, _, F, hF, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map h E L q
    obtain ⟨hFp, θ, hθ, _, _, _⟩ := hforward T h L inferInstance q inferInstance ψ F hψ hF
    refine ⟨F, ⟨hFp, θ, hθ⟩, ?_⟩
    rintro a ⟨ha, v, hv⟩
    obtain ⟨hLa, hqa, _, hrecover⟩ := hback T h a ha
    obtain ⟨ψa, hψa, _, _, Fa, hFa, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map h E _ (pulledQuotient D h a ha)
    obtain ⟨_, _, _, _, hchange, _⟩ :=
      hforward T h _ hLa (pulledQuotient D h a ha) hqa ψa Fa hψa hFa
    exact (hrecover ψa Fa hψa hFa).1.symm.trans
      (hchange L v q hv ψ F hψ hF).1.symm
  refine ⟨D, isSeparated_projectiveBundle E, ?_, ?_, ?_, ?_, hDopen, hDfree⟩
  · intro T h L q hL hq
    exact hclassifies T h L q
  · intro T h a ha
    exact ⟨(hback T h a ha).1, (hback T h a ha).2.1⟩
  · intro T h L q a hL hq ha
    obtain ⟨ψ, hψ, _, _, F, hF, _, hcanonical, _⟩ :=
      line_quotient_homogeneous_fraction_map h E L q
    obtain ⟨hFp, θ, hθ, _⟩ := hforward T h L hL q hq ψ F hψ hF
    have haF : a = F := (hclassifies T h L q).unique ha ⟨hFp, θ, hθ⟩
    subst a
    intro V W hWV e
    obtain ⟨α, hαscalar, hαgenerator, hαhomogeneous, hα⟩ :=
      line_quotient_trivialized_coefficients h E L q ψ hψ V W hWV e
    refine ⟨α, hαscalar, hαgenerator, hα, ?_⟩
    exact hcanonical.2 W.1.toScheme W.1.ι inferInstance V
      (by simpa only [W.1.ι_preimage_self] using W.1.ι.preimage_mono hWV)
      e α hαhomogeneous hα
  · intro T T' h u L q a hL hq ha
    obtain ⟨ψ, hψ, _, _, F, hF, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map h E L q
    obtain ⟨hFp, θ, hθ, _, _, hnatural⟩ :=
      hforward T h L hL q hq ψ F hψ hF
    have haF : a = F := (hclassifies T h L q).unique ha ⟨hFp, θ, hθ⟩
    subst a
    obtain ⟨hLu, hqu, hnu⟩ := hnatural T' u
    obtain ⟨ψu, hψu, _, _, Fu, hFu, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map (u ≫ h) E _ (lineQuotientPullback h u E L q)
    obtain ⟨hFup, θu, hθu, _⟩ :=
      hforward T' (u ≫ h) _ hLu (lineQuotientPullback h u E L q) hqu ψu Fu hψu hFu
    have heq := (hnu ψu Fu hψu hFu).choose
    rw [← heq]
    exact ⟨hFup, θu, hθu⟩

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
