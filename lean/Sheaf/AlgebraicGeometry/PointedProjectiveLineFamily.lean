module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.TraceFormula.SmoothCurveSectionCartier
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen

/-! # Pointed smooth families of projective lines

Source: Conrad, Reductive group schemes, Proposition 4.2.7, proof, printed p.124.
(blueprint: lem-sfb-pointed-projective-line-family)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth proper family of geometric projective lines with a section admits pointed
Zariski local trivializations, and each chosen trivialization stays pointed under arbitrary
base change. The final commuting square specifies the pullback of the chosen isomorphism.

Source: Conrad, Reductive group schemes, Proposition 4.2.7, proof, printed p.124,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf.
(blueprint: lem-sfb-pointed-projective-line-family)

Proof:
1. Smoothness gives flatness and local finite presentation (lem-pc-smooth-flat); properness
   gives quasi-compactness and separatedness, hence finite presentation. The geometric
   projective lines have pure dimension one (lem-sc-projective-line-smooth-relative-dimension-one).
   The geometric dimension comparison (lem-trf-geometric-pure-fibre-point-dimension) makes f
   smooth of relative dimension one. The empty base is covered by the empty family.
2. By lem-trf-smooth-curve-section-cartier, the section defines an effective Cartier divisor D.
   It is relative effective Cartier since D is the base itself (def-pc-relative-effective-cartier).
   Its inverse ideal L is invertible (lem-pc-divisor-line-bundle-invertible), and arbitrary
   base change preserves it and the section divisor (lem-pc-recd-pullback).
3. On each geometric fibre a determinant-one coordinate change sends the marked point to
   [1:0]. The two standard charts identify its inverse ideal with O(1). By
   lem-pc-projective-space-twist-cohomology, H0 has dimension two and H1 vanishes; the complete
   linear system is an isomorphism, as its two affine chart maps are polynomial identities.
   This calculation also works in characteristic two.
4. Apply lem-sfb-fibrewise-very-ample-evaluation: E = f_*L is finite locally free, commutes
   with arbitrary base change, and its evaluation quotient defines a closed immersion into
   the quotient projective bundle P(E). Fibrewise H0 identifies its rank as two.
5. Trivialize E locally. The lem-trf-projective-bundle-quotient-geometry and
   lem-trf-free-projective-bundle-base-change-space comparisons give a map to P1. Its geometric
   fibres are isomorphisms. Apply lem-sfb-universal-isomorphism-open: the source is flat,
   locally finitely presented and universally closed, and the target is proper by
   lemma-nagata-projective-space-base-change-proper. Every geometric point belongs to the
   universal isomorphism open, so it is the entire base, including its nilpotents.
6. The section corresponds to a quotient E -> M with M invertible. Trivialize M and refine
   by the opens where one of the two quotient coefficients is a unit. If they are a,b with
   a invertible, replace v0,v1 by a^-1 v0, v1-b a^-1 v0. This basis carries the quotient to
   (1,0), hence the section to infinity. Interchange v0,v1 on the other open.
7. Pull back each chosen isomorphism and its inverse along every T -> U. Their composites
   remain identities, projective space commutes with base change, and the pointed equality
   pulls back to the same equality. No flatness or reducedness of T is required. -/
theorem exists_pointedProjectiveLineFamily_trivialization
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [Smooth f] [IsProper f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      ∃ e : pullback f s ≅ ProjectiveLine (Spec (.of Ω)),
        e.hom ≫ ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) = pullback.snd f s) :
    ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      ∃ e : pullback f U.ι ≅ ProjectiveLine U.toScheme,
        e.hom ≫ ProjectiveLine U.toScheme ↘ U.toScheme = pullback.snd f U.ι ∧
        pullback.lift (U.ι ≫ σ) (𝟙 U.toScheme) (by simp [Category.assoc, hσ]) ≫ e.hom =
          ProjectiveLine.infinity U.toScheme ∧
        ∀ (T : Scheme.{u}) (h : T ⟶ U.toScheme),
          ∃ eT : pullback f (h ≫ U.ι) ≅ ProjectiveLine T,
            eT.hom ≫ ProjectiveLine T ↘ T = pullback.snd f (h ≫ U.ι) ∧
            pullback.lift ((h ≫ U.ι) ≫ σ) (𝟙 T) (by simp [Category.assoc, hσ]) ≫ eT.hom =
              ProjectiveLine.infinity T ∧
            eT.hom ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) h =
              pullback.map f (h ≫ U.ι) f U.ι (𝟙 X) h (𝟙 S)
                (by simp) (by simp) ≫ e.hom := by
  sorry

end AlgebraicGeometry
