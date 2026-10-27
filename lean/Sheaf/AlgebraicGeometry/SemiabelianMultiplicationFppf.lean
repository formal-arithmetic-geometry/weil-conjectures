module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-! # Multiplication on a semiabelian scheme

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.3.2.1 and II 3.3.3.
(blueprint: lem-sfb-semiabelian-multiplication-fppf)

The relation schemes are arbitrary limit cones for the finite wide cospan of
copies of multiplication in schemes over S. Their restriction is the image cone
under the canonical pullback functor; this retains every projection and the
common-value map. For one factor the limit is canonically G itself.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Positive multiplication is flat, surjective, quasi-finite and finitely presented,
including in residue characteristics dividing the multiplier. Its relation schemes
are flat, finitely presented and locally Noetherian, and commute with open restriction.
Finite presentation is the conjunction of local finite presentation, quasi-compactness
and quasi-separatedness. `HasFiniteFibres` records the explicit finite-fibre clause.

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.3.2.1 and II 3.3.3.
(blueprint: lem-sfb-semiabelian-multiplication-fppf)

Proof plan:
1. On a geometric fibre write the semiabelian extension as T -> H -> A. The
   pullback of multiplication on T over a point with unit coordinates u_i is
   C[z_i]/(z_i^d-u_i). Each z_i is a unit. Successive monic quotients give the
   free basis with exponents less than d (lem-weil-pbc-monic-quotient-free).
   Finite free implies flat and finitely presented as a module; the displayed
   algebra is finitely presented. Roots in algebraically closed residue fields
   give surjectivity. This includes rank zero and characteristics dividing d.
2. Multiplication on A is finite locally free and surjective by
   lem-sc-mult-n-finite-flat and lem-sc-mult-n-isogeny. Apply
   lem-sfb-finite-flat-homomorphism-extensions to the diagram of exact fppf
   sequences to obtain the same assertion on H, hence finite geometric fibres.
3. The map over S is locally finitely presented by
   lem-a1-map-over-base-finite-presentation. Over each affine base open G is
   quasi-compact and quasi-separated, so its endomorphism has both properties
   by lem-weil-pbc-qcqs-morphism-permanence. Locality on the target gives finite
   presentation globally (lem-pc-quasi-compact-local-on-target).
4. Descend geometric-fibre flatness along the faithfully flat field extension
   using lem-sfb-pointwise-flatness-base-change. Smoothness makes G flat over S;
   lem-sfb-fibrewise-flatness-criterion then gives flatness of multiplication.
5. Lift a target point to a geometric fibre and lift it again through its
   surjective multiplication map. Projection gives surjectivity downstairs.
   Descend quasi-finiteness first to the residue-field fibre and then to G by
   lem-sfb-scheme-quasifinite-at-base-change. Together with quasi-compactness
   this is quasi-finiteness (pqf-lem-qf-locqf-qc). Finite fibres also descend
   from the geometric finite fibres through their surjective projections.
6. Flatness, surjectivity and local finite presentation give the singleton fppf
   cover. Quasi-compactness additionally gives the singleton fpqc cover.
7. Start with R_1 = G. Each successor relation scheme projects to the preceding
   one by a base change of multiplication. Flatness and finite presentation
   are preserved by base change and composition. A finitely presented scheme
   over a locally Noetherian scheme is locally Noetherian, by
   lem-weil-pbc-finite-type-over-noetherian applied on affine base opens.
8. Over an open U, maps to the restricted relation scheme are exactly tuples
   of maps to G_U with equal images under restricted multiplication. The
   fibre-product universal property gives the asserted limit cone with all
   projections. The same description works for one factor and the empty open. -/
theorem semiabelian_multiplication_fppf
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G) (d : ℕ) (hd : 0 < d) :
    Flat (𝟙 G.X ^ d).left ∧
    Surjective (𝟙 G.X ^ d).left ∧
    Scheme.Hom.IsQuasiFinite (𝟙 G.X ^ d).left ∧
    Scheme.Hom.HasFiniteFibres (𝟙 G.X ^ d).left ∧
    LocallyOfFinitePresentation (𝟙 G.X ^ d).left ∧
    QuasiCompact (𝟙 G.X ^ d).left ∧ QuasiSeparated (𝟙 G.X ^ d).left ∧
    Presieve.singleton (𝟙 G.X ^ d).left ∈ Scheme.fppfPrecoverage G.X.left ∧
    Presieve.singleton (𝟙 G.X ^ d).left ∈ Scheme.fpqcPrecoverage G.X.left ∧
    ∀ (a : ℕ), 0 < a →
      ∀ R : WidePullbackCone (fun _ : Fin a ↦ (𝟙 G.X ^ d)), IsLimit R →
        Flat R.pt.hom ∧ LocallyOfFinitePresentation R.pt.hom ∧
        QuasiCompact R.pt.hom ∧ QuasiSeparated R.pt.hom ∧
        IsLocallyNoetherian R.pt.left ∧
        ∀ U : S.Opens, Nonempty (IsLimit ((Over.pullback U.ι).mapCone R)) := by
  sorry

end AlgebraicGeometry
