module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.DerivedPullback

/-! # Relative pseudo-coherence of a flat locally finitely presented structure sheaf

Source: Stacks Project, More on Morphisms, Tags 0695 and 067Y (3), with More on Algebra,
Tag 067J (blueprint: lem-sfb-flat-lfp-structure-relative-pseudocoherence).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The structure module in degree zero is pseudo-coherent relative to the base of a flat
locally finitely presented morphism, without quasi-compactness or Noetherian hypotheses.
Source: Stacks Project, More on Morphisms, Tag 0695,
`lemma-flat-finite-presentation-pseudo-coherent`, and Tag 067Y (3),
`lemma-pseudo-coherent`; More on Algebra, Tag 067J
(blueprint: lem-sfb-flat-lfp-structure-relative-pseudocoherence).

Proof:
1. Choose arbitrary affine covers V_a of S and U_ab of the preimages of V_a in Y.
   By lem-weil-pbc-flat-morphism-affine-criterion and
   lem-weil-pbc-lfp-affine-opens-finite-presentation, their ring maps R_a → C_ab
   are flat and finitely presented. No finite subcover is needed.
2. By def-weil-pbc-finitely-presented-algebra choose a surjective presentation
   P = R[x_1,...,x_n] → C with finitely generated kernel, allowing n = 0.
   The finite-presentation criterion on arbitrary affine pairs also implies local
   finite type (def-weil-finite-type-morphism). By def-nagata-relative-affine-space,
   Spec P is affine n-space over V_a. The presentation defines a closed immersion
   i : U_ab → Spec P over V_a by def-weil-closed-immersion and
   lem-weil-pbc-closed-immersion-affine-cover-criterion on the one-member affine cover.
3. By lem-sfb-flat-fp-polynomial-pseudocoherent, C[0], as a P-module through this
   presentation, has a bounded-above finite-free representative. Flatness is over R;
   neither ring is assumed Noetherian.
4. By lem-pc-affine-qcoh-derived-equivalence the structure module on U_ab corresponds
   to C[0]. By lem-weil-pbc-pushforward-tilde-spec its ordinary pushforward is the
   tilde sheaf of C as a P-module. The ordinary pushforward preserves homology by
   lem-pc-closed-module-pushforward-homology, hence takes a K-injective resolution
   to a quasi-isomorphic pushed-forward complex. Thus Ri_* O_U_ab[0] is tilde C[0]
   by def-pc-derived-direct-image.
5. Apply lem-pc-affine-pseudo-coherent-criterion to the representative in step 3.
   The derived image is pseudo-coherent by def-pur-pseudo-coherent-complex, hence
   m-pseudo-coherent for every m in the sense of def-sfb-m-pseudo-coherent-complex.
6. By def-pc-derived-pullback, restriction of O_Y[0] to U_ab is O_U_ab[0]. For each
   integer m, the covers and embeddings above therefore witness the condition of
   def-sfb-relative-pseudo-coherent-complex. Quantify over all m. Infinite covers
   and empty inverse images are allowed throughout. -/
theorem isPseudoCoherentRelativeTo_structureSheaf_of_flat_of_locallyOfFinitePresentation
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {Y S : Scheme.{u}} (g : Y ⟶ S) [Flat g] [LocallyOfFinitePresentation g] :
    IsPseudoCoherentRelativeTo g
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings Y.toRingedSpace))) := by
  sorry

end AlgebraicGeometry.Scheme
