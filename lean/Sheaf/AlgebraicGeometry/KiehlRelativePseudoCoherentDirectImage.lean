module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex

import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.NoetherianProperBoundedCoherentImage
import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic

/-! # Kiehl finiteness for relatively pseudo-coherent complexes

Source: Stacks Project, perfect.tex, Tag 0CSD, the unnumbered paragraph beginning
"More generally" after lemma-flat-proper-pseudo-coherent-direct-image-general, citing Kiehl
(blueprint: lem-sfb-kiehl-relative-pseudocoherent-direct-image).

A proper morphism takes a relatively pseudo-coherent object to a pseudo-coherent object.
The schemes are arbitrary and the derived categories are unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Kiehl finiteness for a proper morphism and a relatively pseudo-coherent complex.
No flatness, finite presentation, Noetherian, global quasi-compactness or global
quasi-separatedness hypothesis on the schemes, or global lower bound on the complex is
required. The derived-category instances select the localizations used by the definitions.

Source: Stacks Project, perfect.tex, Tag 0CSD, unnumbered "More generally" paragraph
following lemma-flat-proper-pseudo-coherent-direct-image-general, citing Kiehl
(blueprint: lem-sfb-kiehl-relative-pseudocoherent-direct-image).

Proof plan (the DAG's agent-written assembly of the Kiehl assertion):
1. Restrict to each affine open V = Spec A of the target. Properness and relative
pseudo-coherence restrict, using lem-sfb-relative-pseudocoherence-all-affine-charts.
Use lem-pc-restrict-derived-direct-image-open to identify the restricted direct image.
2. Set C = RΓ(h⁻¹(V), E|h⁻¹(V)). The finite-degree approximation theorem
lem-sfb-relative-complex-noetherian-cohomology-approximation gives quasi-coherence.
Properness gives a quasi-compact, quasi-separated map, so
lem-pc-derived-direct-image-preserves-qcoh and lem-pc-affine-qcoh-derived-equivalence
identify the image with the sheafification of C. Use
lem-pc-global-sections-direct-image-kinjective-acyclic with the identity ring map to
identify derived global sections of the image with C. For each integer m, approximation
supplies a Noetherian proper model, a bounded coherent object F₀, and a map
A ⊗ᴸ C₀ → C that is an isomorphism above m and surjective in degree m.
3. Apply lem-pc-noetherian-proper-bounded-coherent-image to F₀ and
lem-pc-noetherian-bounded-coherent-pseudo-coherent to its direct image. The same
global-sections acyclicity and lem-pc-affine-pseudo-coherent-criterion give a bounded-above
finite free complex P₀ representing C₀, without any finite Tor dimension assumption.
4. By lem-pc-module-bounded-flat-kflat, P₀ is K-flat. Hence the termwise base change
P = A ⊗ P₀ computes A ⊗ᴸ C₀, remains bounded above and is termwise finite free.
No flatness of A over its Noetherian model is needed.
5. The stupid truncation σ≥m P is bounded finite free and maps to P by a map invertible
on cohomology above m and surjective in degree m. Composing with the approximation map
gives exactly def-pc-ring-m-pseudo-coherent for C in degree m.
6. As m is arbitrary, lem-pc-ring-pseudo-coherent-iff-all-m makes C pseudo-coherent.
The affine criterion makes the direct image pseudo-coherent on V. Its locality, in
def-pur-pseudo-coherent-complex, gives the conclusion on the target. Bounds and models
are chosen separately for each V and m, so no global lower bound is imposed. -/
theorem isPseudoCoherent_derivedDirectImage_of_relative
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Z T : Scheme.{u}}
    [∀ U : T.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (h : Z ⟶ T) [IsProper h] (E : schemeDerivedCategory Z)
    (_hE : IsPseudoCoherentRelativeTo h E) :
    IsPseudoCoherent T ((schemeDerivedDirectImage h).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
