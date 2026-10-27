/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.SchemeEtaleRingedPresentation
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.Paper.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.RingedToposSliceFunctoriality
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.EtaleSubsheafFinalOpen
import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Reconstruction and rigidity of schemes from their ringed étale topoi

Source: Stacks Project, Étale Cohomology, Tags 04HZ, 04I5, 04LW, 04IJ and 04I7
(blueprint: lem-sfb-scheme-ringed-etale-reconstruction).

The small affine presentation is equivalent to the full small étale topos. `Induces`
retains the base-change formula on representables and evaluation of every function;
thus it specifies the induced ringed morphism up to its ring-compatible isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleRinged

/-- Schemes are recovered fully faithfully, with rigid two-morphisms, from their locally
ringed étale topoi. No separation, compactness or finite-type assumption is made.

Source: Stacks Project, Étale Cohomology, Tags 04HZ (lemma-etale-site-locally-ringed),
04I5 (lemma-morphism-locally-ringed), 04LW (lemma-faithful), 04IJ (lemma-2-morphism),
04I6 (lemma-morphism-ringed-etale-topoi-affines), 04I7 (theorem-fully-faithful)
(blueprint: lem-sfb-scheme-ringed-etale-reconstruction).

Proof:
1. Principal opens D(s) and D(1-s) cover every étale chart, and on the respective
   opens s and 1-s are units. If 0=1 on a chart, it is empty; conversely the empty
   chart has its unique section. This proves both local-ringedness conditions,
   including for the empty scheme.
2. Pullback of functions, with the algebraic inverse-image adjunction
   (lem-weil-pbc-etale-inverse-image-algebraic-structures), gives the induced ringed
   morphism and its displayed evaluation normalization. The germ formula
   (lem-weil-pbc-sets-etale-inverse-image-stalk-germ) and strict-henselization
   functoriality identify stalk maps with local homomorphisms. Stalk detection
   (lem-weil-pbc-sets-etale-iso-on-geometric-stalks) proves the units square cartesian.
3. A ring-compatible isomorphism of induced inverse images identifies the inverse
   images of open subterminals, by lem-galois-inverse-image-representable. Points
   of schemes are distinguished by opens, so the underlying maps coincide.
   Naturality for evaluation of functions then identifies their sheaf maps.
   Hence the two scheme morphisms are equal (Tag 04LW).
4. For rigidity, lem-sfb-etale-affine-coordinate-monomorphism embeds the inverse
   image of an affine étale representable into a finite power of the structure
   sheaf by coordinates. Ring compatibility and naturality force the endomorphism
   to be identity there. A small affine cover-dense family exists by
   lem-weil-pbc-affine-etale-essentially-small-cover. Its representables are sheaves
   (lem-weil-pbc-small-etale-representable-presheaf-sheaf), and every sheaf has a
   coequalizer presentation by their coproducts
   (lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation). Inverse image
   preserves these colimits (lem-weil-pbc-left-adjoint-preserves-colimits), so
   naturality forces identity on every sheaf (Tag 04IJ).
5. For affine source and target, form the map on global sections B → A. Apply
   lem-sfb-etale-affine-solution-comparison to identify inverse images of affine
   étale representables with the base changes, compatibly with every evaluation.
   Yoneda and adjunction identify direct images on the affine site. Extend across
   lem-weil-pbc-affine-etale-induced-sheaf-equivalence, then take the adjunction
   mate to get the inverse-image isomorphism. Evaluation compatibility gives ring
   compatibility. Steps 3 and 4 give both uniqueness assertions.
6. Restrict via lem-weil-pbc-localized-sheaves-over-representable and
   lem-weil-pbc-etale-site-localization-open. The structure rings coincide on
   charts. Ringed restriction preserves locality and the comparisons of
   isomorphisms by lem-sfb-ringed-topos-slice-functoriality. Composition is local
   by pasting the cartesian unit squares.
7. For affine target and arbitrary source choose a small affine open cover of the
   source. Apply step 5 locally, use step 3 on overlaps, and glue scheme maps by
   lem-weil-pbc-scheme-morphism-gluing. Step 4 makes the ringed isomorphisms agree
   on overlaps. Glue their components and inverses on the induced open covers of
   each étale chart; naturality and ring compatibility descend by uniqueness.
8. For arbitrary target choose an affine open cover. The inverse images of its
   subterminals correspond to source opens by lem-weil-pbc-etale-subsheaf-final-open.
   These cover: inverse image preserves the covering coequalizer and finite
   intersections; a proper union would yield a proper mono-epi subterminal,
   contradicting lem-weil-pbc-sheaf-sets-mono-epi-iso. Apply steps 6 and 7 there.
9. Regard the local maps as maps to the target. Step 3 identifies them on all
   overlaps; scheme gluing gives the global map. Step 4 makes the local ringed
   isomorphisms agree, so step 7 glues them globally. Step 3 gives uniqueness of
   the scheme map. The ratio of two isomorphisms is an endomorphism of the
   induced inverse image; step 4 makes it identity, proving their equality.
-/
theorem scheme_ringed_etale_reconstruction :
    (∀ X : Scheme.{u}, IsLocallyRingedTopos (ring X)) ∧
    (∀ (U V : Scheme.{u}) (a : U ⟶ V),
      ∃ h : Morphism U V, Induces h a ∧ h.IsLocal) ∧
    (∀ (U V : Scheme.{u}) (g : Morphism U V), g.IsLocal →
      ∃! a : U ⟶ V, ∃ h : Morphism U V, Induces h a ∧ Nonempty (TwoIso g h)) ∧
    (∀ (U V : Scheme.{u}) (a : U ⟶ V) (h : Morphism U V), Induces h a →
      ∀ t : h.inverse ⟶ h.inverse,
        t.app (ringSheafUnderlying (ring V)) ≫ h.ringMap = h.ringMap →
          t = 𝟙 h.inverse) ∧
    (∀ (U V : Scheme.{u}) (g : Morphism U V) (a : U ⟶ V) (h : Morphism U V),
      Induces h a → Subsingleton (TwoIso g h)) := by
  sorry

end AlgebraicGeometry.Scheme.EtaleRinged
