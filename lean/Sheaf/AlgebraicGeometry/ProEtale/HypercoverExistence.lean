/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences
import Sheaf.AlgebraicGeometry.WContractibleAffineCover
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence
import Sheaf.CategoryTheory.CoskeletonMatchingTuples

/-!
# Hypercovers by single w-contractible affines

Source: the blueprint of the Weil conjectures, chapter `sec-proetale-coefficients`,
unit `sk-prop-pe-hypercover` (blueprint: det-pe-hypercover-existence); Stacks Project,
Tag 09A1.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped Simplicial

namespace AlgebraicGeometry

/-- Hypercovers by single spectra of w-contractible rings.

Source: Stacks Project, Tag 09A1, `lemma-w-contractible-hypercovering`, part (2);
Tags 094K, 0DAV and 0DB2 (blueprint: det-pe-hypercover-existence).
The simplicial object is valued in `Over U`, so its augmentation is part of its data
and its matching limits are relative to `U`. In degree one the matching object is
`W₀ ×_U W₀`. Covering predicates are tested on the underlying arrows in `X.ProEt`.

Proof (the nine steps of the node):
1. By [lem-weil-pbc-finite-affine-coproduct-spectrum], the spectrum of a finite
   product is the finite disjoint union of the spectra. The summands are clopen by
   [lem-weil-pbc-scheme-coproduct-family]. Closed points, unique closed specializations,
   strictly henselian local rings and extremal disconnectedness of the component space
   therefore hold piecewise, giving [det-pe-wlocal-strict-contractible]. For the empty
   product the spectrum and component space are empty, so the conditions are vacuous.
2. Apply [det-pe-wcb-cover] to `V`. Faithfully flat affine covers surject onto their
   affine target charts by [lem-weil-pbc-faithfully-flat-surjective-spectrum]. These
   charts cover `V`; compactness selects finitely many. Their affine source coproduct
   is a site object by [lem-weil-pbc-proetale-qcqs-finite-family-geometry], and is the
   spectrum of the product ring by [lem-weil-pbc-finite-affine-coproduct-spectrum].
   Step 1 makes the ring w-contractible; [lem-trf-weakly-etale-between-objects]
   makes its map weakly etale.
3. For each affine open `H` of `V`, choose affine neighborhoods inside its intersections
   with the selected charts, using [lem-weil-pbc-affine-opens-basis], then a finite
   subcover. The inverse images under the affine faithfully flat chart covers are
   affine opens, by [lem-weil-pbc-morphism-affine-schemes-affine], with exactly these
   images. Thus [def-weil-pbc-proetale-covering] gives the singleton covering without
   assuming `V` quasi-separated; the empty case uses the zero ring.
4. Work in the qcqs subsite and its slice over `U`. By
   [lem-weil-pbc-proetale-qcqs-finite-family-geometry] it has the required finite limits
   and finite covering families, with the same limits as the full site slice. Step 3
   gives singleton covers by w-contractible affine objects; adjoining an extra arrow
   preserves a finite cover. Use the size convention [def-weil-size-convention].
5. Apply [lem-weil-pbc-site-finite-basis-hypercover-existence] to obtain finite formal
   families of these affines in every degree, all simplicial identities (including
   degeneracies), and componentwise covering matching arrows. The degree-zero matching
   family is the singleton identity of `U` (Tags 094K and 0DAV).
6. Realize finite formal families by scheme disjoint unions. The mapping property
   [lem-weil-pbc-scheme-coproduct-family] gives a functor. It preserves the terminal
   singleton and pullbacks: distribute pullbacks over coproducts by
   [lem-sc-etale-fibre-product-base-change-coproduct]; unequal target components give
   empty pullbacks and equal ones give the component pullback. Together with
   [lem-weil-pbc-semi-representable-finite-limits] and
   [lem-weil-pbc-finite-limits-from-terminal-pullbacks], this proves finite-limit
   preservation in the qcqs slice (Tag 0DB2).
7. Apply realization to all operators. The proper-face diagram is finite. Its limit
   in `Over U` represents the coskeleton matching object: by
   [lem-weil-pbc-coskeleton-matching-tuples], the latter uses all maps from lower
   ordinals. Factor each such map uniquely as a surjection followed by its injective
   image. Extend a proper-face family using the corresponding degeneracy; compatibility
   and functoriality make this inverse to restriction, naturally in the test object.
   The prescribed projection equations identify the canonical matching arrow. In degree
   one this is the product over `U`; degree zero has matching target `U`.
8. Realized matching arrows are singleton covers. For an affine open in the finite
   target coproduct, choose finitely many affine neighborhoods in its summands by
   [lem-weil-pbc-affine-opens-basis]. Apply [def-weil-pbc-proetale-covering] to each
   component covering and combine the finite affine refinements in the source coproduct.
   Their images are exactly the test open. The arrows are weakly etale by
   [lem-trf-weakly-etale-between-objects]. This includes degree zero and empty families.
9. Each realized term is the spectrum of a finite product by
   [lem-weil-pbc-finite-affine-coproduct-spectrum]; step 1 makes it w-contractible.
   By [det-pe-weak-contractible-equivalences] its representable is weakly contractible.
   Choose these spectra as representatives and conjugate all operators by their
   isomorphisms. Inverse pairs cancel in the simplicial identities, and the universal
   property transports matching cones and their maps. Isomorphisms transport affine
   refinements, so [def-weil-pbc-proetale-covering] preserves the singleton covers.
-/
theorem exists_proetale_hypercover_single_affine
    (X : Scheme.{u}) (U : X.ProEt)
    (hUqc : CompactSpace U.left) (hUqs : QuasiSeparatedSpace U.left) :
    (∀ (I : Type u) [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
      [∀ i, IsWContractibleRing (D i)], IsWContractibleRing (∀ i, D i)) ∧
      (∀ (V : X.ProEt), CompactSpace V.left →
        ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f)
          (g : @Scheme.ProEt.mk X _ f hf ⟶ V),
          IsWContractibleRing D ∧
            Presieve.singleton g ∈ (Scheme.ProEt.precoverage X) V) ∧
      ∃ (W : SimplicialObject (Over U)),
        (∀ (r : ℕ),
          ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f),
            IsWContractibleRing D ∧
              (W _⦋r⦌).left = @Scheme.ProEt.mk X _ f hf ∧
              (∀ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
                (φ : F ⟶ (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left)
                [Epi φ],
                ∃ s : (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left ⟶ F,
                  s ≫ φ = 𝟙 _)) ∧
        Presieve.singleton (W _⦋0⦌).hom ∈
          (Scheme.ProEt.precoverage X) U ∧
        (∀ (r : ℕ),
          ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
            (μ : W _⦋r + 1⦌ ⟶ c.pt),
            Nonempty (IsLimit c) ∧
              Presieve.singleton μ.left ∈ (Scheme.ProEt.precoverage X) c.pt.left ∧
              (∀ (a : SimplicialObject.ProperFaceCategory (r + 1)),
                μ ≫ c.π.app (Opposite.op a) = W.map a.obj.hom.op)) := by
  sorry

end AlgebraicGeometry
