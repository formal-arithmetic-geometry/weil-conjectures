/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Étale change of topology detects finite type of arbitrary structure modules

Source: Stacks Project, `spaces-perfect.tex`, Tag 08HD, lemma-descend-finite-type
(blueprint: lem-sfb-etale-finite-type-module-detection).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An arbitrary structure module is of finite type precisely when its canonical
Zariski-to-small-étale tensor pullback is of finite type.

Source: Stacks Project, `spaces-perfect.tex`, Tag 08HD, lemma-descend-finite-type
(blueprint: lem-sfb-etale-finite-type-module-detection).

The comparison-square theorem supplies the context for the canonical ringed-site
pullback. Its context has only continuity and right-adjoint proofs, so choosing
it chooses no ring, module or noncanonical map. Both finite-type predicates are
Mathlib's local finite generating-section predicate, equivalently a local finite
free epimorphism. Neither side requires quasi-coherence or a finiteness condition
on the scheme.

Proof, following the six steps of the DAG:
1. Locally present a finite-type module by a finite free epimorphism. The tensor
   pullback preserves cokernels and finite coproducts by
   lem-weil-pbc-ringed-topoi-module-adjunction, and sends the structure module to
   the étale structure module. Zariski covers remain covers after étale base
   change by lem-weil-pbc-etale-scheme-base-change. This gives the forward direction.
2. Conversely fix x and choose an étale chart meeting x with finite generators
   s_i for the pulled-back module. Use lem-trf-zariski-etale-tensor-sections and
   def-weil-presheaf-modules-sheafification to view these as sheafified tensor
   sections. By lem-weil-pbc-site-sheafification-iso-locally-bijective, successively
   refine the chart to lift the finitely many s_i, keeping a point over x.
3. The construction def-pc-module-pullback is a sheafified tensor product
   (def-pur-sheaf-tensor-product). Lift locally through that sheafification and
   then through the inverse-image sheafification, using the same local-bijectivity
   lemma. Each generator becomes a finite sum a_ij tensor t_ij. Neighbourhood
   colimits represent each t_ij by a section on an open neighbourhood of x.
   Intersect these finitely many opens and shrink the source about its chosen
   point to obtain all t_ij over one common open U containing x.
4. The resulting étale chart has open image W containing x: étale morphisms are
   flat and locally of finite presentation (def-weil-etale-morphism), so apply
   lem-weil-pbc-flat-lfp-open. The finite t_ij define q : O_W^N to F restricted
   to W. Its étale pullback generates on the surjective chart and is locally
   surjective, hence epi by lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective
   and the sheafified-cokernel description of def-weil-sheaf-of-modules-category.
5. For every y in W, prop-weil-pbc-geometric-stalks-exact makes the geometric
   stalk of the pulled-back q surjective. By
   lem-sfb-etale-zariski-module-geometric-stalk it is q_y tensored with the strict
   henselization of O_W,y. This local extension is faithfully flat by
   lem-sc-strict-henselization-faithfully-flat. Apply
   lem-pc-local-flat-faithful-flat-reflects-surjective to deduce surjectivity of
   q_y. Then lem-sc-abelian-sheaf-epi-iff-stalk-epi and the module cokernel
   description show q itself is epi.
6. These neighbourhoods W cover X, giving finite type on its Zariski site.
   The empty scheme uses the empty cover; zero generators give the zero module.
   No quasi-coherence, Noetherian condition or quasi-compactness was used. -/
theorem isFiniteType_iff_etale_extension (X : Scheme.{u}) (F : X.Modules) :
    F.IsFiniteType ↔
      SheafOfModules.IsFiniteType
        ((Classical.choose zariski_etale_functor_comparison_square X).extension.obj F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
