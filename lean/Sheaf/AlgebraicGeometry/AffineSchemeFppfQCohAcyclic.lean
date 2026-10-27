/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion

/-! # Affine schemes have no positive quasi-coherent fppf cohomology

Source: Stacks Project, Descent, Tag 03DW, first affine-objects paragraph;
Cohomology of Schemes, Tag 01XB
(blueprint: lem-sfb-affine-scheme-fppf-qcoh-acyclic).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Left exact additive sheafification on the chosen big fppf site, used to form
its abelian sheaf cohomology without imposing a universe equality or a hypothesis.
Source: Stacks Project, Sites, Tags 00W1, 00WB; Descent, Tag 03DW
(blueprint: lem-sfb-affine-scheme-fppf-qcoh-acyclic).
Proof: the existing sfbFppfHasWeakSheafify constructs small-valued sheafification
by shrinking the usual larger-valued construction. Finite limits of abelian
presheaves are sectionwise. Larger-valued sheafification preserves finite limits;
transport its finite-limit comparison through the sectionwise shrinking
isomorphisms. This makes the existing small-valued reflector left exact and
therefore supplies HasSheafify, with its usual abelian sheaf category. -/
@[instance] theorem affineFppfHasSheafify (U : Scheme.{u}) :
    HasSheafify (fppfTopology.over U) AddCommGrpCat.{u} := by
  sorry

/-- The underlying abelian sheaf of the associated big-fppf quasi-coherent module
has no positive cohomology on an affine scheme. The chosen equivalence is the
witness of the section-normalized associated-sheaf theorem, whose section and
restriction comparisons identify its value with the prescribed tensor-pullback
section sheaf, up to canonical isomorphism. No arbitrary equivalence is used.
`H'` is cohomology over the terminal arrow `id U`, and the explicit standard Ext
model places the cohomology in the larger universe without a size hypothesis.

Source: Stacks Project, Descent, Tag 03DW, first affine-objects paragraph,
and Cohomology of Schemes, Tag 01XB
(blueprint: lem-sfb-affine-scheme-fppf-qcoh-acyclic).

Proof:
1. Set G to the underlying abelian associated sheaf. Take B to consist of all
   affine-source objects over U, and Cov of finite affine fppf covering families.
   The section and restriction formulas are those of
   lem-sfb-scheme-big-fppf-quasicoherent-equivalence. Iterated fibre products of
   affine schemes over an affine scheme are affine, including repeated factors,
   by lem-weil-pbc-fibre-product-affine-spectra. Thus every covering target,
   member and nonempty iterated intersection belongs to B.
2. For each affine object V, lem-pc-fppf-affine-refinement supplies a finite affine
   fppf refinement of every fppf covering of V, with factorizations through its
   members. Composing with V to U makes this a refinement in the big slice site.
   Thus Cov is cofinal at every object in B.
3. By lem-sfb-finite-affine-fppf-cech-vanishing, the positive Cech cohomology of G
   vanishes on every member of Cov. This uses no finiteness or flatness of the
   module and includes the empty scheme and empty covering.
4. Apply lem-weil-pbc-site-cech-vanishing-criterion to obtain positive cohomology
   vanishing at every affine object. In particular the terminal arrow id U is
   affine. Its cohomology is the right derived functor of abelian evaluation,
   which is the asserted H'.
-/
theorem affine_scheme_fppf_qcoh_acyclic (U : Scheme.{u}) [IsAffine U]
    (F : SfbZariskiQCoh U) (q : ℕ) (hq : 0 < q) :
    IsZero (@Sheaf.H'.{u + 1, u, u + 1} (Over U) _ (fppfTopology.over U)
      inferInstance (HasExt.standard _)
      ((SheafOfModules.toSheaf (sfbFppfRings U)).obj
        ((sfbAssociated U
          ((Classical.choose scheme_big_fppf_quasicoherent_equivalence) U)).obj F))
      q (Over.mk (𝟙 U))) := by
  sorry

end AlgebraicGeometry.Scheme
