/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic

/-! # Ampleness reflected by the abelian quotient of a semiabelian variety

Source: Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes,
XI 1.11, field case; compare Lan, Arithmetic compactifications of PEL-type Shimura
varieties, Proposition 3.3.3.6 and Lemma 4.2.1.8, proofs.
(blueprint: lem-sfb-semiabelian-abelian-quotient-ample-reflection).

The kernel and right-translation squares use the given group laws. No splitting,
perfectness or symmetry assumption is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- An invertible module on the abelian quotient is ample if its tensor pullback
along the given torus extension is ample.

Source: Raynaud XI 1.11, field case; Lan, Proposition 3.3.3.6 and Lemma 4.2.1.8,
proofs (blueprint: lem-sfb-semiabelian-abelian-quotient-ample-reflection).

Proof plan (the accepted DAG split; the original Raynaud text is unavailable):
1. Extend scalars to the algebraic closure. By lem-sfb-abelian-field-extension,
   lem-pc-proper-base-change and lem-pod-separated-finite-type-base-change the
   hypotheses persist; the torus splits by def-sfb-tori-multiplicative-type.
   The fppf cover and finite presentation persist by
   lem-trf-fppf-covering-base-change and lem-weil-pbc-qcqs-morphism-permanence;
   base change also preserves the kernel and torsor isomorphisms. Ampleness pulls
   back by lem-trf-scheme-relative-ample-base-change. It descends back by
   lem-sfb-space-relative-ampleness-fpqc-descent, using the singleton fpqc cover
   def-weil-pbc-fpqc-covering supplied by
   lem-weil-pbc-field-extension-base-change-faithfully-flat. The tensor comparisons
   are lem-weil-pbc-invertible-pullback-tensor.
2. Choose ample H on C by lem-sc-abelian-variety-projective. Its dual pulls back
   to an invertible coherent module. By
   lem-weil-pbc-coherent-twist-global-generation, for some n >= 1 the pullback
   of L = D^n tensor H-dual is globally generated. Its fibre at the group identity
   is nonzero and one-dimensional, so it has a nonzero global section.
3. Apply lem-sfb-split-torus-torsor-section-extraction to obtain an invertible N
   with trivial pullback and a nonzero section of R = L tensor N. The node
   lem-sfb-semiabelian-picard-pullback-kernel makes N algebraically trivial.
4. Apply lem-sfb-semiabelian-effective-square-generation to C and R: C is
   commutative by lem-sc-av-commutative and has semiabelian geometric fibres
   of torus rank zero by lem-sfb-abelian-field-extension and
   def-sfb-semiabelian-geometric-fibres. Smoothness and finite type give finite
   presentation by def-sbc-locally-finite-presentation. Thus R^2 is generated.
5. H^2 is ample by lem-sc-ample-positive-tensor-power. At each x choose an affine
   section chart for H^(2a), a >= 1, and a section of R^2 nonzero at x. Their
   tensor product has nonvanishing locus the intersection of the two loci,
   which is affine by lem-sc-affine-cap-section-open. The definition
   def-weil-pbc-ample-invertible-module gives ampleness of H^2 tensor R^2,
   hence of D^(2n) tensor N^2 by lem-weil-pbc-invertible-pullback-tensor.
6. N^2 is algebraically trivial. Clause (ii) of
   lem-sfb-semiabelian-algebraic-equivalence-norm, with C commutative by
   lem-sc-av-commutative and torus rank zero, makes D^(2n) ample. Every affine
   section chart of a positive power of D^(2n) is one of a positive power of D,
   so def-weil-pbc-ample-invertible-module makes D ample. Step 1 descends this
   conclusion to the original field. -/
theorem semiabelian_abelian_quotient_ample_reflection
    {k : Type u} [Field k] (C T G : Grp (Over (Spec (.of k))))
    [IsAbelianVariety C.X] (hT : MultiplicativeType.IsTorus T)
    [IsCommMonObj G.X] [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (i : T ⟶ G) (q : G ⟶ C)
    (hkernel : IsPullback i.hom.hom (toUnit T.X) q.hom.hom η[C.X])
    (hepi : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (yoneda.map q.hom.hom))
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] [QuasiSeparated q.hom.hom.left]
    (htorsor : IsPullback (fst G.X T.X)
      (lift (fst G.X T.X) (snd G.X T.X ≫ i.hom.hom) ≫ μ[G.X])
      q.hom.hom q.hom.hom)
    (D : C.X.left.Modules) [D.IsInvertible]
    (hample : @Scheme.Modules.IsAmple G.X.left
      ((Scheme.Modules.tensorPullback q.hom.hom.left).obj D)
      (((Scheme.Modules.invertible_pullback_tensor q.hom.hom.left).1 D).2)) :
    Scheme.Modules.IsAmple C.X.left D := by
  sorry

end AlgebraicGeometry
