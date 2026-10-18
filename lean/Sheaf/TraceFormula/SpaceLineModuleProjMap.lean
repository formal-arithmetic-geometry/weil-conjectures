/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.TraceFormula.SpaceLineModuleProjInput
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The canonical relative-Proj map attached to a line module on an algebraic space

Source: Stacks Project, Divisors on Spaces, Tag 0D2Z, opening construction and parts
(2), (3); Constructions, Tag 01O9 (blueprint: lem-trf-space-line-module-proj-map).

`GradedAlgebraData` is the affine-basis presentation of the quasi-coherent graded
algebra used by the existing relative-Proj construction. Scheme tests describe the
small-etale graded map by its canonical tensor pullbacks; they also express arbitrary
base-change squares without assuming that those squares are Cartesian.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The positive-degree generation locus is an open algebraic subspace, and the graded
homomorphism determines its canonical morphism to relative Proj over the scheme base.
For every commutative square with scheme corners on the left, the generation locus is
the inverse image of this open, and the canonical maps commute with the unrestricted
relative-Proj base-change comparison. The `IsCanonicalMap` clause specifies the usual
scheme morphism on every trivializing scheme chart, including the scheme specialization.

Source: Stacks, Divisors on Spaces, Tag 0D2Z, opening construction and parts (2), (3);
Constructions, Tag 01O9 (blueprint: lem-trf-space-line-module-proj-map).

Proof:
1. Choose a representable surjective etale scheme atlas of X. Refine it by affine opens
lying above affine opens of T and by trivializations of L. The image of a homogeneous
section of positive degree is then an ordinary regular function. Its nonvanishing
locus is a principal open and is exactly where that image generates the tensor power
of L. Their union is the surjectivity locus of the homogeneous maps. On double
intersections the opens agree, since they are defined by the same pulled-back map.
They descend to an open subspace. The scheme-test condition IsGenerationOpen is this
same union, checked on every scheme mapping to X, including non-quasi-compact schemes.
2. On each principal open the homogeneous-fraction construction of Tag 01O9 gives the
map to the local Proj. The existing relative-Proj chart identifications identify these
targets with the restriction of A.relProj. After a common affine refinement the local
maps have the same fraction formulas, hence agree. Scheme morphism gluing followed by
the sheaf condition for the target descends them to r. The structural map to T agrees
on the atlas, so agrees globally. The chart formula in IsCanonicalMap fixes the map
on a cover; the jointly surjective atlas detects equality and proves uniqueness.
3. In an arbitrary commutative square with scheme source corners, pulling back the
line module, graded coefficients and their maps gives the same local functions.
Their nonvanishing loci pull back to their inverse images, with no flatness condition.
Thus IsGenerationOpen holds for U.preimage k. Apply the same chart construction to the
pulled-back graded homomorphism. The coefficientwise relative-Proj base-change datum
D gives the unrestricted comparison and its canonical isomorphism to the fibre
product. On the pulled-back affine charts the fraction formulas commute with
D.relProjComparison. Gluing gives the displayed equality of scheme maps. This is the
base-change compatibility under D.relProjIsoPullback, by its two projection identities.
4. For a scheme source, tensor pullback is Scheme.Modules.tensorPullback, and the
trivializing-chart equation is exactly Proj.fromOfGlobalSections followed by the
relative-Proj chart embedding. Hence the morphism is the usual scheme construction.
All arguments allow empty schemes, an empty generation locus, and graded algebras
with no positive-degree generators or with degree-zero piece different from O_T. -/
theorem space_line_module_proj_map (S : Scheme.{u}) (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T) (A : T.left.GradedAlgebraData)
    (L : X.Modules) (hL : X.IsLineModule L)
    (ψ : GradedLineMap f A (lineTestFamily X L hL)) :
    ∃ (U : Subfunctor X.obj.obj)
      (hU : Presheaf.IsSheaf (Scheme.fppfTopology.over S) U.toFunctor),
      IsAlgebraicSpace ⟨U.toFunctor, hU⟩ ∧
      IsRepresentableWith (fun _ _ j ↦ IsOpenImmersion j.left) U.ι ∧
      ψ.IsGenerationOpen U ∧
      ∃! r : U.toFunctor ⟶ yoneda.obj (projOver T A),
        ψ.IsCanonicalMap U r ∧
        ∀ (X' T' : Over S) (g : T' ⟶ T) (f' : X' ⟶ T')
          (k : yoneda.obj X' ⟶ X.obj.obj)
          (_hcomm : k ≫ f = yoneda.map f' ≫ yoneda.map g)
          (A' : T'.left.GradedAlgebraData)
          (D : Scheme.GradedAlgebraData.PullbackData g.left A A')
          (ψ' : GradedLineMap (yoneda.map f') A' ((lineTestFamily X L hL).pullback k)),
          ψ.IsBaseChange k g D ψ' →
            ψ'.IsGenerationOpen (U.preimage k) ∧
            ∃! r' : (U.preimage k).toFunctor ⟶ yoneda.obj (projOver T' A'),
              ψ'.IsCanonicalMap (U.preimage k) r' ∧
              ∀ (W : Over S) (a : (U.preimage k).toFunctor.obj (op W)),
                (r'.app (op W) a).left ≫ D.relProjComparison =
                  (r.app (op W) ((U.fromPreimage k).app (op W) a)).left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
