/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A quasi-compact atlas composite and an affine diagonal

Source: Stacks Project, stacks-morphisms.tex, Tag 050X
(lemma-surjection-from-quasi-compact) and Tag 04YW(4) (definition-separated);
morphisms.tex, Tag 01S7 (lemma-affine-separated)
(blueprint: lem-sfb-stack-qcqs-atlas-affine-diagonal).

The target is a scheme regarded as its existing discrete fibred groupoid.
Affineness of the diagonal is stated by affine scheme representations of its
2-base changes along affine schemes. The composite with the atlas is identified
with a scheme morphism by a 2-isomorphism over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v₁ w₁

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A morphism to a scheme is qcqs if it has an affine relative diagonal and its
composite with a smooth surjective scheme atlas is quasi-compact.
Source: Stacks Project, stacks-morphisms.tex, Tags 050X and 04YW(4), with
morphisms.tex, Tag 01S7
(blueprint: lem-sfb-stack-qcqs-atlas-affine-diagonal).

Proof:
1. For a quasi-compact algebraic stack T mapping to Y, choose a smooth surjective
atlas V → T with V a quasi-compact scheme, using def-sfb-stack-qcqs-morphism.
Form F = Z ×_Y T and F_V = Z ×_Y V using lem-sfb-algebraic-stack-fibre-products.
The scheme W = U ×_Y V is quasi-compact: its map to V is the base change of q,
so apply lem-weil-pbc-qcqs-morphism-permanence, parts (3) and (2).
2. The maps W → F_V and F_V → F are the base changes of the two atlases, as seen
on the triples of def-sfb-stable-pointed-moduli-groupoids. By base change and
composition in lem-sfb-stack-chartwise-smooth-etale-calculus, their composite is
a smooth surjective scheme atlas. Its source W is quasi-compact, proving that F
is quasi-compact. Varying T proves quasi-compactness of f.
3. For any scheme T mapping to Z ×_Y Z, its diagonal base change D → T is an
algebraic-space morphism, by the representable diagonal of Z and the fact that
Y has discrete fibres. All its affine scheme tests have affine scheme source
by hdiag. Pull back along the disjoint union of an affine open cover of T.
The result is an affine scheme morphism: every affine open of that disjoint
union meets only finitely many components. Apply lem-sfb-space-affine-locality
to descend affineness. It also says D is a scheme and D → T is quasi-compact
and separated. Its diagonal is a closed immersion, hence affine, by
pqf-def-affine-morphism and def-weil-closed-immersion.
4. For either D → T or its diagonal, test against a quasi-compact algebraic space
C and take a quasi-compact surjective etale scheme chart C' → C, using
def-trf-algebraic-space. By lem-sfb-space-affine-locality its scheme base change
is affine and hence quasi-compact; its source is quasi-compact by part (2) of
lem-weil-pbc-qcqs-morphism-permanence. This source is a surjective etale scheme
chart of the base change over C, proving its quasi-compactness. Thus D → T is
qcqs on the precise space tests of def-sfb-stack-qcqs-morphism. Varying T proves
quasi-separatedness of f. No nonemptiness, finite-type or Noetherian hypothesis
is used in any step. -/
theorem stack_qcqs_of_atlas_comp_quasiCompact_of_affine_diagonal
    {S : Scheme.{u}} (Z : BasedCategory.{v, w} (Over S)) (Y U : Over S)
    (f : BasedFunctor Z (discreteModuli (yoneda.obj Y)))
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) Z)
    (hZ : IsAlgebraicModuliStack Z) (hp : IsSmoothModuliAtlas Z U p)
    (hqc : ∃ q : U ⟶ Y,
      Nonempty (ModuliTwoIso (p.comp f) (discreteModuliMap (yoneda.map q))) ∧
        QuasiCompact q.left)
    (hdiag : ∀ (T : Over S), IsAffine T.left →
      ∀ t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct f f),
        ∃ R : Over S, IsAffine R.left ∧
          IsRepresentedByScheme (moduliTwoFiberProduct t (moduliRelativeDiagonal f)) R) :
    IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, v₁, w₁} f ∧
      IsQuasiSeparatedAlgebraicModuliMap f := by
  sorry

end CategoryTheory
