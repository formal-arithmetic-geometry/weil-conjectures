/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.GerbeModuliMap
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.StackPointTopology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.Topology.Compactness.Compact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Quasi-compact diagonals descend along gerbes

Source: Stacks Project, stacks-morphisms.tex, Tag 0DQL,
`lemma-gerbe-diagonal-quasi-compact`, relative over S
(blueprint: lem-sfb-gerbe-qc-diagonal-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A gerbe over an algebraic space descends quasi-compactness of the relative
 diagonal. The product of presheaves on `Sch/S` is the relative product over S,
so its diagonal is exactly the relative diagonal of Q over the given base.
Source: Stacks Project, Tag 0DQL (blueprint: lem-sfb-gerbe-qc-diagonal-descent).

Proof:
1. Choose a smooth surjective scheme atlas V of F using
`def-sfb-algebraic-moduli-stack`. The atlas clause of
`lem-sfb-gerbe-smooth-universal-homeomorphism` gives a surjective flat locally
finitely presented composite h : V → Q. Form B = V ×_S V, D = Q ×_S Q,
R = V ×_F V and W = V ×_Q V, using `def-pc-fibre-product`,
`lem-trf-space-fibre-products-etale-covers` and
`lem-sfb-stack-diagonal-space-source-representability`.
2. The map R → B is the base change of the relative diagonal of F. The product
stack is algebraic by `lem-sfb-algebraic-stack-fibre-products` and this map is
quasi-compact by `lem-sfb-representable-stack-quasicompact-tests`. Forgetting the
isomorphism in F gives R → W over B (`def-sfb-stable-pointed-moduli-groupoids`).
3. After every affine scheme test T → B, the map R_T → W_T is point-surjective:
two objects in the same gerbe fibre are fppf locally isomorphic. Over a field a
nonempty member of this covering has a residue field, giving the required lift
of the point class (`def-pc-fppf-site`, `lem-sfb-stack-point-topology`).
4. By `lem-sfb-space-quasicompact-affine-tests`, R_T is quasi-compact. Its continuous
surjective image W_T is quasi-compact, using `lem-a1-space-etale-open-image`,
`lem-a1-space-point-open-calculus` and `lem-weil-pbc-continuous-image-quasi-compact`.
The affine tests make W → B quasi-compact. For a quasi-compact space test, take a
quasi-compact etale scheme atlas, use `lem-trf-space-fibre-products-etale-covers`,
and again use the continuous-image argument. This supplies the space-test form.
5. The map h ×_S h : B → D is surjective flat locally finitely presented by
base change and composition, using `lem-sfb-stack-chartwise-smooth-etale-calculus`
and `lem-sfb-stack-diagonal-space-source-representability`.
6. The square W → B over Q → D is cartesian: remove or insert the repeated common
Q-section in its triples. Descend quasi-compactness along the singleton fppf
cover B → D by `lem-sfb-space-quasicompact-fppf-local`. Thus the relative diagonal
of Q is quasi-compact; `def-sfb-stack-qcqs-morphism` identifies this with relative
quasi-separatedness of Q. The same base-change clause gives every scheme test.
No quasi-compactness, separatedness, finite-type or Noetherian assumption is used. -/
theorem gerbe_qc_diagonal_descent {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (Q : AlgebraicSpace S)
    (p : BasedFunctor F (discreteModuli Q.obj.obj))
    (hF : IsAlgebraicModuliStack F) (hp : IsGerbeModuliMap p)
    (hΔ : IsQuasiCompactAlgebraicModuliMap.{u, _, _, _, _, v', w'}
      (moduliRelativeDiagonal (moduliBaseStructure F))) :
    AlgebraicSpace.MapIsQuasiCompact (prod.lift (𝟙 Q.obj.obj) (𝟙 Q.obj.obj)) := by
  sorry

end CategoryTheory
