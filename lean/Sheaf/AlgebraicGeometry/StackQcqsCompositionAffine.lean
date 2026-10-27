/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Composition and affine examples of qcqs stack morphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 050W, 050K, 050T, 04YT and 0CHQ;
morphisms.tex, Tag 01S7 (blueprint: lem-sfb-stack-qcqs-composition-affine).

The quasi-compact and quasi-separated predicates are those for algebraic stacks,
without assumptions on their absolute diagonals. Affineness is the existing
scheme-test predicate, retaining the projection of each actual 2-base change.

## Main statements

- `CategoryTheory.algebraicModuliMap_qcqs_comp`: qcqs stack morphisms compose.
- `CategoryTheory.algebraicModuliMap_qcqs_of_affine`: affine stack morphisms are qcqs.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- Quasi-compact and quasi-separated morphisms of algebraic stacks over a field compose.
Source: Stacks Project, stacks-morphisms.tex, Tags 050W and 050K
(blueprint: lem-sfb-stack-qcqs-composition-affine).

Proof:
1. For a quasi-compact algebraic-stack test T → Z, form D = Y ×_Z T.
By def-sfb-stack-qcqs-morphism, D and X ×_Y D are quasi-compact; they are algebraic
by lem-sfb-algebraic-stack-fibre-products. The triple description of
 def-sfb-stable-pointed-moduli-groupoids identifies X ×_Y D with X ×_Z T by
(x,(y,t,β),α) ↦ (x,t,β ∘ g(α)), with inverse (x,t,γ) ↦ (x,(f(x),t,γ),id).
Transporting the smooth atlas proves quasi-compactness of the composite.
2. By lem-sfb-fibred-groupoid-representable-smooth-calculus, representable maps
whose scheme tests are qcqs retain those properties under base change.
For composition, lem-sfb-representable-stack-quasicompact-tests and step 1 give
quasi-compactness of each scheme test. For T → W, the middle pullback V_T is an
algebraic space. By lem-sfb-representable-pullback-over-space, U ×_V V_T is also
an algebraic space. Apply lem-sfb-space-quasiseparated-test-calculus to its
projection and then compose with V_T → T to obtain quasi-separatedness.
3. Factor the composite diagonal as X → X ×_Y X → X ×_Z X.
By lem-sfb-groupoid-diagonal-two-pullback-identities the second arrow is the
base change of the diagonal of g. Both arrows therefore have representable qcqs
scheme tests by step 2 and the hypotheses. Their composite is the diagonal of
f.comp g, so def-sfb-stack-qcqs-morphism gives its quasi-separatedness. -/
theorem algebraicModuliMap_qcqs_comp {k : Type u} [Field k]
    {X : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    {Z : BasedCategory.{v₃, w₃} (Over (Spec (.of k)))}
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (hZ : IsAlgebraicModuliStack Z) (f : BasedFunctor X Y) (g : BasedFunctor Y Z)
    (hfqc : IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, 0, 0} f)
    (hfqs : IsQuasiSeparatedAlgebraicModuliMap f)
    (hgqc : IsQuasiCompactAlgebraicModuliMap.{u, v₂, w₂, v₃, w₃, 0, 0} g)
    (hgqs : IsQuasiSeparatedAlgebraicModuliMap g) :
    IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₃, w₃, 0, 0} (f.comp g) ∧
      IsQuasiSeparatedAlgebraicModuliMap (f.comp g) := by
  sorry

/-- Affine morphisms of algebraic stacks over a field are quasi-compact and
quasi-separated. The affine hypothesis includes scheme representability and the
actual projection on every scheme test; `IsAffineHom` means affine inverse images
of affine opens.
Source: Stacks Project, stacks-morphisms.tex, Tags 0CHQ, 050T and 04YT;
morphisms.tex, Tag 01S7 (blueprint: lem-sfb-stack-qcqs-composition-affine).

Proof:
1. Every scheme test A_T → T is affine. Given a quasi-compact algebraic space
C → T, choose a quasi-compact surjective étale scheme atlas U → C.
The affine base change A_U → U is quasi-compact by
lem-weil-pbc-affine-morphism-permanence; its source is quasi-compact by
lem-weil-pbc-quasi-compact-morphism-preimage-qc-open, applied to all of U.
By lem-trf-space-fibre-products-etale-covers, A_U covers A_T ×_T C by a
representable surjective étale map. Thus the test is intrinsically quasi-compact.
The separatedness and quasi-separatedness clauses of lem-sfb-space-affine-locality
and lem-sfb-space-quasiseparated-test-calculus also apply to A_T → T.
Then lem-sfb-representable-stack-quasicompact-tests makes q quasi-compact.
2. A test T → A ×_B A is (x₁,x₂,α). The scheme A ×_B T is affine over T,
and x₁ and x₂ determine sections s₁,s₂. By
lem-sfb-groupoid-diagonal-two-pullback-identities the diagonal test is their
equality locus, the base change of the diagonal of A ×_B T → T.
The affine scheme map is separated by lem-weil-pbc-affine-morphism-permanence.
Its diagonal is a closed immersion and remains one under base change by
lem-weil-pbc-closed-immersion-base-change. By def-weil-closed-immersion it is affine,
so step 1 supplies qcqs for this scheme test. Every diagonal test is therefore an
algebraic space with qcqs projection, as def-sfb-stack-qcqs-morphism requires. -/
theorem algebraicModuliMap_qcqs_of_affine {k : Type u} [Field k]
    {A : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {B : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (q : BasedFunctor A B) (hq : ModuliSchemeTest @IsAffineHom q) :
    IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₃, w₃} q ∧
      IsQuasiSeparatedAlgebraicModuliMap q := by
  sorry

end CategoryTheory
