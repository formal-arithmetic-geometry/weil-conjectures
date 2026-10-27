/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.ModuliStackProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Open substacks and finite étale decorations of smooth finite-type DM stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 0CIP, 0CIM, 075V, 06FT, 0CPM,
050E; algebraic.tex, Tags 05UN and 05UM
(blueprint: lem-sfb-dm-open-finite-etale-permanence).

All stack predicates are the existing scheme-test definitions. The finite étale
hypothesis retains the actual projection from each 2-fibre product, naturally on
test schemes. Neither the open nor the decoration is required to be nonempty.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Open substacks and representable finite étale decorations preserve smoothness,
finite type, the Deligne--Mumford property and finite diagonal. Both resulting stacks
are separated, meaning that their diagonals are proper.
Source: Stacks, stacks-morphisms.tex, Tags 0CIP, 0CIM, 075V, 06FT, 0CPM, 050E;
algebraic.tex, Tags 05UN and 05UM
(blueprint: lem-sfb-dm-open-finite-etale-permanence).

Proof:
1. The full pullback-stable open subcategory is fibred in groupoids, and its
scheme base changes are open subschemes. Apply
`lem-sfb-representable-fibred-category-stack` over X to obtain effective descent.
2. Fullness identifies Isom_U with Isom_X. Thus U has finite diagonal. Pulling
back the etale surjective atlas of X gives an etale surjective atlas of U, so U
is Deligne--Mumford, in the recorded moduli-groupoid convention.
3. Apply `lem-sfb-finite-type-stack-affine-smooth-atlas` to X, whose etale atlas
is smooth by `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, obtaining an affine
finite-type smooth atlas A. Spec k is Noetherian, hence A is Noetherian by
`lem-weil-pbc-finite-type-over-noetherian`. Its open A_U is Noetherian and
quasi-compact by `lem-weil-pbc-noetherian-open-subscheme-noetherian`.
4. `lem-pc-open-immersion-smooth-composition` makes A_U smooth over k. Finitely
many basic opens cover A_U; each localization of the finite-type coordinate ring
is finite type. The base changes of A_U to U are those of A to X, so it is a
smooth surjective atlas. Its quasi-compactness descends to U. This proves finite
type and smoothness of U, equivalently the recorded smooth finite-type etale atlas.
5. The hypothesis gives finite etale scheme representations of every base change
of p, compatible with the projection. This is representable finite etale. Apply
`lem-sfb-representable-fibred-category-stack` over U to make Y a stack.
6. Apply `lem-sfb-representable-finite-stack-properties` to p, the DM stack U,
and the stack Y. Its Deligne--Mumford conclusion gives that property for Y.
7. For y1,y2 over T, I = Isom_U(p(y1),p(y2)) is finite over T. Over I, their
lifts are two sections of a finite etale scheme E. Finiteness makes E proper by
`lem-weil-pbc-finite-proper`, hence separated. The equality locus J of these
sections is closed in I. The 2-fibre-product definition identifies J with
Isom_Y(y1,y2): the relative represented groupoid is discrete, so a lift is unique.
`lem-weil-pbc-closed-immersion-finite` and `lem-weil-pbc-finite-composition` make
J finite over T. Consequently Y has finite diagonal.
8. B = A_U times_U Y is finite etale over A_U. It is smooth over k by
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres` and `lem-trf-smooth-composition`.
It is finite type: over the finite basic-open cover of A_U, its finite algebras
are generated over k by the base algebra generators and finitely many module generators.
9. For T mapping to Y, B times_Y T identifies with A times_X T, by forgetting
and reinserting the intermediate object and its isomorphism. Thus B is a smooth
surjective atlas of Y. Its smoothness and finite type descend; quasi-compactness
descends using finite subcovers. On a DM stack this gives the recorded etale atlas.
10. The finite diagonals of U and Y are proper by `lem-weil-pbc-finite-proper`.
This is separatedness. Empty opens and empty decorations give empty atlases;
all scheme tests and finite-subcover arguments remain valid. Only atlas maps,
never p, are assumed surjective. -/
theorem dm_open_finite_etale_permanence (k : Type u) [Field k]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (hX : IsDeligneMumfordModuliStack X)
    (hft : HasSmoothFiniteTypeModuliAtlas X) (hdiag : HasFiniteModuliDiagonal X)
    (U : OpenModuliSubstack X) :
    IsDeligneMumfordModuliStack U.category ∧
    HasSmoothFiniteTypeModuliAtlas U.category ∧ HasFiniteModuliDiagonal U.category ∧
    HasProperModuliDiagonal U.category ∧
    ∀ (Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
      (p : BasedFunctor Y U.category), IsFibredInGroupoids Y →
      (∀ (T : Over (Spec (.of k)))
          (t : BasedFunctor (discreteModuli (yoneda.obj T)) U.category),
        ∃ (E : Over (Spec (.of k))) (g : E ⟶ T)
          (e : BasedFunctor (discreteModuli (yoneda.obj E)) (moduliTwoFiberProduct t p)),
          IsFinite g.left ∧ Etale g.left ∧ IsSchemeModuliBaseChange e g) →
      IsDeligneMumfordModuliStack Y ∧ HasSmoothFiniteTypeModuliAtlas Y ∧
      HasFiniteModuliDiagonal Y ∧ IsRepresentableFiniteModuliMap p ∧
      IsEtaleModuliMap p ∧ HasProperModuliDiagonal Y := by
  sorry

end CategoryTheory
