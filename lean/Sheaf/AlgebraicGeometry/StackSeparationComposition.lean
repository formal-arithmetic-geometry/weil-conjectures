/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Composition preserves proper relative diagonals of DM stacks

Source: Stacks Project, stacks-morphisms.tex, Tag 050K, separated case;
Tags 050H, 06N3 and 06MB; spaces-morphisms.tex, Tag 03XX;
more-morphisms.tex, Tag 02LS (blueprint: lem-sfb-stack-separation-composition).

The scheme tests retain an equivalence with the actual 2-base change and a
2-isomorphism identifying its projection. Properness of a stack map itself is
not assumed. The algebraic-space interpretation and its finite scheme
representative are stated separately below.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Proper relative diagonals are preserved by composition of DM stack morphisms.
Source: Stacks Project, stacks-morphisms.tex, Tag 050K, separated case
(blueprint: lem-sfb-stack-separation-composition).

Proof: Steps 1--4 of the node expand the 2-fibre product on each test scheme T.
The pullback of a diagonal at (x₁,x₂,ε) is the discrete groupoid of isomorphisms
β with h(β)=ε: send (x,a,b) to b a⁻¹, with inverse β ↦ (x₁,id,β).
An arrow is forced to be (a')⁻¹a, so this is an equivalence on arrows too.
For a test (x₁,x₂,θ) of the composite, properness of Δ_g supplies a scheme E
proper over T parametrizing α with g(α)=θ. Its identity gives the universal α.
Properness of Δ_f then supplies a scheme V proper over E parametrizing β
with f(β)=α. Forgetting α identifies V with the composite-diagonal pullback;
the inverse sends β to (f(β),β). These formulas commute with restrictions and
identify the projection with V → E → T. Step 5 applies scheme proper-composition
(lem-weil-pbc-proper-composition). No finite-type assumption on f or g occurs. -/
theorem proper_moduli_diagonal_comp {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)}
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (hC : IsDeligneMumfordModuliStack C) (f : BasedFunctor A B) (g : BasedFunctor B C)
    (hf : ModuliSchemeTest @IsProper (moduliRelativeDiagonal f))
    (hg : ModuliSchemeTest @IsProper (moduliRelativeDiagonal g)) :
    ModuliSchemeTest @IsProper (moduliRelativeDiagonal (f.comp g)) := by
  sorry

/-- Every scheme base change of a relative DM diagonal is an algebraic space
locally quasi-finite over the test scheme, with no finiteness hypothesis on the map.
Source: Stacks Project, Tags 045G, 06N3, 06MB, 06G6, 03ZJ, 06CR, 03ZI and 02V5
(blueprint: lem-sfb-stack-separation-composition).

Proof: Step 1 identifies the diagonal pullback with isomorphisms β satisfying
h(β)=ε. Step 6 applies lem-sfb-dm-isom-space-unramified to obtain unramified
Isom spaces I_P and I_Q over T. The pullback I_P ×_{I_Q,ε} T is an algebraic
space by lem-trf-space-fibre-products-etale-covers and represents those β,
naturally on all T-schemes. Step 7 applies unramified cancellation to I_P → I_Q,
then base change to this pullback (lem-sfb-space-unramified-permanence).
Every representable étale chart is unramified, as is its composite with the
unramified structure map. Apply lem-weil-pbc-unramified-quasi-finite-at-points
to each resulting scheme map to T. This gives precisely ModuliSpaceTest. -/
theorem relative_moduli_diagonal_locallyQuasiFinite {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (f : BasedFunctor A B) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliRelativeDiagonal f) := by
  sorry

/-- Each relative DM diagonal base change has equivalent scheme and algebraic-space tests.
Source: Stacks Project, stacks-morphisms.tex, Tag 050K; spaces-morphisms.tex,
Tag 03XX and definition-proper; more-morphisms.tex, Tag 02LS
(blueprint: lem-sfb-stack-separation-composition).

Proof: Steps 6--7 give an algebraic-space representative locally quasi-finite
on every étale scheme chart, as in relative_moduli_diagonal_locallyQuasiFinite.
Step 8 uses separatedness in space properness and
lem-a1-separated-locally-qf-space-representable to obtain a scheme representative
over the test scheme. On represented maps, identity scheme charts identify
separatedness, quasi-compactness, local finite type and universal closedness
with their scheme definitions (def-weil-proper-morphism). Thus the representing
scheme projection is proper. Conversely a proper scheme representative satisfies
these same space tests. Transport the projection comparisons along the representing
isomorphism to retain HasSpaceBaseChange and IsSchemeModuliBaseChange. -/
theorem proper_moduli_diagonal_iff_space_tests {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (f : BasedFunctor A B) (T : Over S)
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct f f))
    (E : AlgebraicSpace S) (p : E.obj.obj ⟶ yoneda.obj T)
    (hE : HasSpaceBaseChange (moduliRelativeDiagonal f) T t E p) :
    SpaceMapIsProper (ObjectProperty.homMk ⟨p⟩ : E ⟶ AlgebraicSpace.schemeSpace T) ↔
      ∃ (R : Over S) (q : R ⟶ T)
          (e : BasedFunctor (discreteModuli (yoneda.obj R))
            (moduliTwoFiberProduct t (moduliRelativeDiagonal f))),
        IsSchemeModuliBaseChange e q ∧ IsProper q.left := by
  sorry

/-- A proper chartwise locally quasi-finite algebraic space over a scheme is finite
and represented by a scheme over that target.
Source: Stacks Project, spaces-morphisms.tex, Tag 03XX and definition-proper;
more-morphisms.tex, Tag 02LS, (3) implies (1)
(blueprint: lem-sfb-stack-separation-composition).

Proof: Step 8 applies lem-a1-separated-locally-qf-space-representable to the
closed-immersion diagonal supplied by properness and the chart hypothesis.
The resulting isomorphism identifies the actual structure map with a scheme
map q. Identity charts identify space properness with scheme properness and
give local quasi-finiteness of q. Apply pqf-lem-proper-lqf-finite to q.
The representing isomorphism commutes with the map to T, as required. -/
theorem proper_locallyQuasiFinite_space_to_scheme_finite {S : Scheme.{u}}
    (T : Over S) (E : AlgebraicSpace S) (p : E.obj.obj ⟶ yoneda.obj T)
    (hqf : ∀ (V : Over S) (a : yoneda.obj V ⟶ E.obj.obj), AlgebraicSpace.IsEtale a →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ p)).left)
    (hp : SpaceMapIsProper (ObjectProperty.homMk ⟨p⟩ : E ⟶ AlgebraicSpace.schemeSpace T)) :
    ∃ (Z : Over S) (q : Z ⟶ T) (e : yoneda.obj Z ≅ E.obj.obj),
      e.hom ≫ p = yoneda.map q ∧ IsFinite q.left := by
  sorry

end CategoryTheory
