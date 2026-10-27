/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange

/-! # Local quasi-finiteness of representable stack morphisms

Source: Stacks Project, Tags 04XD, 0427, 03XK, 03XL and 03XN
(blueprint: lem-sfb-representable-lqf-calculus-descent).

Local quasi-finiteness uses the existing source-local algebraic-space test with
`Scheme.Hom.IsLocallyQuasiFinite`, including the finite-type requirement of Tag 01TD.
The open substack and field-point constructions are the existing recorded definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ z

open AlgebraicGeometry

namespace CategoryTheory

/-- Arbitrary base change preserves local quasi-finiteness of representable stack maps.
Source: Stacks Project, Tags 03XL and 04XC
(blueprint: lem-sfb-representable-lqf-calculus-descent).

Proof: (1) Scheme local quasi-finiteness is invariant under isomorphisms, open
source-local, stable under étale precomposition, arbitrary base change and composition;
scheme cancellation needs no condition on the second map. Use
lem-a1-scheme-lqf-etale-source-locality, lem-weil-pbc-separated-lqf-base-change,
lem-a1-scheme-lqf-composition and lem-sfb-scheme-lqf-cancellation.
(2) Verify all three hypotheses of lem-sfb-space-etale-presentation-property-criterion.
For its reverse pointwise clause factor an étale chart through its open image using
lem-a1-etale-scheme-map-open-image and descend on that image by scheme étale locality.
(3) Choose compatible étale atlases U → V → W to obtain space composition and
cancellation from their scheme counterparts, using
lem-trf-space-fibre-products-etale-covers and
lem-trf-space-representable-etale-scheme-tests.
(4) Pull back compatible presentations to obtain arbitrary space base change.
(5) Pull an open cover back to a scheme atlas; apply the pointwise scheme definition
on its covering open subschemes, including the empty-source case.
(6) For a space over a scheme, choose a source scheme atlas and descend its local
quasi-finiteness along the surjective flat locally finitely presented scheme cover.
Use def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and
lem-sfb-scheme-lqf-fpqc-descent; no quasi-compactness is needed.
(7) Scheme tests extend to arbitrary algebraic-space tests by choosing target and
source étale atlases and using lem-sfb-representable-pullback-over-space.
(8) The representable-calculus and algebraic-stack-fibre-product lemmas give the
representable pullback; associativity of the triple construction identifies each
scheme test with a scheme test of the original map.
(9) Apply space composition and open-source locality to every scheme test, using
lem-sfb-stack-chartwise-smooth-etale-calculus for the pulled-back open cover.
(10) For fppf target descent and a test T → B, set H = V ×_B T and Z = A ×_B T.
Choose a surjective étale scheme chart D → H. The composite D → T is surjective,
flat and locally finitely presented. The specified comparison in the fibre-product
triples identifies Z ×_T D with (A ×_B V) ×_V D over D. Space base change gives
local quasi-finiteness there, and (6) descends it to Z → T. The cover is H → T,
not Z ×_T H → T; no surjectivity of f is assumed. -/
theorem representable_lqf_baseChange {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C) (f : BasedFunctor A B) (g : BasedFunctor C B)
    (hf : IsRepresentableByAlgebraicSpaces f)
    (hq : ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite f) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliTwoFiberFst g f) := by
  sorry

/-- Composition preserves local quasi-finiteness of representable stack maps.
Source: Stacks Project, Tags 03XK and 04XC
(blueprint: lem-sfb-representable-lqf-calculus-descent).

Proof: (1) Scheme local quasi-finiteness is invariant under isomorphisms, open
source-local, stable under étale precomposition, arbitrary base change and composition;
scheme cancellation needs no condition on the second map. Use
lem-a1-scheme-lqf-etale-source-locality, lem-weil-pbc-separated-lqf-base-change,
lem-a1-scheme-lqf-composition and lem-sfb-scheme-lqf-cancellation.
(2) Verify all three hypotheses of lem-sfb-space-etale-presentation-property-criterion.
For its reverse pointwise clause factor an étale chart through its open image using
lem-a1-etale-scheme-map-open-image and descend on that image by scheme étale locality.
(3) Choose compatible étale atlases U → V → W to obtain space composition and
cancellation from their scheme counterparts, using
lem-trf-space-fibre-products-etale-covers and
lem-trf-space-representable-etale-scheme-tests.
(4) Pull back compatible presentations to obtain arbitrary space base change.
(5) Pull an open cover back to a scheme atlas; apply the pointwise scheme definition
on its covering open subschemes, including the empty-source case.
(6) For a space over a scheme, choose a source scheme atlas and descend its local
quasi-finiteness along the surjective flat locally finitely presented scheme cover.
Use def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and
lem-sfb-scheme-lqf-fpqc-descent; no quasi-compactness is needed.
(7) Scheme tests extend to arbitrary algebraic-space tests by choosing target and
source étale atlases and using lem-sfb-representable-pullback-over-space.
(8) The representable-calculus and algebraic-stack-fibre-product lemmas give the
representable pullback; associativity of the triple construction identifies each
scheme test with a scheme test of the original map.
(9) Apply space composition and open-source locality to every scheme test, using
lem-sfb-stack-chartwise-smooth-etale-calculus for the pulled-back open cover.
(10) For fppf target descent and a test T → B, set H = V ×_B T and Z = A ×_B T.
Choose a surjective étale scheme chart D → H. The composite D → T is surjective,
flat and locally finitely presented. The specified comparison in the fibre-product
triples identifies Z ×_T D with (A ×_B V) ×_V D over D. Space base change gives
local quasi-finiteness there, and (6) descends it to Z → T. The cover is H → T,
not Z ×_T H → T; no surjectivity of f is assumed. -/
theorem representable_lqf_comp {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C) (f : BasedFunctor A B) (g : BasedFunctor B C)
    (hf : IsRepresentableByAlgebraicSpaces f) (hg : IsRepresentableByAlgebraicSpaces g)
    (hfq : ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite f)
    (hgq : ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite g) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (f.comp g) := by
  sorry

/-- Local quasi-finiteness is local for an arbitrary open cover of the source.
The covering condition tests all field-valued objects; an open cover contains each such
object in one member, even when a general scheme-valued object straddles several opens.
Source: Stacks Project, Tags 03XJ and 040Z
(blueprint: lem-sfb-representable-lqf-calculus-descent).

Proof: (1) Scheme local quasi-finiteness is invariant under isomorphisms, open
source-local, stable under étale precomposition, arbitrary base change and composition;
scheme cancellation needs no condition on the second map. Use
lem-a1-scheme-lqf-etale-source-locality, lem-weil-pbc-separated-lqf-base-change,
lem-a1-scheme-lqf-composition and lem-sfb-scheme-lqf-cancellation.
(2) Verify all three hypotheses of lem-sfb-space-etale-presentation-property-criterion.
For its reverse pointwise clause factor an étale chart through its open image using
lem-a1-etale-scheme-map-open-image and descend on that image by scheme étale locality.
(3) Choose compatible étale atlases U → V → W to obtain space composition and
cancellation from their scheme counterparts, using
lem-trf-space-fibre-products-etale-covers and
lem-trf-space-representable-etale-scheme-tests.
(4) Pull back compatible presentations to obtain arbitrary space base change.
(5) Pull an open cover back to a scheme atlas; apply the pointwise scheme definition
on its covering open subschemes, including the empty-source case.
(6) For a space over a scheme, choose a source scheme atlas and descend its local
quasi-finiteness along the surjective flat locally finitely presented scheme cover.
Use def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and
lem-sfb-scheme-lqf-fpqc-descent; no quasi-compactness is needed.
(7) Scheme tests extend to arbitrary algebraic-space tests by choosing target and
source étale atlases and using lem-sfb-representable-pullback-over-space.
(8) The representable-calculus and algebraic-stack-fibre-product lemmas give the
representable pullback; associativity of the triple construction identifies each
scheme test with a scheme test of the original map.
(9) Apply space composition and open-source locality to every scheme test, using
lem-sfb-stack-chartwise-smooth-etale-calculus for the pulled-back open cover.
(10) For fppf target descent and a test T → B, set H = V ×_B T and Z = A ×_B T.
Choose a surjective étale scheme chart D → H. The composite D → T is surjective,
flat and locally finitely presented. The specified comparison in the fibre-product
triples identifies Z ×_T D with (A ×_B V) ×_V D over D. Space base change gives
local quasi-finiteness there, and (6) descends it to Z → T. The cover is H → T,
not Z ×_T H → T; no surjectivity of f is assumed. -/
theorem representable_lqf_openCover {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (f : BasedFunctor A B) (hf : IsRepresentableByAlgebraicSpaces f)
    (I : Type z) (U : I → OpenModuliSubstack A)
    (hcover : ∀ x : ModuliFieldObject A, ∃ i : I, (U i).property x.val) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite f ↔
      ∀ i : I, ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite
        ((fullModuliInclusion A (U i).property).comp f) := by
  sorry

/-- A representable surjective flat locally finitely presented algebraic-space
target cover detects local quasi-finiteness. Surjectivity on the actual field-point
classes is field-extension local lifting.
Source: Stacks Project, Tags 04XD and 0427
(blueprint: lem-sfb-representable-lqf-calculus-descent).

Proof: (1) Scheme local quasi-finiteness is invariant under isomorphisms, open
source-local, stable under étale precomposition, arbitrary base change and composition;
scheme cancellation needs no condition on the second map. Use
lem-a1-scheme-lqf-etale-source-locality, lem-weil-pbc-separated-lqf-base-change,
lem-a1-scheme-lqf-composition and lem-sfb-scheme-lqf-cancellation.
(2) Verify all three hypotheses of lem-sfb-space-etale-presentation-property-criterion.
For its reverse pointwise clause factor an étale chart through its open image using
lem-a1-etale-scheme-map-open-image and descend on that image by scheme étale locality.
(3) Choose compatible étale atlases U → V → W to obtain space composition and
cancellation from their scheme counterparts, using
lem-trf-space-fibre-products-etale-covers and
lem-trf-space-representable-etale-scheme-tests.
(4) Pull back compatible presentations to obtain arbitrary space base change.
(5) Pull an open cover back to a scheme atlas; apply the pointwise scheme definition
on its covering open subschemes, including the empty-source case.
(6) For a space over a scheme, choose a source scheme atlas and descend its local
quasi-finiteness along the surjective flat locally finitely presented scheme cover.
Use def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and
lem-sfb-scheme-lqf-fpqc-descent; no quasi-compactness is needed.
(7) Scheme tests extend to arbitrary algebraic-space tests by choosing target and
source étale atlases and using lem-sfb-representable-pullback-over-space.
(8) The representable-calculus and algebraic-stack-fibre-product lemmas give the
representable pullback; associativity of the triple construction identifies each
scheme test with a scheme test of the original map.
(9) Apply space composition and open-source locality to every scheme test, using
lem-sfb-stack-chartwise-smooth-etale-calculus for the pulled-back open cover.
(10) For fppf target descent and a test T → B, set H = V ×_B T and Z = A ×_B T.
Choose a surjective étale scheme chart D → H. The composite D → T is surjective,
flat and locally finitely presented. The specified comparison in the fibre-product
triples identifies Z ×_T D with (A ×_B V) ×_V D over D. Space base change gives
local quasi-finiteness there, and (6) descends it to Z → T. The cover is H → T,
not Z ×_T H → T; no surjectivity of f is assumed. -/
theorem representable_lqf_fppf_target {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (f : BasedFunctor A B) (hf : IsRepresentableByAlgebraicSpaces f)
    (V : AlgebraicSpace S) (q : BasedFunctor (discreteModuli V.obj.obj) B)
    (hq : IsRepresentableByAlgebraicSpaces q)
    (hs : Function.Surjective (moduliPointMap q))
    (hflat : ModuliSpaceTest @Flat q)
    (hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite f ↔
      ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliTwoFiberFst q f) := by
  sorry

/-- Local quasi-finiteness of a composite of algebraic-space maps implies
local quasi-finiteness of its first factor, with no condition on the second factor.
Source: Stacks Project, Tag 03XN
(blueprint: lem-sfb-representable-lqf-calculus-descent).

Proof: (1) Scheme local quasi-finiteness is invariant under isomorphisms, open
source-local, stable under étale precomposition, arbitrary base change and composition;
scheme cancellation needs no condition on the second map. Use
lem-a1-scheme-lqf-etale-source-locality, lem-weil-pbc-separated-lqf-base-change,
lem-a1-scheme-lqf-composition and lem-sfb-scheme-lqf-cancellation.
(2) Verify all three hypotheses of lem-sfb-space-etale-presentation-property-criterion.
For its reverse pointwise clause factor an étale chart through its open image using
lem-a1-etale-scheme-map-open-image and descend on that image by scheme étale locality.
(3) Choose compatible étale atlases U → V → W to obtain space composition and
cancellation from their scheme counterparts, using
lem-trf-space-fibre-products-etale-covers and
lem-trf-space-representable-etale-scheme-tests.
(4) Pull back compatible presentations to obtain arbitrary space base change.
(5) Pull an open cover back to a scheme atlas; apply the pointwise scheme definition
on its covering open subschemes, including the empty-source case.
(6) For a space over a scheme, choose a source scheme atlas and descend its local
quasi-finiteness along the surjective flat locally finitely presented scheme cover.
Use def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and
lem-sfb-scheme-lqf-fpqc-descent; no quasi-compactness is needed.
(7) Scheme tests extend to arbitrary algebraic-space tests by choosing target and
source étale atlases and using lem-sfb-representable-pullback-over-space.
(8) The representable-calculus and algebraic-stack-fibre-product lemmas give the
representable pullback; associativity of the triple construction identifies each
scheme test with a scheme test of the original map.
(9) Apply space composition and open-source locality to every scheme test, using
lem-sfb-stack-chartwise-smooth-etale-calculus for the pulled-back open cover.
(10) For fppf target descent and a test T → B, set H = V ×_B T and Z = A ×_B T.
Choose a surjective étale scheme chart D → H. The composite D → T is surjective,
flat and locally finitely presented. The specified comparison in the fibre-product
triples identifies Z ×_T D with (A ×_B V) ×_V D over D. Space base change gives
local quasi-finiteness there, and (6) descends it to Z → T. The cover is H → T,
not Z ×_T H → T; no surjectivity of f is assumed. -/
theorem space_lqf_of_comp {S : Scheme.{u}} {A B C : AlgebraicSpace S}
    (f : A ⟶ B) (g : B ⟶ C) (h : SpaceMapIsLocallyQuasiFinite (f ≫ g)) :
    SpaceMapIsLocallyQuasiFinite f := by
  sorry

end CategoryTheory
