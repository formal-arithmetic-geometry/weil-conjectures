/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.FormalSupportedModuliQuotient
public import Sheaf.AlgebraicGeometry.CompletedLocalSchemeChart
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Henselian
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Effective formal quotient atlases are completed étale scheme charts

Source: Stacks, stacks-geometry.tex, Tag 0DQZ; etale.tex, Tag 039M.
The effective-atlas specialization is the explicit argument in the DAG node
(blueprint: lem-sfb-effective-formal-chart-completed-atlas).

The formal comparison uses the existing coherent atlas action and the local
object-and-arrow presentation of the torsor quotient. The conclusion retains
the given effective map on all of `Spec R`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace CategoryTheory

/-- An effective formal quotient chart at a geometric point is obtained by completing
an étale finite-type scheme chart at a rational lift of that point.

Source: Stacks, Tag 0DQZ, with Tag 039M; the effective-atlas comparison argument
(blueprint: lem-sfb-effective-formal-chart-completed-atlas).

Proof:
1. Completeness makes the maximal-ideal pair henselian
(lem-weil-pbc-complete-pair-henselian). The algebraically closed residue field is
separably closed, so R is strictly henselian (def-weil-pbc-henselian-terminology).
2. Choose a locally finite-type étale atlas U. Its pullback along f is an étale
surjective algebraic space. Choose a scheme cover and a point above the closed
point of Spec R, using lem-sfb-stack-chartwise-smooth-etale-calculus and
 def-trf-algebraic-space. Apply lem-sbc-strict-henselian-etale-neighbourhood-section.
The resulting section gives g:Spec R→U and an actual isomorphism a g≅f.
3. Shrink U to a finite-type affine neighbourhood T of the closed image. Every
open of Spec R containing its closed point is the whole scheme, so g factors
through T. Its local ring map u:O(T,t)→R is local and has identity residue map
(lem-weil-pbc-affine-open-stalk-localization, def-weil-affine-spectrum).
4. For any local Ω-algebra C with nilpotent maximal ideal and residue Ω, unique
étale lifting identifies maps into T reducing to t with the groupoid of objects
of X(C) framed by x. Lift successively over powers of the maximal ideal; uniqueness
also proves full faithfulness and naturality (lem-sfb-etale-space-infinitesimal-lifting).
5. The formal quotient gives the same framed groupoid from continuous local maps
R→C. The pullback of the quotient atlas is the finite étale torsor; the framing
specifies its closed section, and unique étale lifting extends it uniquely.
Pass to a common finite level to compare choices
(lem-sfb-finite-group-quotient-atlas-torsor).
6. Comparing through the actual isomorphism a g≅f gives exactly the bijection
r↦r u between local maps R→C and O(T,t)→C, by affine spectrum and localization.
7. Apply this bijection with C=A/n^n and C=R/m^n. Surjectivity constructs an inverse
of u modulo n^n,m^n; injectivity proves its other composite is the identity.
The inverses commute with quotient transitions because the u_n do.
8. Take compatible sequences to obtain α:Â≃R with α composed with completion equal
to u (def-weil-pbc-adic-completion). The inverse is the required Ω-algebra isomorphism.
Both directions preserve maximal-ideal powers, hence are complete-local isomorphisms.
9. The coordinate map of Spec R→Spec Â→T is D→A→Â→R, which equals D→A→R.
Thus it is g by the affine spectrum correspondence. Compose its equality with
the actual isomorphism a g≅f. The chosen t has the prescribed closed framing. -/
theorem effectiveFormalChart_completedAtlas
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (X : BasedCategory.{v, w} (Over (Spec (.of Ω))))
    (hX : IsDeligneMumfordModuliStack X)
    (hft : ∃ (U : Over (Spec (.of Ω)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) X),
      IsEtaleModuliAtlas a ∧ LocallyOfFiniteType U.hom)
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (𝟙 (Spec (.of Ω)))))) X)
    (H : Type u) [Group H] [Finite H] (aut : H ≃* Aut (moduliChartPoint x))
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra Ω R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (ρ : IsLocalRing.ResidueField R ≃ₐ[Ω] Ω)
    (f : BasedFunctor (discreteModuli (yoneda.obj (affineActionScheme Ω R))) X)
    (hf : Nonempty (ModuliTwoIso
      ((discreteModuliMap (yoneda.map (closedResiduePoint Ω R ρ))).comp f) x))
    (σ : H →* Aut (affineActionScheme Ω R))
    (θ : FormalSupportedAtlasAction σ f {IsLocalRing.closedPoint R})
    (hformal : IsFormalSupportedModuliQuotient x σ f {IsLocalRing.closedPoint R} θ) :
    ∃ (T : Over (Spec (.of Ω)))
      (a : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (t : Over.mk (𝟙 (Spec (.of Ω))) ⟶ T),
      LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom ∧ IsEtaleModuliMap a ∧
      Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map t)).comp a) x) ∧
      ∃ (e : R ≃ₐ[Ω] pointCompletedLocalRing Ω T (t.left (IsLocalRing.closedPoint Ω)))
        (b : affineActionScheme Ω R ⟶ T),
        b.left = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          fromSpecPointCompletion Ω T (t.left (IsLocalRing.closedPoint Ω)) ∧
        Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map b)).comp a) f) := by
  sorry

end CategoryTheory
