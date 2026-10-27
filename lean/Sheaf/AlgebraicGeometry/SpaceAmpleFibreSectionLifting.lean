/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.TraceFormula.SpaceLineModuleProjInput
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.SpaceInfinitesimalSectionImageStabilization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-! # Lifting high-power fibre sections on a proper algebraic space

Source: Stacks Project, Divisors on Spaces, Tag 0D39 (lemma-ample-on-fibre),
final surjectivity assertion with F = O_X
(blueprint: lem-sfb-space-ample-fibre-section-lifting).

Sections are written in the existing cartesian scheme-test realization of the given
small-etale line module. A section on X_U is its compatible family of sections on
all scheme tests whose structural map lands in U. Descent identifies these families
with module-sheaf sections. Evaluation on the representing fibre is the canonical
pullback, using the tensor-power comparisons in TestLineFamily.powerMap.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every section of every sufficiently high power of a fibre-ample line module
lifts over a neighbourhood of the base point. The fibre is any scheme representing
the displayed sheaf pullback square; no representability of X itself is assumed.
The ordinary fibre line is the canonical scheme-test pullback of L. The lift is a
compatible family on every scheme test over U, hence precisely a section on X_U.
The last equality evaluates it on the fibre, so uses the canonical tensor-pullback
identification rather than an independently chosen map. Natural exponents encode
exactly the integers above a nonnegative bound; zero powers and empty fibres remain
included.

Source: Stacks Project, Tag 0D39, final assertion specialized to F = O_X
(blueprint: lem-sfb-space-ample-fibre-section-lifting).

Proof, following the accepted DAG split:
1. Set A = O_{T,t} and base change to Spec A, using the canonical flat local-ring
morphism (lem-weil-pbc-spec-local-ring-canonical-morphism). Localization preserves
Noetherianity (lem-weil-pbc-localization-noetherian), and proper base change
(lem-sfb-space-proper-base-change) gives a proper local-base space Z and line N.
Tensor pullback preserves local frames and identifies its closed fibre with X_t
(lem-trf-space-enlarged-etale-ringed-site-model).
2. For J = m O_Z, lem-sfb-space-conormal-uniform-vanishing gives one d0 with
H1((J^n/J^{n+1}) tensor N^d) = 0 for every n and d >= d0.
3. Set E = N^d and Q_n = E/J^n E. Local frames give the exact successive quotient
sequences, and lem-sfb-space-closed-immersion-quasi-coherent-modules identifies Q_1
with the direct image of the fibre line power. The canonical module functors
(def-trf-space-etale-module-functors) identify their global sections.
4. The long exact sequence (lem-weil-pbc-derived-functor-long-exact), using enough
injectives (lem-weil-pbc-site-sheaves-enough-injectives), makes each map of quotient
sections onto. Finite composition makes Gamma(Q_r) -> Gamma(Q_1) onto for r >= 1.
5. By lem-sfb-space-infinitesimal-section-image-stabilization this image eventually
equals the image of Gamma(E). Thus the prescribed fibre section lifts to Z.
6. The direct image of L^d is quasi-coherent
(lem-trf-space-qc-separated-quasi-coherent-pushforward). Flat base change
(lem-sfb-space-flat-direct-image-base-change), the Zariski/etale comparison
(lem-trf-scheme-zariski-etale-quasi-coherent-equivalence), and the local-ring stalk
comparison identify this lift with a germ of the direct image at t. Represent that
germ on an open neighbourhood (def-weil-pbc-module-stalk). The base-change counit
formula says that its further pullback to the fibre is the prescribed section.
In the existing cartesian realization, this representative is the compatible family
in the conclusion; its fibre evaluation uses the same tensor-pullback formula. -/
theorem exists_lift_section_of_schematic_fiber_isAmple
    (T : Scheme.{u}) [IsNoetherian T] (X : AlgebraicSpace T)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 T))) (hf : MapIsProper f)
    (L : X.Modules) (hL : X.IsLineModule L) (t : T)
    (F : SchemeTests X.obj.obj)
    (p : F.left ⟶ Over.mk (T.fromSpecResidueField t))
    (hF : IsPullback F.hom (yoneda.map p) f.hom.hom
      (yoneda.map (Over.homMk (T.fromSpecResidueField t) :
        Over.mk (T.fromSpecResidueField t) ⟶ Over.mk (𝟙 T))))
    (hample : Scheme.Modules.IsAmple F.left.left ((lineTestFamily X L hL).module F)) :
    ∃ d₀ : ℕ, ∀ (d : ℕ), d₀ ≤ d →
      ∀ v : Γ(((lineTestFamily X L hL).module F).tensorPow d, ⊤),
        ∃ (U : T.Opens) (_ : t ∈ U)
          (hFU : Set.range F.left.hom ⊆ (U : Set T))
          (s : ∀ W : SchemeTests X.obj.obj,
            Set.range W.left.hom ⊆ (U : Set T) →
              Γ(((lineTestFamily X L hL).module W).tensorPow d, ⊤)),
          (∀ (W V : SchemeTests X.obj.obj) (j : W ⟶ V)
            (hW : Set.range W.left.hom ⊆ (U : Set T))
            (hV : Set.range V.left.hom ⊆ (U : Set T)),
            s W hW = (lineTestFamily X L hL).powerMap j d (s V hV)) ∧
          s F hFU = v := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
