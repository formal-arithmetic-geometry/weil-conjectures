/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.AlgebraicGeometry.ZariskiEtaleFinitenessPreservation
import Sheaf.AlgebraicGeometry.ZariskiEtaleFinitenessLocalRecovery
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Sheaf.AlgebraicGeometry.FpqcFiniteTypeModuleDescent
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# Exactness and finiteness for the Zariski-small-étale module comparison

Source: Stacks Project, Descent, Tags 06VE(5) and 05VG
(blueprint: lem-sfb-scheme-etale-module-exact-finiteness-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical tensor-extension functor of the recorded comparison, with its
proof-only context supplied by that comparison theorem. This is the existing
`ZariskiEtaleModuleContext.extension`, not a new construction of associated sheaves.
The chosen context contains only continuity and adjoint-existence proofs; its
underlying functor is the specified ringed-site tensor pullback. On quasi-coherent
modules the comparison theorem identifies it naturally and linearly with
`etaleTensorSectionsSheaf`, including the pullback restriction maps.
Source: Stacks Project, Descent, Tags 03FH, 06VE and 05VG
(blueprint: lem-sfb-scheme-etale-module-exact-finiteness-comparison). -/
abbrev schemeEtaleModuleComparison (T : Scheme.{u}) : T.Modules ⥤ SmallEtaleModules T :=
  (Classical.choose scheme_zariski_etale_quasiCoherent_equivalence T).extension

private theorem comparison_mono (T : Scheme.{u}) {F G : T.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) [Mono f] :
    Mono ((schemeEtaleModuleComparison T).map f) := by
  obtain ⟨e, _, he, _⟩ :=
    (Classical.choose_spec scheme_zariski_etale_quasiCoherent_equivalence).2.2
  apply (SheafOfModules.toSheaf (smallEtaleModuleRing T)).mono_of_mono_map
  apply (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}).mono_of_mono_map
  change Mono (((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
    ((schemeEtaleModuleComparison T).map f)).hom)
  have hm (V : T.Etale) :
      Mono (((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
        ((schemeEtaleModuleComparison T).map f)).hom.app (Opposite.op V)) := by
    have : CategoryTheory.Limits.PreservesFiniteLimits (tensorPullback V.hom) :=
      (flat_module_pullback_exact_pushforward_injective V.hom).1.1
    have : Mono ((tensorPullback V.hom).map f) := inferInstance
    have hsec : Mono (((tensorPullback V.hom).map f).app ⊤) := by
      have : Mono ((toPresheaf V.left).map ((tensorPullback V.hom).map f)) :=
        inferInstance
      exact inferInstanceAs (Mono
        (((toPresheaf V.left).map ((tensorPullback V.hom).map f)).app (Opposite.op ⊤)))
    have hcomp : Mono ((e T F).hom.hom.app (Opposite.op V) ≫
        ((tensorPullback V.hom).map f).app ⊤) := inferInstance
    rw [← he T F G f V] at hcomp
    exact mono_of_mono _ ((e T G).hom.hom.app (Opposite.op V))
  have : ∀ V, Mono (((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
      ((schemeEtaleModuleComparison T).map f)).hom.app V) := fun V ↦ hm V.unop
  exact NatTrans.mono_of_mono_app _

/-- The associated-small-étale-module functor is exact into the ambient module
category and preserves and reflects finite type and finite presentation.
Source: Stacks Project, Descent, Tag 06VE, lemma-equivalence-quasi-coherent-limits (5),
and Tag 05VG, lemma-equivalence-quasi-coherent-properties
(blueprint: lem-sfb-scheme-etale-module-exact-finiteness-comparison).

Proof:
1. The ringed-topos module adjunction makes tensor extension a left adjoint, hence
   it preserves colimits, zero objects, finite sums and cokernels. Quasi-coherent
   cokernels are ambient cokernels. The tensor-section formula identifies the
   extension of the structure sheaf, and therefore its finite sums, with the small
   etale structure sheaf and its finite sums. Use the recorded comparison,
   lem-weil-pbc-ringed-topoi-module-adjunction,
   lem-weil-pbc-left-adjoint-preserves-colimits and
   lem-weil-pbc-quasi-coherent-module-cokernel-image.
2. Kernels of quasi-coherent maps are quasi-coherent. Every small-etale test map
   is flat, so its module pullback is exact. Global sections are left exact, hence
   tensor sections compute the kernel objectwise. Module-sheaf kernels are
   sectionwise. Together with step 1 this proves ambient short exactness. Use
   lem-weil-pbc-quasi-coherent-module-kernel, def-weil-etale-morphism,
   lem-weil-pbc-flat-module-pullback-exact-pushforward-injective,
   lem-sc-global-sections-left-exact and lem-weil-pbc-module-sheaves-limits-sectionwise.
3. Apply exactness on each Zariski open carrying finite generators or a finite
   presentation. The finite free modules remain finite free. Etale composition
   and cancellation identify the etale slice over that open with its own small
   etale site; tensor-pullback composition identifies the restricted associated
   sheaf with that of the restricted module, with the same restrictions. A
   Zariski open cover is an etale cover. This proves both forward implications,
   using lem-weil-pbc-etale-composition-cancellation and
   lem-pc-module-pullback-identity-composition.
4. Conversely, take an etale cover carrying finite generators or a finite
   presentation. The same slice and tensor-composition identifications give the
   associated sheaf of each pulled-back quasi-coherent module. The comparison's
   full faithfulness lifts the finite-free presentation maps to Zariski maps.
   In the finite-type case their quasi-coherent cokernel extends to zero, and
   faithfulness makes it zero. In the finite-presentation case the induced map
   from the Zariski cokernel extends to an isomorphism; full faithfulness lifts
   its inverse and its inverse equations. Thus the pullbacks have the required
   Zariski finiteness property. Use the recorded comparison,
   lem-weil-pbc-module-pullback-quasi-coherent, the tensor composition theorem,
   the quasi-coherent cokernel theorem and etale composition/cancellation.
5. Etale covers are fpqc by lem-weil-pbc-fpqc-finer-than-etale. Apply
   lem-sfb-fpqc-finite-type-module-descent for finite type and clause (2) of
   lem-pc-fpqc-descent for finite presentation. No Noetherian assumption enters.
   Empty schemes, empty covers, zero modules and zero finite ranks are allowed. -/
theorem scheme_etale_module_exact_finiteness_comparison (T : Scheme.{u}) :
    (∀ (S : ShortComplex T.Modules),
      S.X₁.IsQuasicoherent → S.X₂.IsQuasicoherent → S.X₃.IsQuasicoherent →
        S.ShortExact →
          ∃ h : (schemeEtaleModuleComparison T).map S.f ≫
              (schemeEtaleModuleComparison T).map S.g = 0,
            (ShortComplex.mk ((schemeEtaleModuleComparison T).map S.f)
              ((schemeEtaleModuleComparison T).map S.g) h).ShortExact) ∧
    (∀ (F : T.Modules) [F.IsQuasicoherent],
      (F.IsFiniteType ↔ ((schemeEtaleModuleComparison T).obj F).IsFiniteType) ∧
      (F.IsFinitePresentation ↔
        ((schemeEtaleModuleComparison T).obj F).IsFinitePresentation)) := by
  let c := Classical.choose scheme_zariski_etale_quasiCoherent_equivalence
  have hrestriction : (c T).restriction.Additive := { map_add := rfl }
  have hadj := (c T).adjunction
  have : (schemeEtaleModuleComparison T).IsLeftAdjoint := hadj.isLeftAdjoint
  have : (schemeEtaleModuleComparison T).Additive := hadj.left_adjoint_additive
  constructor
  · intro S h₁ h₂ _ hS
    have := h₁
    have := h₂
    have := hS.mono_f
    have := hS.epi_g
    have : Mono ((schemeEtaleModuleComparison T).map S.f) := comparison_mono T S.f
    refine ⟨(S.map (schemeEtaleModuleComparison T)).zero, ?_⟩
    exact ShortComplex.ShortExact.mk'
      (hS.exact.map_of_epi_of_preservesCokernel (schemeEtaleModuleComparison T)
        inferInstance inferInstance) inferInstance inferInstance
  · intro F hF
    have hforward := zariskiEtale_finiteness_preservation T (c T) F
    have hlocal := zariskiEtale_finiteness_local_recovery T (c T) F
    refine ⟨⟨hforward.1, ?_⟩, ⟨hforward.2, ?_⟩⟩
    · intro h
      obtain ⟨I, Y, f, _, hf, hfinite⟩ := hlocal.1 h
      exact isFiniteType_of_fpqc_tensorPullback F hF Y f hf hfinite
    · intro h
      obtain ⟨I, Y, f, _, hf, hfinite⟩ := hlocal.2 h
      have hcover : Sieve.ofArrows Y f ∈ Scheme.fpqcTopology T :=
        Precoverage.generate_mem_toGrothendieck hf
      exact isFinitePresentation_of_toDescentData_iso f hcover
        ((modulesPseudofunctor.toDescentData f).obj F) F ⟨Iso.refl _⟩ hfinite

end AlgebraicGeometry.Scheme.Modules
