/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
import Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityExact
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Smooth transitivity for relative differential sheaves

Source: Stacks Project, Morphisms, Tag 02K4, `lemma-triangle-differentials-smooth`
(blueprint: lem-sfb-smooth-differential-transitivity-short-exact).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

private theorem app_injective_of_mono {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] (U : X.Opens) : Function.Injective (f.app U) := by
  have hm := Functor.map_mono (Modules.toPresheaf X) f
  exact (AddCommGrpCat.mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app _).mp hm (op U))

private theorem mono_differential_extension {R B C : CommRingCat.{u}}
    (f : R ⟶ B) (k : B ⟶ C) (l : R ⟶ C) (fac : f ≫ k = l)
    (hs : k.hom.FormallySmooth)
    (v : (ModuleCat.extendScalars k.hom).obj (CommRingCat.KaehlerDifferential f) ⟶
      CommRingCat.KaehlerDifferential l)
    (hv : ∀ (a : C) (b : B),
      v (a • @id ((ModuleCat.extendScalars k.hom).obj
        (CommRingCat.KaehlerDifferential f))
          ((ModuleCat.extendRestrictScalarsAdj k.hom).unit.app
            (CommRingCat.KaehlerDifferential f) (CommRingCat.KaehlerDifferential.d b))) =
        a • CommRingCat.KaehlerDifferential.d (k b)) : Mono v := by
  subst l
  let := f.hom.toAlgebra
  let := k.hom.toAlgebra
  let := (f ≫ k).hom.toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallySmooth B C := hs
  let d : (ModuleCat.extendScalars k.hom).obj (CommRingCat.KaehlerDifferential f) ⟶
      CommRingCat.KaehlerDifferential (f ≫ k) :=
    ModuleCat.ofHom (KaehlerDifferential.mapBaseChange R B C)
  have he : v = d := by
    apply ((ModuleCat.extendRestrictScalarsAdj k.hom).homEquiv _ _).injective
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    change v ((ModuleCat.extendRestrictScalarsAdj k.hom).unit.app
      (CommRingCat.KaehlerDifferential f) (CommRingCat.KaehlerDifferential.d b)) = _
    have hd : d ((ModuleCat.extendRestrictScalarsAdj k.hom).unit.app
        (CommRingCat.KaehlerDifferential f) (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d (k b) := by
      change KaehlerDifferential.mapBaseChange R B C
        (1 ⊗ₜ[B] (KaehlerDifferential.D R B b)) = KaehlerDifferential.D R C (k b)
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
      rfl
    have hv1 : v ((ModuleCat.extendRestrictScalarsAdj k.hom).unit.app
        (CommRingCat.KaehlerDifferential f) (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d (k b) := by
      simpa only [one_smul, id_eq] using hv 1 b
    exact hv1.trans hd.symm
  rw [he, ModuleCat.mono_iff_injective]
  change Function.Injective (KaehlerDifferential.mapBaseChange R B C)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R B C x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- If `h : X ⟶ Y` is smooth, the canonical differential transitivity sequence
`0 → h* Ω(Y/S) → Ω(X/S) → Ω(X/Y) → 0` is short exact. The last arrow is specified
on the universal derivations on every source open; the first arrow is the recorded
canonical tensor-pullback differential map. There is no assumption on `g : Y ⟶ S`.

Source: Stacks Project, Morphisms, Tag 02K4, `lemma-triangle-differentials-smooth`
(blueprint: lem-sfb-smooth-differential-transitivity-short-exact).

Proof:
1. Apply `lem-a1-differential-sheaf-transitivity-exact`. It gives the canonical
   last arrow with the displayed derivation formula, middle exactness and an
   epimorphism onto the last term. Only monicity of the first arrow remains.
2. Fix x in X, y = h(x), s = g(y), and use the actual stalk maps R → B → C.
   By `lem-weil-pbc-module-stalk-pullback` and
   `lem-sfb-relative-differentials-stalk`, the first stalk arrow identifies with
   C tensor_B Omega(B/R) → Omega(C/R), c tensor db ↦ c d(b).
   To check this identification, represent b by a section near y; the pullback
   stalk comparison carries its pulled-back differential to 1 tensor db, and
   `def-a1-relative-differentials-pullback-map` sends it to d(h-sharp b).
   The differential-stalk comparison carries this germ to d(b). Linearity and
   generation by these tensors give the formula on the whole source.
3. `lem-sfb-smooth-stalk-formally-smooth` makes B → C formally smooth.
   `lem-weil-pbc-formally-smooth-differentials-injective` gives injectivity of
   this stalk arrow. No condition on R → B is required.
4. If a section of the first term maps to zero, all its germs are zero by step 3.
   The germ equality criterion of `def-weil-pbc-module-stalk` makes it locally
   zero, and sheaf uniqueness makes it zero. Kernels are sectionwise by
   `def-weil-sheaf-of-modules-category`, so the first arrow is a monomorphism.
   Combine with step 1 using `def-weil-pbc-exact-sequence`. The empty cover
   handles empty opens and the empty scheme as well. -/
theorem relativeDifferentials_transitivity_shortExact_of_smooth {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) [Smooth h] :
    ∃ q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials,
      (∀ (O : X.Opens) (a : Γ(X, O)),
        q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
          h.relativeDifferentialsDerivation.d (X := op O) a) ∧
      ∃ z : g.relativeDifferentialsPullbackMap h ≫ q = 0,
        (ShortComplex.mk (g.relativeDifferentialsPullbackMap h) q z).ShortExact := by
  obtain ⟨q, hq, ⟨z, hex⟩, hepi, _, haff, _⟩ :=
    relativeDifferentials_transitivity_exact h g
  have hm (U : X.affineOpens) (V : Y.affineOpens) (W : S.affineOpens)
      (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ g ⁻¹ᵁ W.1) :
      Mono ((Modules.restrictFunctor U.2.fromSpec).map
        (g.relativeDifferentialsPullbackMap h)) := by
    obtain ⟨θ, _, uA, vA, hu, _, _, _, hd, _⟩ := haff U V W hUV hVW
    have hcomp : g.appLE W.1 V.1 hVW ≫ h.appLE V.1 U.1 hUV =
        (h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx)) := by
      exact h.appLE_comp_appLE g W.1 V.1 U.1 hVW hUV
    have : Mono uA := mono_differential_extension _ _ _ hcomp
      (h.smooth_appLE V.2 U.2 hUV).formallySmooth uA hu
    let : PreservesFiniteLimits (tilde.functor Γ(X, U.1)) :=
      tilde_preserves_finite_limits Γ(X, U.1)
    have : Mono ((tilde.functor Γ(X, U.1)).map uA) := Functor.map_mono _ _
    have : Mono (θ.hom ≫ (tilde.functor Γ(X, U.1)).map uA) := inferInstance
    rw [← hd] at this
    exact mono_of_mono _ ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
      (fun _ hx ↦ hVW (hUV hx))).hom
  have : Mono (g.relativeDifferentialsPullbackMap h) := by
    constructor
    intro T a b hab
    ext O t
    apply (Modules.isSheaf ((Modules.tensorPullback h).obj
      g.relativeDifferentials)).section_ext
    intro x hxO
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g (h x))) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hxW (W.2.preimage g.continuous)
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ O ⊓ h ⁻¹ᵁ V from ⟨hxO, hxV⟩)
        (O.2.inter (V.2.preimage h.continuous))
    have hUV : U ≤ h ⁻¹ᵁ V := hUO.trans inf_le_right
    have : Mono ((Modules.restrictFunctor hU.fromSpec).map
        (g.relativeDifferentialsPullbackMap h)) :=
      hm ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ hUV hVW
    have hi := app_injective_of_mono
      ((Modules.restrictFunctor hU.fromSpec).map (g.relativeDifferentialsPullbackMap h)) ⊤
    change Function.Injective
      ((g.relativeDifferentialsPullbackMap h).app (hU.fromSpec ''ᵁ ⊤)) at hi
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec] at hi
    have hUO' : U ≤ O := hUO.trans inf_le_left
    let i : U ⟶ O := homOfLE hUO'
    refine ⟨U, hUO', hxU, hi ?_⟩
    have hn := congrArg (fun f ↦ f.app U (T.presheaf.map i.op t)) hab
    have ha := congrArg (fun f ↦ f t) (a.mapPresheaf.naturality i.op)
    have hb := congrArg (fun f ↦ f t) (b.mapPresheaf.naturality i.op)
    change a.app U (T.presheaf.map i.op t) =
      ((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map i.op
        (a.app O t) at ha
    change b.app U (T.presheaf.map i.op t) =
      ((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map i.op
        (b.app O t) at hb
    change (g.relativeDifferentialsPullbackMap h).app U
        (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map i.op
          (a.app O t)) =
      (g.relativeDifferentialsPullbackMap h).app U
        (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map i.op
          (b.app O t))
    rw [← ha, ← hb]
    exact hn
  exact ⟨q, hq, z, ⟨hex⟩⟩

end AlgebraicGeometry.Scheme.Hom
