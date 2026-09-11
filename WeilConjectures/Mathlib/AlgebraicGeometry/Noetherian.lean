/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Noetherian schemes, associated points, and the dévissage of a coherent sheaf

The first part of this file records that a base change of a morphism locally of finite type has
locally noetherian source.

The second part defines the *associated points* of a sheaf of modules on a scheme: a point `x`
is associated to `F` when the maximal ideal of `𝒪_{X, x}` is an associated prime of the stalk
`F_x`. This is manifestly intrinsic; the content of the file is that on a locally Noetherian
scheme it is the affine-local notion, and the consequences of that.

The third part states the **dévissage** of a coherent sheaf on a Noetherian scheme: a finite
filtration whose graded pieces are pushforwards of non-zero ideal sheaves on integral closed
subschemes. It is `sorry` by design; see the implementation note below.

## Main statements

- `AlgebraicGeometry.instIsLocallyNoetherianPullback` and its symmetric variant: `X ×ₛ T` is
  locally noetherian as soon as `T` is locally noetherian and `X ⟶ S` is locally of finite type.
- `AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint`: the associated points of a sheaf of
  modules, and `AlgebraicGeometry.Scheme.Modules.support`, its support.
- `AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_iff_mem_associatedPrimes`: over an affine
  open with Noetherian ring of sections, associated points of a quasi-coherent sheaf are the
  associated primes of its module of sections.
- `AlgebraicGeometry.Scheme.Modules.finite_associatedPoints`: on a quasi-compact locally
  Noetherian scheme a coherent sheaf has finitely many associated points.
- `AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_of_minimal_mem_support`: the generic
  points of the irreducible components of the support are associated points.
- `AlgebraicGeometry.Scheme.Modules.isSMulRegular_iff_associatedPoints_subset_basicOpen` and
  `AlgebraicGeometry.Scheme.Modules.injective_smul_iff_associatedPoints_subset`: a section of
  `𝒪_X` is a nonzerodivisor on `F` if and only if its zero locus misses the associated points.
- `AlgebraicGeometry.Scheme.Modules.exists_devissage`: the **dévissage** of a coherent sheaf on
  a Noetherian scheme, stated in terms of
  `AlgebraicGeometry.Scheme.Modules.IsPushforwardIdealSheaf`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.exists_devissage` is `sorry` by design: this file only
*states* it, following the convention of `WeilConjectures.AlgebraicGeometry.ChowLemma`. It is
the one open obligation of the blueprint's notion (N12), listed there as `lem:deg-devissage`.

## TODO

Prove `AlgebraicGeometry.Scheme.Modules.exists_devissage`. The standard route is Noetherian
induction on the support of `F`: take `Z₁` an irreducible component of `Supp F` of maximal
dimension with its reduced structure and `F₁ ⊆ F` the subsheaf of sections supported on `Z₁`
whose restriction to `Z₁` has no embedded contribution, so that `F₁` is the pushforward of a
non-zero ideal sheaf on `Z₁`, and apply the induction hypothesis to `F / F₁`, whose support is
strictly smaller. See the section *Dévissage of coherent sheaves* of the chapter *Cohomology of
schemes* in the Stacks project, and [Hartshorne, III, §5].

Mathlib's `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` is a theorem rather than an
instance, because the morphism cannot be recovered from its source. For a pullback it can, so the
first two statements below are instances.

## Blueprint

`AlgebraicGeometry.Scheme.Modules.exists_devissage` implements `lem:deg-devissage` of the
degree-of-the-isogeny chapter.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X T S : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

instance [LocallyOfFiniteType f] [IsLocallyNoetherian T] : IsLocallyNoetherian (pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)

instance [LocallyOfFiniteType g] [IsLocallyNoetherian X] : IsLocallyNoetherian (pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g)

/-!
## Associated points of a sheaf of modules

Following [Stacks, 0546], a point `x` of `X` is associated to a sheaf of modules `F` when the
maximal ideal of `𝒪_{X, x}` is an associated prime of the stalk `F_x`.
-/

namespace Scheme.Modules

variable {X : Scheme.{u}} {U : X.Opens} (F : X.Modules)

/-- A point `x` of a scheme `X` is an *associated point* of a sheaf of modules `F` if the maximal
ideal of the local ring `𝒪_{X, x}` is an associated prime of the stalk `F_x`.

On a locally Noetherian scheme this is the affine-local notion: for a quasi-coherent `F` and an
affine open `U ∋ x` with Noetherian ring of sections, `x` is an associated point of `F` if and
only if the prime of `x` is an associated prime of the `Γ(X, U)`-module `Γ(F, U)`, see
`AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_iff_mem_associatedPrimes`. -/
def IsAssociatedPoint (F : X.Modules) (x : X) : Prop :=
  IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)

/-- The set of associated points of a sheaf of modules. -/
def associatedPoints (F : X.Modules) : Set X := {x | F.IsAssociatedPoint x}

lemma mem_associatedPoints_iff (x : X) : x ∈ F.associatedPoints ↔ F.IsAssociatedPoint x := Iff.rfl

/-- The support of a sheaf of modules: the set of points where the stalk is nonzero. -/
def support (F : X.Modules) : Set X := {x | Nontrivial (F.presheaf.stalk x)}

lemma mem_support_iff (x : X) : x ∈ F.support ↔ Nontrivial (F.presheaf.stalk x) := Iff.rfl

section Affine

variable (hU : IsAffineOpen U) [F.IsQuasicoherent]

/-- **Associated points are affine-local.** For a quasi-coherent sheaf on a scheme and an affine
open `U` with Noetherian ring of sections, a point of `U` is an associated point of `F` exactly
when the corresponding prime of `Γ(X, U)` is an associated prime of `Γ(F, U)`. -/
theorem isAssociatedPoint_iff_mem_associatedPrimes [IsNoetherianRing Γ(X, U)] (x : U) :
    F.IsAssociatedPoint x.1 ↔
      (hU.primeIdealOf x).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  have hlm := isLocalizedModule_germₗ F hU x
  have key :=
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      (M := Γ(F, U)) (hU.primeIdealOf x).asIdeal.primeCompl (X.presheaf.stalk x.1) (germₗ F x)
  rw [show F.IsAssociatedPoint x.1 ↔
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) ∈
      associatedPrimes (X.presheaf.stalk x.1) (F.presheaf.stalk x.1) from Iff.rfl, ← key]
  rw [Set.mem_preimage,
    show (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)).comap
      (algebraMap Γ(X, U) (X.presheaf.stalk x.1)) = (hU.primeIdealOf x).asIdeal from
      IsLocalization.AtPrime.under_maximalIdeal _ _]

/-- The support of a quasi-coherent sheaf meets an affine open in the support of its module of
sections. -/
theorem mem_support_iff_mem_module_support (x : U) :
    x.1 ∈ F.support ↔ hU.primeIdealOf x ∈ Module.support Γ(X, U) Γ(F, U) := by
  have hlm := isLocalizedModule_germₗ F hU x
  rw [mem_support_iff, Module.mem_support_iff]
  exact ((IsLocalizedModule.iso (hU.primeIdealOf x).asIdeal.primeCompl
    (germₗ F x)).toEquiv.nontrivial_congr).symm

include hU in
/-- **A coherent sheaf on a Noetherian affine open has finitely many associated points there.**

Coherence enters through the hypothesis `Module.Finite Γ(X, U) Γ(F, U)`: that a sheaf of finite
type has finitely generated sections over an affine open is not yet available, so it is taken as
a hypothesis here. -/
theorem finite_associatedPoints_inter [IsNoetherianRing Γ(X, U)]
    [Module.Finite Γ(X, U) Γ(F, U)] : (F.associatedPoints ∩ (U : Set X)).Finite := by
  have hsub : (fun x : U ↦ (hU.primeIdealOf x).asIdeal) '' {x : U | F.IsAssociatedPoint x.1} ⊆
      associatedPrimes Γ(X, U) Γ(F, U) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (isAssociatedPoint_iff_mem_associatedPrimes F hU x).mp hx
  have hfin : {x : U | F.IsAssociatedPoint x.1}.Finite :=
    Set.Finite.of_finite_image ((associatedPrimes.finite _ _).subset hsub)
      (hU.primeIdealOf_injective.injOn)
  refine (hfin.image Subtype.val).subset ?_
  rintro x ⟨hx, hxU⟩
  exact ⟨⟨x, hxU⟩, hx, rfl⟩

include hU in
/-- **Generic points of the irreducible components of the support are associated points.** If
`x` lies in the support of `F` and every point of the support specializing to `x` is `x` itself
— that is, `x` is the generic point of an irreducible component of the support — then `x` is an
associated point of `F`. -/
theorem isAssociatedPoint_of_minimal_mem_support [IsNoetherianRing Γ(X, U)]
    [Module.Finite Γ(X, U) Γ(F, U)] (x : U) (hx : x.1 ∈ F.support)
    (hmin : ∀ y : X, y ∈ F.support → y ⤳ x.1 → y = x.1) : F.IsAssociatedPoint x.1 := by
  rw [isAssociatedPoint_iff_mem_associatedPrimes F hU]
  refine Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    Γ(X, U) Γ(F, U) ⟨⟨inferInstance, ?_⟩, ?_⟩
  · exact Module.mem_support_iff_of_finite.mp
      ((mem_support_iff_mem_module_support F hU x).mp hx)
  · rintro q ⟨hq, hqle⟩ hq'
    have hqs : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)) ∈ Module.support Γ(X, U) Γ(F, U) :=
      Module.mem_support_iff_of_finite.mpr hqle
    have hmem : hU.fromSpec ⟨q, hq⟩ ∈ U := by
      have hr : hU.fromSpec ⟨q, hq⟩ ∈ Set.range hU.fromSpec.base := Set.mem_range_self _
      rwa [hU.range_fromSpec] at hr
    have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
    have hpio : hU.primeIdealOf ⟨hU.fromSpec ⟨q, hq⟩, hmem⟩ = ⟨q, hq⟩ :=
      hinj (hU.fromSpec_primeIdealOf ⟨_, hmem⟩)
    have hy : hU.fromSpec ⟨q, hq⟩ ∈ F.support :=
      (mem_support_iff_mem_module_support F hU ⟨_, hmem⟩).mpr (by rw [hpio]; exact hqs)
    have hspec : hU.fromSpec ⟨q, hq⟩ ⤳ x.1 := by
      have h1 : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)) ⤳ hU.primeIdealOf x :=
        (PrimeSpectrum.le_iff_specializes _ _).mp
          ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hq')
      have h2 := h1.map hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf] at h2
    have heq := hmin _ hy hspec
    have : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)) = hU.primeIdealOf x := by
      rw [← hpio]
      congr 1
      exact Subtype.ext heq
    exact le_of_eq congr(($this).asIdeal).symm

include hU in
/-- **A global section of `𝒪_X` acts injectively on the sections of a quasi-coherent sheaf over
a Noetherian affine open exactly when its zero locus avoids the associated points.**

This is the case `L = 𝒪_X` of the general statement: for an invertible sheaf `L` and a section
`s : Γ(X, L)`, multiplication by `s` is an injection `F ⟶ F ⊗ L` if and only if the vanishing
locus of `s` contains no associated point of `F`. Once invertible sheaves are available, the
general form follows from this one by trivialising `L` on the affine opens of a cover. -/
theorem isSMulRegular_iff_associatedPoints_subset_basicOpen [IsNoetherianRing Γ(X, U)]
    (g : Γ(X, U)) :
    IsSMulRegular Γ(F, U) g ↔ F.associatedPoints ∩ (U : Set X) ⊆ X.basicOpen g := by
  have hreg : IsSMulRegular Γ(F, U) g ↔ ∀ m : Γ(F, U), g • m = 0 → m = 0 := by
    refine ⟨fun h m hm ↦ h (by simpa using hm), fun h a b hab ↦ ?_⟩
    have hab' : g • a = g • b := hab
    have hs : g • (a - b) = 0 := by rw [smul_sub, hab', sub_self]
    simpa [sub_eq_zero] using h _ hs
  have hzd : (¬ IsSMulRegular Γ(F, U) g) ↔
      ∃ p ∈ associatedPrimes Γ(X, U) Γ(F, U), g ∈ p := by
    rw [hreg]
    rw [show (∃ p ∈ associatedPrimes Γ(X, U) Γ(F, U), g ∈ p) ↔
      g ∈ ⋃ p ∈ associatedPrimes Γ(X, U) Γ(F, U), (p : Set Γ(X, U)) from by simp,
      biUnion_associatedPrimes_eq_zero_divisors]
    push Not
    exact ⟨fun ⟨m, hm, hm0⟩ ↦ ⟨m, hm0, hm⟩, fun ⟨m, hm0, hm⟩ ↦ ⟨m, hm, hm0⟩⟩
  rw [← not_iff_not, hzd]
  constructor
  · rintro ⟨p, hp, hgp⟩ hsub
    have hprime : p.IsPrime := hp.1
    have hmem : hU.fromSpec ⟨p, hprime⟩ ∈ U := by
      have hr : hU.fromSpec ⟨p, hprime⟩ ∈ Set.range hU.fromSpec.base := Set.mem_range_self _
      rwa [hU.range_fromSpec] at hr
    have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
    have hpio : hU.primeIdealOf ⟨hU.fromSpec ⟨p, hprime⟩, hmem⟩ = ⟨p, hprime⟩ :=
      hinj (hU.fromSpec_primeIdealOf ⟨_, hmem⟩)
    have hass : F.IsAssociatedPoint (hU.fromSpec ⟨p, hprime⟩) :=
      (isAssociatedPoint_iff_mem_associatedPrimes F hU ⟨_, hmem⟩).mpr (by rw [hpio]; exact hp)
    have hb : (⟨hU.fromSpec ⟨p, hprime⟩, hmem⟩ : U).1 ∈ X.basicOpen g := hsub ⟨hass, hmem⟩
    rw [← mem_primeCompl_iff_mem_basicOpen hU ⟨_, hmem⟩ g, hpio] at hb
    exact hb hgp
  · intro hsub
    simp only [Set.not_subset] at hsub
    obtain ⟨x, ⟨hx, hxU⟩, hxg⟩ := hsub
    refine ⟨(hU.primeIdealOf ⟨x, hxU⟩).asIdeal,
      (isAssociatedPoint_iff_mem_associatedPrimes F hU ⟨x, hxU⟩).mp hx, ?_⟩
    by_contra hg
    exact hxg ((mem_primeCompl_iff_mem_basicOpen hU ⟨x, hxU⟩ g).mp hg)

end Affine

/-- **A coherent sheaf on a quasi-compact locally Noetherian scheme has finitely many
associated points.**

As in `AlgebraicGeometry.Scheme.Modules.finite_associatedPoints_inter`, coherence enters through
the hypothesis that the sections over each affine open form a finite module; that this follows
from `SheafOfModules.IsFiniteType` is not yet available. -/
theorem finite_associatedPoints [CompactSpace X] [IsLocallyNoetherian X] [F.IsQuasicoherent]
    (hfin : ∀ V : X.affineOpens, Module.Finite Γ(X, V.1) Γ(F, V.1)) :
    F.associatedPoints.Finite := by
  have hcov : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, (V.1 : Set X) := by
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V.1 : Set X))
    (fun V ↦ V.1.2) hcov
  have hfinite : ∀ V ∈ s, (F.associatedPoints ∩ (V.1 : Set X)).Finite := by
    intro V _
    have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
    have : Module.Finite Γ(X, V.1) Γ(F, V.1) := hfin V
    exact finite_associatedPoints_inter F V.2
  refine (s.finite_toSet.biUnion hfinite).subset fun x hx ↦ ?_
  obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Set.mem_biUnion (by simpa using hV) ⟨hx, hxV⟩

/-- **A global section of `𝒪_X` acts injectively on the sections of a quasi-coherent sheaf over
every open exactly when its zero locus avoids the associated points.**

See `AlgebraicGeometry.Scheme.Modules.isSMulRegular_iff_associatedPoints_subset_basicOpen` for
the affine-local form and for what the statement for a general invertible sheaf will look
like. -/
theorem injective_smul_iff_associatedPoints_subset [IsLocallyNoetherian X] [F.IsQuasicoherent]
    (g : Γ(X, ⊤)) :
    (∀ V : X.Opens, Function.Injective fun s : Γ(F, V) ↦ X.presheaf.map V.leTop.op g • s) ↔
      F.associatedPoints ⊆ X.basicOpen g := by
  constructor
  · intro hinj x hx
    obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact ⟨U, hU, hxU⟩
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hsub := (isSMulRegular_iff_associatedPoints_subset_basicOpen F hU
      (X.presheaf.map U.leTop.op g)).mp (hinj U)
    have := hsub ⟨hx, hxU⟩
    rw [Scheme.basicOpen_res] at this
    exact this.2
  · intro hsub V
    have hzero : ∀ s : Γ(F, V), X.presheaf.map V.leTop.op g • s = 0 → s = 0 := by
      intro s hs
      refine TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ V s 0 fun x hxV ↦ ?_
      obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
        obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact ⟨U, hU, hxU⟩
      obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le (V := V ⊓ U) ⟨x, ⟨hxV, hxU⟩⟩ hxU
      have hW : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
      have : IsNoetherianRing Γ(X, X.basicOpen f) :=
        IsLocallyNoetherian.component_noetherian ⟨_, hW⟩
      have hWV : X.basicOpen f ≤ V := hfV.trans inf_le_left
      have hreg : IsSMulRegular Γ(F, X.basicOpen f)
          (X.presheaf.map (X.basicOpen f).leTop.op g) := by
        rw [isSMulRegular_iff_associatedPoints_subset_basicOpen F hW]
        rintro y ⟨hy, hyW⟩
        rw [Scheme.basicOpen_res]
        exact ⟨hyW, hsub hy⟩
      have hres : F.presheaf.map (homOfLE hWV).op s = 0 := by
        have h1 := congr(F.presheaf.map (homOfLE hWV).op $hs)
        rw [map_zero, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp, ← op_comp] at h1
        rw [show (homOfLE hWV ≫ TopologicalSpace.Opens.leTop V :
          X.basicOpen f ⟶ (⊤ : X.Opens)) = (X.basicOpen f).leTop from
          Subsingleton.elim _ _] at h1
        exact hreg (by simpa using h1)
      rw [map_zero, ← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWV) x hxf s, hres,
        map_zero]
    intro a b hab
    have hab' : X.presheaf.map V.leTop.op g • a = X.presheaf.map V.leTop.op g • b := hab
    have : X.presheaf.map V.leTop.op g • (a - b) = 0 := by rw [smul_sub, hab', sub_self]
    simpa [sub_eq_zero] using hzero _ this

/-!
## Dévissage of a coherent sheaf

Every coherent sheaf on a Noetherian scheme admits a finite filtration whose graded pieces are
pushforwards of non-zero ideal sheaves on integral closed subschemes. This is the engine of the
finiteness theorem for coherent cohomology, and of the computation of a top intersection number
in terms of the generic rank.
-/

/-- A sheaf of modules on `X` is the **pushforward of a non-zero ideal sheaf on an integral
closed subscheme** if it is isomorphic to `ι_* 𝓘` for a closed immersion `ι : Z ⟶ X` with `Z`
integral and a non-zero ideal sheaf `𝓘 ⊆ 𝒪_Z`.

These are the graded pieces of the dévissage of a coherent sheaf,
`AlgebraicGeometry.Scheme.Modules.exists_devissage`. -/
def IsPushforwardIdealSheaf (G : X.Modules) : Prop :=
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι) (_ : IsIntegral Z)
    (I : Z.IdealSheafData), I ≠ ⊥ ∧ Nonempty (G ≅ (Modules.pushforward ι).obj I.toModules)

/-- **Dévissage of a coherent sheaf.** A coherent sheaf `F` on a Noetherian scheme `X` has a
finite filtration by coherent subsheaves

`0 = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_t = F`

whose graded pieces `F_j / F_{j-1}` are pushforwards `(ι_j)_* 𝓘_j` of non-zero ideal sheaves
`𝓘_j ⊆ 𝒪_{Z_j}` along closed immersions `ι_j : Z_j ⟶ X` of integral schemes.

The filtration is presented as a chain of monomorphisms `F₀ ⟶ F₁ ⟶ ⋯ ⟶ F_t` with `F₀` zero and
`F_t ≅ F`, the graded pieces being the cokernels of the successive monomorphisms.

This statement is `sorry` by design; see the implementation notes of this file.
(blueprint: `lem:deg-devissage`) -/
theorem exists_devissage [IsNoetherian X] (F : X.Modules) [F.IsCoherent] :
    ∃ (t : ℕ) (G : Fin (t + 1) → X.Modules) (φ : ∀ j : Fin t, G j.castSucc ⟶ G j.succ),
      IsZero (G 0) ∧ Nonempty (G (Fin.last t) ≅ F) ∧
        ∀ j : Fin t, (G j.succ).IsCoherent ∧ Mono (φ j) ∧
          IsPushforwardIdealSheaf (cokernel (φ j)) :=
  sorry

end Scheme.Modules

end AlgebraicGeometry
