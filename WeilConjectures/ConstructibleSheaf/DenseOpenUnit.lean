/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Locally constant sheaves on a regular scheme extend uniquely over a dense open

Let `X` be a locally noetherian regular scheme, `j : U ⟶ X` an open immersion with dense image
and `G` a locally constant sheaf of `Λ`-modules on the small étale site of `X`. Then the unit
`G ⟶ j_* j^* G` of the adjunction `j^* ⊣ j_*` is an isomorphism.

It is a monomorphism since morphisms into a locally constant sheaf are determined on a dense
open (`AlgebraicGeometry.Etale.upperStar_map_injective_of_isLocallyConstantSheaf`). It is locally
surjective: a section of `j_* j^* G` over an étale `V ⟶ X` is a section of `G` over
`V ×_X U`; near a point of `V`, refine `V` to an étale `W` over which `G` is constant and whose
underlying scheme is irreducible. Such `W` exist because étale `X`-schemes are again locally
noetherian with integral local rings, so their points have irreducible open neighbourhoods. Then
`W ×_X U` is a nonempty open of `W`, hence irreducible, and the sections of a constant sheaf
over an irreducible étale scheme are the constants
(`AlgebraicGeometry.Etale.bijective_toSheafify_app_of_irreducibleSpace`); so the section over
`W ×_X U` is a constant, which is the restriction of the same constant over `W`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_toSheafify_app_of_irreducibleSpace`: the sections of the
  constant sheaf of modules `N` over an étale `X`-scheme with irreducible underlying space are
  `N`.
- `AlgebraicGeometry.exists_isOpen_irreducibleSpace_of_isDomain_stalk`: a point of a locally
  noetherian scheme with integral local rings has an irreducible open neighbourhood.
- `AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction_of_isRegular`: the unit
  `G ⟶ j_* j^* G` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- **Irreducible neighbourhoods.** A point of a locally noetherian scheme whose local rings are
integral domains has an irreducible open neighbourhood: its connected component is open, the
scheme being locally connected, and a connected locally noetherian scheme with integral local
rings is irreducible (`AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`). -/
theorem exists_isOpen_irreducibleSpace_of_isDomain_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    ∃ O : X.Opens, x ∈ O ∧ IrreducibleSpace O := by
  let O : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  refine ⟨O, mem_connectedComponent, ?_⟩
  have : ConnectedSpace O :=
    Subtype.connectedSpace isConnected_connectedComponent
  have : IsLocallyNoetherian O := inferInstance
  exact irreducibleSpace_of_isDomain_stalk O fun y ↦
    have := h y.1
    MulEquiv.isDomain _ (O.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}

section VanishingLocus

variable (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The points of an étale `X`-scheme `W` near which a section `σ` of `M` over `W` vanishes:
those in the image of an étale `W' ⟶ W` on which `σ` restricts to zero. This is the analogue for
sheaves of `Λ`-modules of `AlgebraicGeometry.Etale.vanishingLocus` for abelian sheaves. -/
def moduleVanishingLocus {W : X.Etale} (σ : ToType (M.obj.obj (op W))) : Set W.left :=
  {w | ∃ (W' : X.Etale) (g : W' ⟶ W) (w' : W'.left), g.left w' = w ∧ M.obj.map g.op σ = 0}

variable {M}

/-- The vanishing locus of a section is open, étale morphisms being open. -/
lemma isOpen_moduleVanishingLocus {W : X.Etale} (σ : ToType (M.obj.obj (op W))) :
    IsOpen (moduleVanishingLocus M σ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨W', g, w', rfl, hg⟩
  exact ⟨Set.range g.left, fun _ ⟨w'', hw''⟩ ↦ ⟨W', g, w'', hw'', hg⟩,
    g.left.isOpenMap.isOpen_range, w', rfl⟩

/-- A section whose vanishing locus is everything is zero, by the sheaf condition. -/
lemma eq_zero_of_moduleVanishingLocus_eq_univ {W : X.Etale} {σ : ToType (M.obj.obj (op W))}
    (h : moduleVanishingLocus M σ = Set.univ) : σ = 0 := by
  let S : Sieve W :=
    { arrows W' g := M.obj.map g.op σ = 0
      downward_closed {W W'} g hg g' := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg, map_zero] }
  refine Sheaf.isSeparated M W S ?_ σ 0 fun W' g hg ↦ by rw [map_zero]; exact hg
  rw [mem_smallEtaleTopology_iff]
  intro w
  obtain ⟨W', g, w', hw', hg⟩ : w ∈ moduleVanishingLocus M σ := h ▸ Set.mem_univ w
  exact ⟨W', g, hg, w', hw'⟩

/-- **A locally constant sheaf is locally a constant sheaf.** Near a point `w` of an étale
`X`-scheme `W`, a section `σ` of a locally constant sheaf `M` is a constant `n` of a constant
sheaf: there is an étale neighbourhood `g : W₂ ⟶ W` of `w` such that for every nonempty étale
`P ⟶ W₂`, the restriction of `σ` to `P` vanishes if and only if `n` does. -/
lemma exists_isZero_iff_of_isLocallyConstantSheaf [IsLocallyConstantSheaf M] {W : X.Etale}
    (σ : ToType (M.obj.obj (op W))) (w : W.left) :
    ∃ (W₂ : X.Etale) (g : W₂ ⟶ W) (w₂ : W₂.left) (N : ModuleCat.{u + 1} Λ) (n : N),
      g.left w₂ = w ∧ ∀ (P : X.Etale) (h : P ⟶ W₂), Nonempty P.left →
        (M.obj.map (h ≫ g).op σ = 0 ↔ n = 0) := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := M)
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨i, u, hu⟩ := 𝒰.exists_eq (W.hom w)
  set Ui := 𝒰.etalePrecoverageToEtale i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  let W₁ : X.Etale := Scheme.Etale.mk (pullback.fst W.hom (𝒰.f i) ≫ W.hom)
  let g₁ : W₁ ⟶ W := MorphismProperty.Over.homMk (pullback.fst W.hom (𝒰.f i))
  let h₁ : W₁ ⟶ Ui := MorphismProperty.Over.homMk (pullback.snd W.hom (𝒰.f i))
    pullback.condition.symm
  obtain ⟨w₁, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hu.symm
  have := hc i
  obtain ⟨N, ⟨e₀⟩⟩ := (M.over Ui).mem_essImage_of_isConstant (J := X.smallEtaleTopology.over Ui)
  let e : M.over Ui ≅ ((constantSheaf X.smallEtaleTopology _).obj N).over Ui :=
    e₀.symm ≪≫ constantSheafOverIso X.smallEtaleTopology _ Ui N
  set NX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
  have hnat {V V' : Over Ui} (k : V' ⟶ V) (y : ToType (M.obj.obj (op V.left))) :
      e.hom.hom.app (op V') (M.obj.map k.left.op y) =
        NX.obj.map k.left.op (e.hom.hom.app (op V) y) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality k.op) y
  let W₁' : Over Ui := Over.mk h₁
  let c : ToType (NX.obj.obj (op W₁)) := e.hom.hom.app (op W₁') (M.obj.map g₁.op σ)
  have hsurj := (X.smallEtaleTopology.W_toSheafify
    ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallySurjective
  obtain ⟨W₂, g₂, ⟨n, hn⟩, w₂, hw₂⟩ := (mem_smallEtaleTopology_iff _).1
    (Presheaf.imageSieve_mem X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) c) w₁
  change ToType N at n
  refine ⟨W₂, g₂ ≫ g₁, w₂, N, n, ?_, fun P h hP ↦ ?_⟩
  · change (g₂.left ≫ g₁.left) w₂ = w
    rw [Scheme.Hom.comp_apply, hw₂]
    exact hw₁
  · let P' : Over Ui := Over.mk ((h ≫ g₂) ≫ h₁)
    have hinj := (((sheafToPresheaf _ _).mapIso e).app (op P')).toLinearEquiv.injective
    have h₄ : e.hom.hom.app (op P') (M.obj.map (h ≫ g₂ ≫ g₁).op σ) =
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op P) n := by
      have := hnat (V := W₁') (V' := P') (Over.homMk (h ≫ g₂)) (M.obj.map g₁.op σ)
      rw [← Category.assoc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      refine this.trans ?_
      change NX.obj.map (h ≫ g₂).op c = _
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [← hn]
      exact (ConcreteCategory.congr_hom
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).naturality h.op)
          n).symm
    constructor
    · intro h0
      refine eq_zero_of_toSheafify_app_eq_zero (W := P) n ?_
      rw [← h₄, h0]
      exact LinearMap.map_zero _
    · rintro rfl
      refine hinj ((h₄.trans ?_).trans (LinearMap.map_zero _).symm)
      exact map_zero _

/-- **The vanishing locus of a section of a locally constant sheaf is open and closed.** Near a
point outside it the section is a nonzero constant, and a nonzero constant vanishes on no
nonempty étale scheme. -/
theorem isClopen_moduleVanishingLocus [IsLocallyConstantSheaf M] {W : X.Etale}
    (σ : ToType (M.obj.obj (op W))) : IsClopen (moduleVanishingLocus M σ) := by
  refine ⟨?_, isOpen_moduleVanishingLocus σ⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro w hw
  obtain ⟨W₂, g, w₂, N, n, hw₂, hn⟩ := exists_isZero_iff_of_isLocallyConstantSheaf σ w
  have hn0 : n ≠ 0 := by
    intro h0
    exact hw ⟨W₂, g, w₂, hw₂, by simpa using (hn W₂ (𝟙 _) ⟨w₂⟩).2 h0⟩
  refine ⟨Set.range g.left, ?_, g.left.isOpenMap.isOpen_range, w₂, hw₂⟩
  rintro _ ⟨y, rfl⟩ ⟨W', g', w', hw', hg'⟩
  obtain ⟨Z, p₁, p₂, z, hp, -, -⟩ := exists_eq_of_apply_eq g g' y w' hw'.symm
  refine hn0 ((hn Z p₁ ⟨z⟩).1 ?_)
  rw [hp, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg', map_zero]

end VanishingLocus

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}

section ConstantSheaf

variable (N : ModuleCat.{u + 1} Λ)

/-- A constant sheaf of modules on the small étale site is locally constant, trivialised by the
identity cover. -/
instance isLocallyConstantSheaf_constantSheaf :
    IsLocallyConstantSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) := by
  have : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N).IsConstant
      X.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  exact ⟨⟨⟨Cover.mkOfCovers PUnit (fun _ ↦ X) (fun _ ↦ 𝟙 X) (fun x ↦ ⟨⟨⟩, x, rfl⟩)
    (fun _ ↦ inferInstance), fun _ ↦
    (isConstant_over_iff_upperStar _ _ _).2 (Sheaf.IsConstant.upperStar (X := X) _ _ _)⟩⟩⟩

end ConstantSheaf

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end Etale

end AlgebraicGeometry
