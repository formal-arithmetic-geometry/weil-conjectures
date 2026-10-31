/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.TraceFormula.SchemeRelativeAmpleAffineCover

/-!
# Relative ampleness for schemes under arbitrary base change

Source: Stacks Project, Morphisms, Tag 0893 (lemma-ample-base-change), with relative
ampleness as in Tag 01VH (definition-relatively-ample)
(blueprint: lem-trf-scheme-relative-ample-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

-- The local square is the base change of a map between affine opens.
private theorem isAmple_restricted_baseChange
    {X T T' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T)
    (L : X.Modules) [L.IsInvertible]
    (W : T.Opens) (V : T'.Opens) (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hVW : V ≤ g ⁻¹ᵁ W)
    (hL : ∃ h : ((tensorPullback (f ⁻¹ᵁ W).ι).obj L).IsInvertible,
      @IsAmple (f ⁻¹ᵁ W).toScheme ((tensorPullback (f ⁻¹ᵁ W).ι).obj L) h) :
    ∃ h : ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ V).ι).obj
        ((tensorPullback (pullback.fst f g)).obj L)).IsInvertible,
      @IsAmple ((pullback.snd f g) ⁻¹ᵁ V).toScheme
        ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ V).ι).obj
          ((tensorPullback (pullback.fst f g)).obj L)) h := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  have hle : q ⁻¹ᵁ V ≤ p ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hVW
  let a := p.resLE (f ⁻¹ᵁ W) (q ⁻¹ᵁ V) hle
  have hsquare := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    hVW le_rfl (inf_eq_right.mpr hle).symm
  have : IsAffine W.toScheme := hW
  have : IsAffine V.toScheme := hV
  have : IsAffineHom (g.resLE W V hVW) := inferInstance
  have : IsAffineHom a := MorphismProperty.of_isPullback hsquare.flip inferInstance
  obtain ⟨hLW, hLamp⟩ := hL
  have := hLW
  have : ((tensorPullback a).obj ((tensorPullback (f ⁻¹ᵁ W).ι).obj L)).IsInvertible :=
    ((invertible_pullback_tensor a).1 _).2
  have ha := isAmple_tensorPullback_of_isAffineHom a _ hLamp
  have heq : a ≫ (f ⁻¹ᵁ W).ι = (q ⁻¹ᵁ V).ι ≫ p := by
    exact p.resLE_comp_ι hle
  obtain ⟨c⟩ := nonempty_tensorPullbackComp a (f ⁻¹ᵁ W).ι
  obtain ⟨d⟩ := nonempty_tensorPullbackComp (q ⁻¹ᵁ V).ι p
  let e := (c.app L).symm ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj L) heq) ≪≫ d.app L
  change (tensorPullback a).obj ((tensorPullback (f ⁻¹ᵁ W).ι).obj L) ≅
    (tensorPullback (q ⁻¹ᵁ V).ι).obj ((tensorPullback p).obj L) at e
  have : ((tensorPullback p).obj L).IsInvertible :=
    ((invertible_pullback_tensor p).1 L).2
  have : ((tensorPullback (q ⁻¹ᵁ V).ι).obj
      ((tensorPullback p).obj L)).IsInvertible :=
    ((invertible_pullback_tensor (q ⁻¹ᵁ V).ι).1 _).2
  exact ⟨_, (isAmple_iff_of_iso e).mp ha⟩

/-- Relative ampleness of an invertible module survives arbitrary base change.
Restrictions are tensor pullbacks along the indicated open immersions. The existential
invertibility proofs supply the proof argument of absolute `IsAmple`; they introduce no
extra geometric assumption.

Source: Stacks Project, Morphisms, Tag 0893, using Tags 01VH and 01VJ
(blueprint: lem-trf-scheme-relative-ample-base-change).

Proof, following the node's five steps:
1. Absolute ampleness over every affine open implies quasi-compactness of each inverse
image (def-weil-pbc-ample-invertible-module), hence of f
(def-weil-finite-type-morphism).
2. Pullback preserves invertibility (lem-weil-pbc-invertible-pullback-tensor), and base
change preserves quasi-compactness (lem-pc-quasi-compact-base-change).
3. Choose affine neighbourhoods U'_i covering T', each mapping into an affine open U_i
of T (lem-weil-pbc-affine-opens-basis). The fibre-product universal property
(def-pc-fibre-product) identifies the inverse image of U'_i with the base change of
f inverse-image U_i along U'_i to U_i.
4. The latter base map is affine (lem-weil-pbc-morphism-affine-schemes-affine), so its
base change is affine (lem-weil-pbc-affine-morphism-permanence). Affine pullback preserves
ampleness (lem-weil-pbc-pullback-ample-invertible). Functoriality of tensor pullback
(def-pc-module-pullback) identifies this module with the restriction of the pullback L.
5. Apply lem-trf-scheme-relative-ample-affine-cover to f', its pulled-back invertible
module, and this affine cover of T'. Quasi-compactness from step 2 and ampleness from
step 4 give ampleness over every affine open V' of T'. -/
theorem isAmple_on_affineOpens_tensorPullback_baseChange
    {X T T' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T)
    (L : X.Modules) [L.IsInvertible]
    (hL : ∀ V : T.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h) :
    ∀ V' : T'.Opens, IsAffineOpen V' →
      ∃ h : ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ V').ι).obj
          ((tensorPullback (pullback.fst f g)).obj L)).IsInvertible,
        @IsAmple ((pullback.snd f g) ⁻¹ᵁ V').toScheme
          ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ V').ι).obj
            ((tensorPullback (pullback.fst f g)).obj L)) h := by
  have hqc : QuasiCompact f := by
    apply quasiCompact_iff_forall_isAffineOpen.mpr
    intro W hW
    obtain ⟨hLW, hLamp⟩ := hL W hW
    exact isCompact_iff_compactSpace.mpr hLamp.1
  have : ((tensorPullback (pullback.fst f g)).obj L).IsInvertible :=
    ((invertible_pullback_tensor (pullback.fst f g)).1 L).2
  let I := {WV : T.Opens × T'.Opens //
    IsAffineOpen WV.1 ∧ IsAffineOpen WV.2 ∧ WV.2 ≤ g ⁻¹ᵁ WV.1}
  let U : I → T'.Opens := fun i ↦ i.1.2
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦ i.2.2.1
  have hcover : iSup U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := T) (x := g x) (U := ⊤) trivial
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset
      (X := T') (x := x) (U := g ⁻¹ᵁ W) hxW
    exact (le_iSup U ⟨(W, V), hW, hV, hVW⟩) hxV
  have hamp : ∀ i : I,
      @IsAmple ((pullback.snd f g) ⁻¹ᵁ U i).toScheme
        ((tensorPullback ((pullback.snd f g) ⁻¹ᵁ U i).ι).obj
          ((tensorPullback (pullback.fst f g)).obj L))
        ((invertible_pullback_tensor ((pullback.snd f g) ⁻¹ᵁ U i).ι).1
          ((tensorPullback (pullback.fst f g)).obj L)).2 := by
    intro i
    obtain ⟨_, ha⟩ := isAmple_restricted_baseChange f g L
      i.1.1 i.1.2 i.2.1 i.2.2.1 i.2.2.2 (hL i.1.1 i.2.1)
    exact ha
  intro V hV
  exact ⟨_, scheme_relative_ample_affine_cover (pullback.snd f g)
    ((tensorPullback (pullback.fst f g)).obj L) U hU hcover hamp V hV⟩

end AlgebraicGeometry.Scheme.Modules
