module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Simultaneous spreading of closed-subscheme germs

Source: Stacks Project, Tag 01Y3 (neighbourhood principle), Tags 01IN, 01HV,
01I3 and 01HO (affine ideals), and Tag 0C4H (scheme-theoretic intersections).
(blueprint: lem-trf-closed-subscheme-germ-family-spreading).

An intersection is the closed subscheme of the supremum (sum) of the defining
ideal sheaves, using Mathlib's existing `IdealSheafData.subscheme`. Equality of
embedded subschemes is an isomorphism commuting with their maps to the ambient
scheme. The stalk hypothesis compares ranges of the ideal inclusions in the same
stalk of the structure module, so it retains the embeddings.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite family of equal embedded ideal germs agrees on one affine neighbourhood,
including all scheme-theoretic intersections and their affine sum ideals.
Source: Stacks Tags 01Y3, 01IN, 01HV, 01I3, 01HO, 01I1 and 0C4H.
(blueprint: lem-trf-closed-subscheme-germ-family-spreading).

Proof:
1. Choose a Noetherian affine chart through y (pqf-def-locnoeth). Each defining
   ideal has a finite generating list (def-weil-pbc-noetherian-ring), with empty
   lists allowed; its associated ideal sheaf is the one of the closed immersion
   (def-sbc-closed-immersion-ideal-sheaf).
2. The affine stalk-localization and tilde-stalk-localization nodes identify the
   embedded stalk images with the localized ideals. For each generator use
   lem-exc-localization-ideal-membership-clearing to find a denominator outside
   the prime making it belong to the other ideal, in both directions.
3. Multiply all denominators, with empty product 1. Primality keeps this product
   outside the prime. The affine-open-section-vanishing-prime node supplies the
   affine basic neighbourhood D(f); every denominator is a unit in its section
   ring (def-weil-ring-localization-away), so both ideal inclusions hold there.
4. The tilde-sections node identifies these section ideals with the restrictions
   of the original ideal sheaves. The equal-ideal-closed-immersions node gives
   the unique isomorphisms over this common neighbourhood.
5. The fibre-product universal property shows that base change commutes with
   the finite intersection, including the empty family. Compose the factor
   isomorphisms to identify it with the intersection of the H factors.
6. By lem-weil-pbc-morphism-into-affine-scheme, maps to Spec(B / sum J_a) over
   Spec B correspond to ring maps annihilating every J_a. Thus this quotient
   realizes the intersection, whose ideal is the sum. An empty sum is zero and
   its subscheme is U. An empty factor has unit ideal, so the sum is the unit
   ideal and its subscheme is empty. -/
theorem closedSubscheme_germ_family_spreading
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (y : Y)
    {F : Type v} [Finite F] (Z H : F → Scheme.{u})
    (i : ∀ a : F, Z a ⟶ Y) (j : ∀ a : F, H a ⟶ Y)
    [∀ a : F, IsClosedImmersion (i a)] [∀ a : F, IsClosedImmersion (j a)]
    (hgerm : ∀ a : F,
      LinearMap.range ((PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj y).map
        (i a).ker.toModulesι.val).hom =
      LinearMap.range ((PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj y).map
        (j a).ker.toModulesι.val).hom) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      (∀ a : F, ∃ e : pullback (i a) U.1.ι ≅ pullback (j a) U.1.ι,
        e.hom ≫ pullback.snd (j a) U.1.ι = pullback.snd (i a) U.1.ι) ∧
      ∀ S : Finset F,
        (∃ e : pullback (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι ≅
            (⨆ a ∈ S, (pullback.snd (j a) U.1.ι).ker).subscheme,
          e.hom ≫ (⨆ a ∈ S, (pullback.snd (j a) U.1.ι).ker).subschemeι =
            pullback.snd (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι) ∧
        (pullback.snd (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι).ker.ideal
            ⟨⊤, @isAffineOpen_top U.1.toScheme U.2⟩ =
          ⨆ a ∈ S, (pullback.snd (j a) U.1.ι).ker.ideal ⟨⊤, @isAffineOpen_top U.1.toScheme U.2⟩ ∧
        (S = ∅ →
          IsIso (pullback.snd (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι) ∧
          (pullback.snd (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι).ker.ideal
            ⟨⊤, @isAffineOpen_top U.1.toScheme U.2⟩ = ⊥) ∧
        ((∃ a ∈ S, IsEmpty (pullback (C := Scheme.{u}) (j a) U.1.ι)) →
          IsEmpty (pullback (C := Scheme.{u}) (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι) ∧
          (pullback.snd (⨆ a ∈ S, (i a).ker).subschemeι U.1.ι).ker.ideal
            ⟨⊤, @isAffineOpen_top U.1.toScheme U.2⟩ = ⊤) := by
  sorry

end AlgebraicGeometry
