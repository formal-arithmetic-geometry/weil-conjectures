/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.RingTheory.FiniteRingMapQuasiFinite
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.TraceFormula.StrictHenselizationQuasiFiniteRing
import Sheaf.TraceFormula.StrictHenselizationTensorFinite

/-!
# Finite base change of strict localizations

Source: Stacks Project, Algebra, Tags 05WR and 0GIP; Étale Cohomology, Tag 03QP,
using Algebra, Tag 04GH (blueprint: lem-trf-finite-base-strict-localization).

The geometric lifts of `s` are canonically in bijection with the connected components
of the finite geometric fibre. Indexing by these lifts avoids choosing a point in a
component. The coproduct is allowed to be empty. The second statement uses the universal
property of the canonical square to state the isomorphism and its projection compatibilities.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite geometric fibre indexes the canonical strict-local decomposition.
The displayed bijection identifies a lift `t` with the component of its fibre point.
The two coproduct projection equations specify the actual canonical map over `T` and
`S_(s)`. Each factor is finite and strictly henselian, and its local ring map induces
a finite purely inseparable residue-field extension.

Source: Stacks Project, Tags 03QP, 04GH and 05WR
(blueprint: lem-trf-finite-base-strict-localization).

Proof:
1. By strict-henselization functoriality, `S_(s)` is the spectrum of a strictly henselian
local ring `R`; its residue field is the separable algebraic closure of the residue
field of the image of `s` inside Ω, rather than necessarily Ω itself.
2. Choose an affine neighbourhood `Spec A` of that image. Finiteness gives an affine
inverse image `Spec B`, and the base change has ring `B ⊗[A] R`. It is finite over `R`
by finite-morphism permanence and the affine fibre-product formula. The finite-over-
henselian product theorem (Tag 04GH) decomposes it into finitely many henselian local
factors. The finite-ring-map quasi-finite lemma and Tag 05WR identify each factor
with the strict henselization at the corresponding geometric lift, through the
canonical structural and functorial maps; these maps are finite and local.
3. A finite scheme over Ω has one Ω-point in each connected component, including for
nonreduced fibres. A finite extension of the separably closed residue field of `R`
has exactly one compatible embedding in Ω (the finite-extension unique-embedding
lemma). Thus the local factors are indexed bijectively by the geometric lifts and
by the components of the geometric fibre. Tag 05WR gives the finite purely
inseparable residue extension. Functoriality gives strict henselianity of the factors.
If the fibre is empty, the finite `R`-module `B ⊗[A] R` vanishes by Nakayama, so the
coproduct and base change are both empty. The factor identifications have the stated
projection equations because the ring identifications use the canonical structure maps.
-/
theorem finite_strictLocalization_decomposition
    {T S : Scheme.{u}} (h : T ⟶ S) [IsFinite h]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Finite (ConnectedComponents (pullback h s : Scheme.{u})) ∧
    Function.Bijective
      (fun t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s} ↦
        ConnectedComponents.mk
          ((pullback.lift t.val (𝟙 _) (t.property.trans (Category.id_comp s).symm))
            (IsLocalRing.closedPoint Ω))) ∧
    ∃ (_ : IsLocalRing (strictHenselizationRing s)),
      ∃ e : (∐ fun t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s} ↦
          strictHenselizationScheme t.val) ≅
          pullback h (strictHenselizationStructuralMap s),
        (∀ t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s},
          Sigma.ι (fun t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s} ↦
            strictHenselizationScheme t.val) t ≫ e.hom ≫
              pullback.fst h (strictHenselizationStructuralMap s) =
            strictHenselizationStructuralMap t.val) ∧
        (∀ t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s},
          Sigma.ι (fun t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s} ↦
            strictHenselizationScheme t.val) t ≫ e.hom ≫
              pullback.snd h (strictHenselizationStructuralMap s) =
            strictHenselizationMap h t.val ≫
              eqToHom (congrArg strictHenselizationScheme t.property)) ∧
        ∀ t : {t : Spec (.of Ω) ⟶ T // t ≫ h = s},
          ∃ (_ : IsLocalRing (strictHenselizationRing t.val)),
            IsStrictlyHenselianLocalRing (strictHenselizationRing t.val) ∧
            IsFinite (strictHenselizationMap h t.val ≫
              eqToHom (congrArg strictHenselizationScheme t.property)) ∧
            ∃ φ : strictHenselizationRing s →+* strictHenselizationRing t.val,
              Spec.map (CommRingCat.ofHom φ) = strictHenselizationMap h t.val ≫
                eqToHom (congrArg strictHenselizationScheme t.property) ∧
              ∃ (_ : IsLocalHom φ),
                (IsLocalRing.ResidueField.map φ).Finite ∧
                @IsPurelyInseparable
                  (IsLocalRing.ResidueField (strictHenselizationRing s))
                  (IsLocalRing.ResidueField (strictHenselizationRing t.val)) _ _
                  (IsLocalRing.ResidueField.map φ).toAlgebra := by
  sorry

/-- Strict localization carries base change along a finite morphism to a pullback.
The right vertical map includes only transport along the original square's equality;
all four arrows are the canonical functorial strict-local maps. The pullback property
is precisely the canonical isomorphism with its two projection compatibilities.
The structural map to `W` is compatible as well, by functoriality and uniqueness in
the original pullback. There is no finiteness hypothesis on `g`.

Source: Stacks Project, Tag 0GIP, case (1) (also case (4))
(blueprint: lem-trf-finite-base-strict-localization).

Proof:
4. Choose affine neighbourhoods of the images of the geometric point in `S` and `Y`.
The inverse image in `T` is affine because `h` is finite; the resulting affine open
of `W` has ring `B ⊗[A] C`, with `A → B` finite and `A → C` arbitrary. The ind-étale
strict-local invariance lemma for open immersions identifies the four strict
localizations with those of these affine charts, over the original schemes and
with the canonical functorial arrows. The tensor strict-henselization lemma
(Tag 0GIP) identifies the strict henselization of `B ⊗[A] C` with the tensor product
of the other strict henselizations over that of `A`. The affine fibre-product
formula turns this into the asserted pullback of schemes.
5. The tensor isomorphism is induced by the four structure maps. Consequently its
composites with both projections are the original functorial maps; their composites
with the structural maps recover those from `W_(w)` to `Y` and `T`. Uniqueness in
the original fibre product makes the resulting map to `W` its structural map.
-/
theorem finite_strictLocalization_isPullback
    {W Y T S : Scheme.{u}} (p : W ⟶ Y) (q : W ⟶ T)
    (g : Y ⟶ S) (h : T ⟶ S) [IsFinite h] (H : IsPullback p q g h)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (w : Spec (.of Ξ) ⟶ W) :
    IsPullback (strictHenselizationMap p w) (strictHenselizationMap q w)
      (strictHenselizationMap g (w ≫ p))
      (strictHenselizationMap h (w ≫ q) ≫
        eqToHom (congrArg strictHenselizationScheme
          ((Category.assoc w q h).trans
            ((congrArg (fun a : W ⟶ S ↦ w ≫ a) H.w.symm).trans
              (Category.assoc w p g).symm)))) := by
  sorry

end AlgebraicGeometry.Scheme
