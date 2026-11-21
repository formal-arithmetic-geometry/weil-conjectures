/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersionSquare
public import WeilConjectures.WeilSheaf.BaseChangeField.Comparison
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Transport of Weil sheaves commutes with extension by zero

Let `θ : X̄ ≅ X̄'` and `θ_Y : Ȳ ≅ Ȳ'` identify the geometric fibers of `k₀`-schemes `X`, `Y` with
those of `k₀'`-schemes `X'`, `Y'`, intertwining the geometric Galois Frobenii of `X'`, `Y'` with
the `r`-th powers of those of `X`, `Y`, and let `j : X ⟶ Y`, `j' : X' ⟶ Y'` be open immersions
whose base changes commute with `θ`, `θ_Y`. Then transporting pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.transport`) commutes with extension by zero
(`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero`): on underlying sheaves, this is the
exchange isomorphism `j̄'_! θ_* ≅ θ_Y_* j̄_!` of
`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekSquareIso`.

Its compatibility with the Weil structures follows from that of the transport of pushforwards
(`AlgebraicGeometry.ProEtaleWeilSheaf.transportLowerStarIso`), since the comparisons
`j̄_! ⟶ j̄_*`, which are monomorphisms compatible with the Weil structures, intertwine the exchange
isomorphisms of extensions by zero and of pushforwards.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.transportExtensionByZeroIso`: transporting along `θ`,
  `θ_Y` commutes with extension by zero along `j`, `j'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category* C] {F : C ⥤ C}

/-- An isomorphism `e` of the underlying objects of algebras `A`, `B` with invertible structure
morphisms is compatible with the structure morphisms as soon as its composite with the underlying
monomorphism of a morphism `m : B ⟶ D` underlies a morphism `A ⟶ D`. -/
lemma map_hom_comp_str_of_hom_comp_mono {A B D : IsoAlgebra F} (e : A.carrier ≅ B.carrier)
    (m : B ⟶ D) [Mono m.hom.f] (g : A ⟶ D) (h : e.hom ≫ m.hom.f = g.hom.f) :
    F.map e.hom ≫ B.obj.str = A.obj.str ≫ e.hom := by
  rw [← cancel_mono m.hom.f, Category.assoc, ← m.hom.h, ← F.map_comp_assoc, h, g.hom.h,
    Category.assoc, h]

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] {X' Y' : Scheme.{u}}
  [X'.Over (Spec (CommRingCat.of k₀'))] [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (X' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (X' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)
  (θY : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber)
  (hθY : θY.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θY.hom)
  (j : X ⟶ Y) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (j' : X' ⟶ Y') [IsOpenImmersion j'] [j'.IsOver (Spec (CommRingCat.of k₀'))]
  (hsq : θ.hom ≫ Scheme.Hom.geometricFiberMap j' (comp_over j' _) =
    Scheme.Hom.geometricFiberMap j (comp_over j _) ≫ θY.hom)

/-- On underlying sheaves, `j_!` acts on morphisms by the extension by zero along `j̄`. -/
@[simp]
lemma extensionByZero_map_hom_f {K K' : ProEtaleWeilSheaf k₀ l X} (φ : K ⟶ K') :
    ((extensionByZero k₀ l j).map φ).hom.f =
      (Scheme.Hom.geometricFiberMap j (comp_over j _))_!ᵃ[l].map φ.hom.f :=
  rfl

include hsq in
/-- On underlying sheaves, the comparison `j_! ⟶ j_*` intertwines the exchange isomorphism
`j̄'_! θ_* ≅ θ_Y_* j̄_!` with the transport of pushforwards. -/
lemma adicOpenImmersionLowerShriekSquareIso_hom_app_comp_transport_map_hom_f
    (K : ProEtaleWeilSheaf k₀ l X) :
    (adicOpenImmersionLowerShriekSquareIso l hsq).hom.app K.carrier ≫
        ((transport θY r hθY).map ((extensionByZeroToLowerStar k₀ l j).app K)).hom.f =
      ((extensionByZeroToLowerStar k₀' l j').app ((transport θ r hθ).obj K) ≫
        (transportLowerStarIso θ r hθ θY hθY j j' hsq).hom.app K).hom.f := by
  rw [transport_map_hom_f, IsoAlgebra.comp_hom_f, transportLowerStarIso_hom_app_hom_f]
  exact (congr_app (adicOpenImmersionLowerShriekToLowerStar_squareIso l hsq) K.carrier).symm

/-- The transport of the comparison `j_! ⟶ j_*` is a monomorphism on underlying sheaves. -/
instance mono_transport_map_extensionByZeroToLowerStar_app_hom_f (K : ProEtaleWeilSheaf k₀ l X) :
    Mono ((transport θY r hθY).map ((extensionByZeroToLowerStar k₀ l j).app K)).hom.f := by
  rw [transport_map_hom_f]
  have : Mono ((extensionByZeroToLowerStar k₀ l j).app K).hom.f :=
    mono_adicOpenImmersionLowerShriekToLowerStar_app _ K.carrier
  exact (adicLowerStarEquivalence l θY).functor.map_mono _

include hsq in
/-- The component at `K` of
`AlgebraicGeometry.ProEtaleWeilSheaf.transportExtensionByZeroIso`: on underlying sheaves, the
exchange isomorphism `j̄'_! θ_* K ≅ θ_Y_* j̄_! K`. -/
def transportExtensionByZeroIsoApp (K : ProEtaleWeilSheaf k₀ l X) :
    (extensionByZero k₀' l j').obj ((transport θ r hθ).obj K) ≅
      (transport θY r hθY).obj ((extensionByZero k₀ l j).obj K) :=
  IsoAlgebra.isoMk ((adicOpenImmersionLowerShriekSquareIso l hsq).app K.carrier)
    (IsoAlgebra.map_hom_comp_str_of_hom_comp_mono _
      ((transport θY r hθY).map ((extensionByZeroToLowerStar k₀ l j).app K)) _
      (adicOpenImmersionLowerShriekSquareIso_hom_app_comp_transport_map_hom_f θ r hθ θY hθY j j'
        hsq K))

include hsq in
/-- The component `transportExtensionByZeroIsoApp` is the exchange isomorphism
`j̄'_! θ_* ≅ θ_Y_* j̄_!` on underlying sheaves. -/
lemma transportExtensionByZeroIsoApp_hom_hom_f (K : ProEtaleWeilSheaf k₀ l X) :
    (transportExtensionByZeroIsoApp θ r hθ θY hθY j j' hsq K).hom.hom.f =
      ((adicOpenImmersionLowerShriekSquareIso l hsq).app K.carrier).hom :=
  IsoAlgebra.isoMk_hom_hom_f _ _

include hsq in
/-- The components `transportExtensionByZeroIsoApp` are natural. -/
lemma transportExtensionByZeroIsoApp_naturality {K K' : ProEtaleWeilSheaf k₀ l X} (f : K ⟶ K') :
    (transport θ r hθ ⋙ extensionByZero k₀' l j').map f ≫
        (transportExtensionByZeroIsoApp θ r hθ θY hθY j j' hsq K').hom =
      (transportExtensionByZeroIsoApp θ r hθ θY hθY j j' hsq K).hom ≫
        (extensionByZero k₀ l j ⋙ transport θY r hθY).map f := by
  -- The objects are given as `IsoAlgebra.carrier` throughout: unifying them with the projections
  -- `K.obj.a` makes the kernel unfold the exchange isomorphism.
  have h₁ : ((transport θ r hθ ⋙ extensionByZero k₀' l j').map f ≫
      (transportExtensionByZeroIsoApp θ r hθ θY hθY j j' hsq K').hom).hom.f =
        ((θ.hom)_*ᵃ[l] ⋙ (Scheme.Hom.geometricFiberMap j' (comp_over j' _))_!ᵃ[l]).map f.hom.f ≫
          (adicOpenImmersionLowerShriekSquareIso l hsq).hom.app K'.carrier := by
    rw [IsoAlgebra.comp_hom_f, transportExtensionByZeroIsoApp_hom_hom_f, Functor.comp_map,
      extensionByZero_map_hom_f, transport_map_hom_f, Iso.app_hom, Functor.comp_map]
  have h₂ : ((transportExtensionByZeroIsoApp θ r hθ θY hθY j j' hsq K).hom ≫
      (extensionByZero k₀ l j ⋙ transport θY r hθY).map f).hom.f =
        (adicOpenImmersionLowerShriekSquareIso l hsq).hom.app K.carrier ≫
          ((Scheme.Hom.geometricFiberMap j (comp_over j _))_!ᵃ[l] ⋙ (θY.hom)_*ᵃ[l]).map
            f.hom.f := by
    rw [IsoAlgebra.comp_hom_f, transportExtensionByZeroIsoApp_hom_hom_f, Functor.comp_map,
      transport_map_hom_f, extensionByZero_map_hom_f, Iso.app_hom, Functor.comp_map]
  exact IsoAlgebra.hom_ext (h₁.trans
    (((adicOpenImmersionLowerShriekSquareIso l hsq).hom.naturality (X := K.carrier)
      (Y := K'.carrier) f.hom.f).trans h₂.symm))

include hsq in
/-- Transporting along the identifications `θ`, `θ_Y` of geometric fibers commutes with the
extension by zero along open immersions `j : X ⟶ Y` and `j' : X' ⟶ Y'` whose base changes commute
with them. -/
def transportExtensionByZeroIso :
    transport (l := l) θ r hθ ⋙ extensionByZero k₀' l j' ≅
      extensionByZero k₀ l j ⋙ transport θY r hθY :=
  NatIso.ofComponents (transportExtensionByZeroIsoApp θ r hθ θY hθY j j' hsq)
    (transportExtensionByZeroIsoApp_naturality θ r hθ θY hθY j j' hsq)

include hsq in
/-- The components of `transportExtensionByZeroIso` on underlying sheaves are those of the
exchange isomorphism `j̄'_! θ_* ≅ θ_Y_* j̄_!`. -/
@[simp]
lemma transportExtensionByZeroIso_hom_app_hom_f (K : ProEtaleWeilSheaf k₀ l X) :
    ((transportExtensionByZeroIso θ r hθ θY hθY j j' hsq).hom.app K).hom.f =
      (adicOpenImmersionLowerShriekSquareIso l hsq).hom.app K.carrier := by
  rw [transportExtensionByZeroIso, NatIso.ofComponents_hom_app
      (naturality := transportExtensionByZeroIsoApp_naturality θ r hθ θY hθY j j' hsq),
    transportExtensionByZeroIsoApp_hom_hom_f, Iso.app_hom]

end AlgebraicGeometry.ProEtaleWeilSheaf
