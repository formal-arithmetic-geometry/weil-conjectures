/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateTransitivity
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Open exchange and finite reduction for condensed coefficients

Source: latest blueprint, `prop-pur-weil-equivariance-compatibilities`, compact-support
exchange compatibility with reduction, open-immersion factor before proper exchange
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).

All categories are ordinary unbounded derived categories of internal modules over
coefficients pulled back from the point. The index `n : ℕ+` is the exponent of the
uniformizer, not an index in a completed category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedFiniteOpenExchange

/-- Exact derived open extension, using the recorded module-object operation.
Source: blueprint open exchange (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
abbrev J (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (CondensedRing.openImmersionLowerShriek R j).mapDerivedCategory

/-- The exchange type, with the node's orientation `P_g J_j ≅ J_j' P_gU`.
Source: blueprint open exchange (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
abbrev Exchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] :=
  J R j ⋙ QuotientChange.L R g ≅ QuotientChange.L R gU ⋙ J R j'

/-- The canonical scalar/open conjugate, in the recorded scalar functor interface.
Source: blueprint scalar/open comparison
(blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def H {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J R j ⋙ QuotientChange.D a X ≅ QuotientChange.D a U ⋙ J S j := by
  unfold QuotientChange.D
  exact CondensedRing.derivedOpenImmersionShriekIso a j

/-- The exact scalar/open exchange equation, for every normalized pullback comparison.
Using the recorded normalization predicate fixes the maps, including nonflat reductions.
Source: blueprint reduction square
(blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def ScalarSquare {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (a : R ⟶ S) [IsMonHom a]
    (eR : Exchange R gU j' j g) (eS : Exchange S gU j' j g) : Prop :=
  ∀ (lg : QuotientChange.D a X ⋙ QuotientChange.L S g ≅
        QuotientChange.L R g ⋙ QuotientChange.D a X')
    (lU : QuotientChange.D a U ⋙ QuotientChange.L S gU ≅
        QuotientChange.L R gU ⋙ QuotientChange.D a U'),
    QuotientChange.PullNormalized a g lg → QuotientChange.PullNormalized a gU lU →
    ∀ K : DerivedCategory (QuotientChange.Modules R U),
      lg.inv.app ((J R j).obj K) ≫ (QuotientChange.L S g).map ((H a j).hom.app K) ≫
          eS.hom.app ((QuotientChange.D a U).obj K) ≫ (J S j').map (lU.hom.app K) =
        (QuotientChange.D a X').map (eR.hom.app K) ≫
          (H a j').hom.app ((QuotientChange.L R gU).obj K)

/-- Two successive scalar extensions obey the specified open and pullback pasting laws.
The comparison is normalized by the dependency's computation-counit predicate.
The final scalar square for the composite records cancellation of these comparisons.
Source: blueprint successive reductions
(blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def SuccessiveSquare {R S V : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [MonObj V] [IsCommMonObj V]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ V) [IsMonHom b]
    (eR : Exchange R gU j' j g) (eV : Exchange V gU j' j g) : Prop :=
  (∃ comp : ∀ T : Scheme.{u},
      QuotientChange.D a T ⋙ QuotientChange.D b T ≅ QuotientChange.D (a ≫ b) T,
    (∀ T : Scheme.{u}, QuotientChange.SuccessiveNormalized a b (a ≫ b) rfl T (comp T)) ∧
    (∀ K : DerivedCategory (QuotientChange.Modules R U),
      (QuotientChange.D b X).map ((H a j).hom.app K) ≫
          (H b j).hom.app ((QuotientChange.D a U).obj K) ≫
          (J V j).map ((comp U).hom.app K) =
        (comp X).hom.app ((J R j).obj K) ≫ (H (a ≫ b) j).hom.app K) ∧
    (∀ K : DerivedCategory (QuotientChange.Modules R U'),
      (QuotientChange.D b X').map ((H a j').hom.app K) ≫
          (H b j').hom.app ((QuotientChange.D a U').obj K) ≫
          (J V j').map ((comp U').hom.app K) =
        (comp X').hom.app ((J R j').obj K) ≫ (H (a ≫ b) j').hom.app K) ∧
    (∀ {Y Z : Scheme.{u}} (f : Z ⟶ Y)
      (l01 : QuotientChange.D a Y ⋙ QuotientChange.L S f ≅
        QuotientChange.L R f ⋙ QuotientChange.D a Z)
      (l12 : QuotientChange.D b Y ⋙ QuotientChange.L V f ≅
        QuotientChange.L S f ⋙ QuotientChange.D b Z)
      (l02 : QuotientChange.D (a ≫ b) Y ⋙ QuotientChange.L V f ≅
        QuotientChange.L R f ⋙ QuotientChange.D (a ≫ b) Z),
      QuotientChange.PullNormalized a f l01 → QuotientChange.PullNormalized b f l12 →
      QuotientChange.PullNormalized (a ≫ b) f l02 →
      ∀ K : DerivedCategory (QuotientChange.Modules R Y),
        l12.hom.app ((QuotientChange.D a Y).obj K) ≫
            (QuotientChange.D b Z).map (l01.hom.app K) ≫
            (comp Z).hom.app ((QuotientChange.L R f).obj K) =
          (QuotientChange.L V f).map ((comp Y).hom.app K) ≫ l02.hom.app K)) ∧
    ScalarSquare (a ≫ b) eR eV

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

end AlgebraicGeometry.ProEtale.CondensedFiniteOpenExchange
