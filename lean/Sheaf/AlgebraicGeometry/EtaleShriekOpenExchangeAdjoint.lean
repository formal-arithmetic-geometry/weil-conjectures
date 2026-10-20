module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.Paper.UnboundedProperOpenInterchange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Open compact-support exchange and the extension-composition mate

Source: literature/stacks-project/more-etale.tex, Tags 0F7B, 0F7J and 0F7L
(blueprint: lem-amb-shriek-open-exchange-adjoint).
-/


open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Etale

@[expose] public section

namespace AlgebraicGeometry.Etale

-- Re-recorded by Q87 for the stage-2 delivery on 2026-10-18.

universe u

set_option autoImplicit false

/-- The extension/composition comparison `δ : Rf_! Dv_! ≅ Du_! Rf_{U!}` of the node, namely
`α_{u,f_U}⁻¹ ∘ α_{f,v}` with compact support along the opens `v` and `u` identified with
termwise extension by zero through the compactification `(w, 𝟙)`
(`rightDerivedLowerShriekIsoOfIsOpenImmersion`) and the refinement comparisons.
Source: Stacks Project, Tags 0F7B, 0F7J and 0F7L
(blueprint: lem-amb-shriek-open-exchange-adjoint).
-/
noncomputable def openExchangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekIsoOfIsOpenImmersion A (pullback.fst f u)).symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
    unboundedEtaleLowerShriekCompIso A (pullback.fst f u) f ≪≫
    unboundedEtaleLowerShriekCongr A (pullback.condition) ≪≫
    (unboundedEtaleLowerShriekCompIso A (pullback.snd f u) u).symm ≪≫
    Functor.isoWhiskerLeft
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u))
      (rightDerivedLowerShriekIsoOfIsOpenImmersion A u)

/-- The canonical compact-support exchange for the cartesian square of an open immersion.
Source: Stacks Project, Tag 0F7L (blueprint: lem-amb-shriek-open-exchange-adjoint).
-/
noncomputable def canonicalCompactSupportExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u) := by
  let sq : IsPullback (pullback.fst f u) (pullback.snd f u) f u :=
    IsPullback.of_hasPullback f u
  letI : IsIso (unboundedEtaleCompactSupportBaseChange A sq) :=
    (unboundedEtaleCompactSupport_baseChange A sq).1
  exact asIso (unboundedEtaleCompactSupportBaseChange A sq)

/-- The extension/composition comparison mate is the canonical compact-support exchange: for
`f : X ⟶ S` separated, of finite type and compactifiable, an open immersion `u : U ⟶ S`,
`v = pullback.fst f u` and `f_U = pullback.snd f u`, the map
`κ_F = Rf_!(ε_{v,F}) ∘ δ_{v^*F}⁻¹ : Du_! Rf_{U!} v^*F ⟶ Rf_! F` has adjunct `C_{f,u,F}⁻¹`
under `Du_! ⊣ u^*`; equivalently `κ_F = ε_{u,Rf_!F} ∘ Du_!(C_{f,u,F}⁻¹)`. No boundedness
assumption on `F` is made.
Source: Stacks Project, Tags 0F7B, 0F7J and 0F7L; etale-cohomology Tags 03S3,
03S6 and 0F70 (blueprint: lem-amb-shriek-open-exchange-adjoint).

Proof:
1. Choose a compactification `f = r ∘ j` and its pullback along `u`: open
   `b : X̄_U ⟶ X̄`, `j_U : X_U ⟶ X̄_U` and proper `r_U : X̄_U ⟶ U`. Put `J = Dj_!`,
   `J' = Dj_{U!}`, `V = Dv_!`, `B = Db_!`, `L = Du_!`, `P = Rr_*`, `P' = Rr_{U*}`. Let
   `a : JV ≅ BJ'` be the adjunction-normalized open composition identification for
   `j v = b j_U` (lem-cbc-extension-zero-composition). Compact support along an open `w`
   is identified with `Dw_!` by the compactification `(w, 𝟙)`; the sheaf counit for an
   open is evaluation (lem-weil-pbc-extension-by-zero-adjunction), with its termwise derived
   adjunction (lem-amb-etale-adjoint-locality). Let `Γ : L P' ≅ P B` be the interchange for
   the cartesian square `(b, r_U, r, u)` (lem-amb-unbounded-proper-open-interchange). The
   tower formula for `α` (lem-amb-unbounded-compact-support-comparisons) gives
   `δ_M⁻¹ = P(a_M⁻¹) ∘ Γ_{J'M}`: for `α_{f,v}` the tower square has identity bottom open and
   gives the open composition identification, for `α_{u,f_U}` it is the square
   `(b, r_U, r, u)`. All schemes are Noetherian, so the opens are quasi-compact of finite
   type, and the comparisons and interchange apply on the unbounded categories.
2. Write `E : u^* P ⟶ P' b^*` for proper exchange and `e : b^* J ≅ J' v^*` for the inverse
   open base-change comparison, so `C_F = P'(e_F) ∘ E_{JF}`
   (lem-amb-unbounded-compact-support-comparisons); `e` has the unit normalization of
   lem-cbc-derived-extension-zero-base-change-underived-compatibility. For `H = J' v^* F` put
   `h = J(ε_{v,F}) ∘ a_{v^*F}⁻¹ : B H ⟶ J F`. On an etale test object over `X̄_U` both
   `b^* B H` and `H` are extensions by zero from `X_U`; restricting to `X_U` identifies `a`,
   the restricted evaluation counit and `e` with identities, so
   `e_F ∘ b^* h ∘ η_{b,H} = 1_H`, first for sheaves and then degreewise on complexes. The
   cartesian clause of lem-amb-unbounded-proper-open-interchange says the adjunct of `Γ_H` is
   `λ_H⁻¹` with `λ_H = P'(η_{b,H}⁻¹) ∘ E_{BH}`, hence
   `E_{BH} ∘ u^*(Γ_H) ∘ η_{u,P'H} = P'(η_{b,H})`. By step 1, `κ_F = P(h) ∘ Γ_H`. For its
   adjunct `m_F = u^* κ_F ∘ η_{u,P'H}`, naturality of `E` in `h` gives
   `C_F ∘ m_F = P'(e_F) ∘ E_{JF} ∘ u^*P(h) ∘ u^*(Γ_H) ∘ η_{u,P'H}`
   `= P'(e_F ∘ b^* h) ∘ E_{BH} ∘ u^*(Γ_H) ∘ η_{u,P'H} = P'(e_F ∘ b^* h ∘ η_{b,H}) = 1_{P'H}`.
   Since `C_F` is an isomorphism, `m_F = C_F⁻¹`, the first conjunct.
3. The adjunction bijection for `Du_! ⊣ u^*` is injective, so the equality of adjuncts in
   step 2 gives `κ_F = ε_{u,Rf_!F} ∘ Du_!(C_F⁻¹)`, the second conjunct. Every comparison and
   adjunction used is constructed on the whole unbounded derived category, so `F` is
   arbitrary.
-/
theorem openExchange_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    (F : DerivedCategoryModule A X) :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) u).homEquiv
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u)).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory.obj F))
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj F)
      ((openExchangeIso A u).inv.app
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory.obj F) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (pullback.fst f u)).counit.app F)) =
      (canonicalCompactSupportExchange A u).inv.app F) ∧
    ((openExchangeIso A u).inv.app
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory.obj F) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (pullback.fst f u)).counit.app F)) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory.map
        ((canonicalCompactSupportExchange A u).inv.app F) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) u).counit.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj F) := by
  sorry

end AlgebraicGeometry.Etale

end
