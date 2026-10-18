module
public import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
public import Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Normalized reconstruction from two successive support conditions

Source: Stacks Project, Pro-etale Cohomology, Tag 09AH; Categories, Tag 0037
(blueprint: lem-sfb-proetale-supported-reconstruction).

The statement records the canonical reconstruction of a module sheaf supported on a
closed subscheme and then on an open stratum.  The underlying ring sheaf is transported
to additive sheaves only to use the published module-object realization; no coefficient
or functor is chosen privately.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Additive realization of a commutative pro-etale ring sheaf.
Source: Stacks, Tag 03D1 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedRingAb {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (AlgebraicGeometry.Scheme.proEtaleModuleCoefficients R)

/-- The monoid object transported along a pro-etale inverse image.
Source: Stacks, Tags 03D1 and 09A5 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedRingMon {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :=
  (f)^*[Ab.{u + 1}].mapMon.obj (Mon.mk (supportedRingAb R))

/-- The monoid object after a second inverse-image transport.
Source: Stacks, Tags 03D1 and 09A5 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedRingMonComp {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Mon (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  (g)^*[Ab.{u + 1}].mapMon.obj (supportedRingMon f R)

/-- Closed inverse-image and direct-image module functors used by reconstruction.
Source: Stacks, Tags 03D1 and 03D3 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedClosedPullback {X Z : Scheme.{u}} (i : Z ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafInverseImage i (supportedRingAb R)

noncomputable abbrev supportedClosedPushforward {X Z : Scheme.{u}} (i : Z ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafDirectImage i (supportedRingAb R)

/-- Open inverse-image module functor after the closed coefficient transport.
Source: Stacks, Tags 03D1 and 03D3 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedOpenPullback {X Z S : Scheme.{u}}
    (i : Z ⟶ X) (u : S ⟶ Z)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafInverseImage u (supportedRingMon i R).X

/-- Extension by zero from the open stratum after the closed coefficient transport.
Source: Stacks, Tags 03DI and 03DJ (blueprint: lem-sfb-proetale-supported-reconstruction). -/
noncomputable abbrev supportedOpenExtension {X Z S : Scheme.{u}}
    (i : Z ⟶ X) (u : S ⟶ Z) [IsOpenImmersion u]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafOpenExtension u (supportedRingMon i R).X

/-- The normalized open counit map in the reconstruction statement.
Source: Stacks, Tag 09AH (blueprint: lem-sfb-proetale-supported-reconstruction). -/
noncomputable def supportedLambda {X Z S : Scheme.{u}}
    (i : Z ⟶ X) (u : S ⟶ Z) [IsOpenImmersion u]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj ((supportedClosedPullback i R).obj A) ≅ M) :
    (supportedOpenExtension i u R).obj M ⟶ (supportedClosedPullback i R).obj A :=
  (supportedOpenExtension i u R).map σ.inv ≫
    (ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app
      ((supportedClosedPullback i R).obj A)

/-- The support hypotheses make the normalized open map invertible.
Source: Stacks, Tag 09AH (blueprint: lem-sfb-proetale-supported-reconstruction).
The two localization sequences identify the closed unit and open counit with
isomorphisms; this named fact supplies the inverse used by `supportedTheta`. -/
theorem supportedLambda_isIso {X Z S B K : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (e : B ⟶ Z) [IsClosedImmersion e]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) [IsOpenImmersion u] [QuasiCompact u]
    (hk : Set.range k = (Set.range i)ᶜ)
    (hu : Set.range u = (Set.range e)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj
      ((supportedClosedPullback i R).obj A) ≅ M)
    (hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A))
    (hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
      ((supportedClosedPullback i R).obj A))) :
    IsIso (supportedLambda i u R A M σ) := by
  sorry

/-- The closed-adjunction transpose of the normalized map.
Source: Stacks, Tag 0037 (blueprint: lem-sfb-proetale-supported-reconstruction).
-/
noncomputable def supportedTheta {X Z S B K : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (e : B ⟶ Z) [IsClosedImmersion e]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) [IsOpenImmersion u] [QuasiCompact u]
    (hk : Set.range k = (Set.range i)ᶜ)
    (hu : Set.range u = (Set.range e)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj
      ((supportedClosedPullback i R).obj A) ≅ M)
    (hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A))
    (hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
      ((supportedClosedPullback i R).obj A))) :
    A ⟶ (supportedClosedPushforward i R).obj
      ((supportedOpenExtension i u R).obj M) := by
  letI := supportedLambda_isIso i e k u hk hu R A M σ hK hB
  exact (ringSheafAdjunction i (supportedRingAb R)).unit.app A ≫
    (supportedClosedPushforward i R).map (inv (supportedLambda i u R A M σ))

/-- Normalized reconstruction from two successive support conditions.
Source: Stacks Project, Pro-etale Cohomology, Tag 09AH, and Categories, Tag 0037
(blueprint: lem-sfb-proetale-supported-reconstruction).
Proof: apply the arbitrary-ring open--closed localization sequence first to `(i,k)`
and then to `(e,u)`.  The two vanishing restrictions make the closed unit and open
counit invertible.  Transpose the inverse of `supportedLambda` through the closed
adjunction to obtain `supportedTheta`; the triangle identities give the displayed
restriction equation.  Transposing an arbitrary map with that equation and cancelling
the invertible open counit gives uniqueness.  Naturality follows from naturality of
both units and counits and the commuting equation for the two input morphisms.
-/
theorem supported_reconstruction
    {X Z S B K : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (e : B ⟶ Z) [IsClosedImmersion e]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) [IsOpenImmersion u] [QuasiCompact u]
    (hk : Set.range k = (Set.range i)ᶜ)
    (hu : Set.range u = (Set.range e)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj ((supportedClosedPullback i R).obj A) ≅ M)
    (hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A))
    (hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
      ((supportedClosedPullback i R).obj A))) :
    IsIso (supportedLambda i u R A M σ) ∧
      IsIso (supportedTheta i e k u hk hu R A M σ hK hB) ∧
      (supportedOpenPullback i u R).map
          ((supportedClosedPullback i R).map (supportedTheta i e k u hk hu R A M σ hK hB)) ≫
        (supportedOpenPullback i u R).map
          ((ringSheafAdjunction i (supportedRingAb R)).counit.app
            ((supportedOpenExtension i u R).obj M)) =
      σ.hom ≫ (ringSheafOpenAdjunction u (supportedRingMon i R).X).unit.app M ∧
      (∀ (h : A ⟶ (supportedClosedPushforward i R).obj
          ((supportedOpenExtension i u R).obj M)),
        (supportedOpenPullback i u R).map
            ((supportedClosedPullback i R).map h) ≫
          (supportedOpenPullback i u R).map
            ((ringSheafAdjunction i (supportedRingAb R)).counit.app
              ((supportedOpenExtension i u R).obj M)) =
        σ.hom ≫ (ringSheafOpenAdjunction u (supportedRingMon i R).X).unit.app M →
          h = supportedTheta i e k u hk hu R A M σ hK hB) ∧
      (∀ {A' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R)}
          {M' : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (supportedRingMonComp i u R).X}
          (σ' : (supportedOpenPullback i u R).obj
            ((supportedClosedPullback i R).obj A') ≅ M')
          (hK' : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A'))
          (hB' : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
            ((supportedClosedPullback i R).obj A')))
          (a : A ⟶ A') (b : M ⟶ M'),
        (supportedOpenPullback i u R).map
              ((supportedClosedPullback i R).map a) ≫ σ'.hom = σ.hom ≫ b →
          ((supportedOpenExtension i u R).map b ≫
              supportedLambda i u R A' M' σ' =
            supportedLambda i u R A M σ ≫
              (supportedClosedPullback i R).map a) ∧
          (a ≫ supportedTheta i e k u hk hu R A' M' σ' hK' hB' =
            supportedTheta i e k u hk hu R A M σ hK hB ≫
              (supportedClosedPushforward i R).map
                ((supportedOpenExtension i u R).map b))) := by
  sorry

end AlgebraicGeometry.ProEtale
