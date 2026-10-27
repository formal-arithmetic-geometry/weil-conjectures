/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # The derivation action on the étale sheaf of infinitesimal lifts

Source: Stacks Project, Tags 061A, 061C, 061D (scheme case), 04FG, 04FJ,
04FK, and the final paragraph of 02H6
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent).

The ideal on the reduced scheme is its tensor conormal module. The coefficient
comparisons below are normalized on pulled-back local sections. Thus the action
has the specified sign and does not depend on an arbitrary coefficient isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.InfinitesimalLifts
open Scheme.Modules

/-- The square-zero ideal regarded as a module on the closed subscheme: `I/I²`,
which is `I` when `I² = 0`. Source: Stacks 04EX, 061D
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
def idealOnReduction {T₀ T : Scheme.{u}} (i : T₀ ⟶ T) : T₀.Modules :=
  (tensorPullback i).obj i.ker.toModules

/-- The coefficient module `i_* Hom(a₀* Ω, I)` with quotient scalar action.
Source: Stacks 061D, 02H6
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
def coefficients {V W T₀ T : Scheme.{u}} (f : V ⟶ W) (i : T₀ ⟶ T)
    (a₀ : T₀ ⟶ V) : T.Modules :=
  (pushforward i).obj (SheafOfModules.homObj (R := T₀.sheaf)
    ((tensorPullback a₀).obj f.relativeDifferentials) (idealOnReduction i))

/-- Compatible lifts on an étale test scheme. No inhabitance is required.
Source: Stacks 061A, 061D
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
def IsLift {V W T₀ T : Scheme.{u}} (f : V ⟶ W) (i : T₀ ⟶ T)
    (a₀ : T₀ ⟶ V) (b : T ⟶ W) (U : T.Etale) (a : U.left ⟶ V) : Prop :=
  a ≫ f = U.hom ≫ b ∧ pullback.snd i U.hom ≫ a = pullback.fst i U.hom ≫ a₀

/-- Precomposition preserves the two lift equations. Source: Stacks 061A.
Proof: associate composition in the equation over `W`. For the reduction equation,
use the universal morphism between the two fibre products and their projection
identities. This gives exactly the restriction of a compatible lift.
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
theorem isLift_precomp {V W T₀ T : Scheme.{u}} (f : V ⟶ W) (i : T₀ ⟶ T)
    (a₀ : T₀ ⟶ V) (b : T ⟶ W) {U U' : T.Etale} (v : U' ⟶ U)
    (a : U.left ⟶ V) (ha : IsLift f i a₀ b U a) :
    IsLift f i a₀ b U' (v.left ≫ a) := by
  sorry

/-- The subpresheaf of the representable functor consisting of compatible lifts.
Source: Stacks 061A, 061D
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
def liftSubfunctor {V W T₀ T : Scheme.{u}} (f : V ⟶ W) (i : T₀ ⟶ T)
    (a₀ : T₀ ⟶ V) (b : T ⟶ W) :
    Subfunctor ((Scheme.Etale.forget T ⋙ Over.forget T).op ⋙ yoneda.obj V) where
  obj U := {a | IsLift f i a₀ b U.unop a}
  map v a ha := isLift_precomp f i a₀ b v.unop a ha

/-- The lift presheaf, with actual precomposition as restriction. Source: Stacks 061A.
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
def liftPresheaf {V W T₀ T : Scheme.{u}} (f : V ⟶ W) (i : T₀ ⟶ T)
    (a₀ : T₀ ⟶ V) (b : T ⟶ W) : T.Etaleᵒᵖ ⥤ Type u :=
  (liftSubfunctor f i a₀ b).toFunctor

/-- The two normalized coefficient comparisons on each étale object. `ideal` is
flat base change of the square-zero ideal; `hom` is flat base change of sheaf Hom.
Their evaluation equations fix the usual tensor maps on local generators.
Source: Stacks 061C, 061D, 02H6, and 02KG
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
structure CoefficientComparison {V W T₀ T : Scheme.{u}}
    (f : V ⟶ W) (i : T₀ ⟶ T) (a₀ : T₀ ⟶ V) (U : T.Etale) where
  ideal : (pushforward (pullback.snd i U.hom)).obj
    ((tensorPullback (pullback.fst i U.hom)).obj (idealOnReduction i)) ≅
      (pullback.snd i U.hom).ker.toModules
  hom : (tensorPullback U.hom).obj (coefficients f i a₀) ≅
    (pushforward (pullback.snd i U.hom)).obj
      (SheafOfModules.homObj (R := (pullback i U.hom).sheaf)
        ((tensorPullback (pullback.fst i U.hom)).obj
          ((tensorPullback a₀).obj f.relativeDifferentials))
        ((tensorPullback (pullback.fst i U.hom)).obj (idealOnReduction i)))
  ideal_eval : ∀ (O : T.Opens) (Q : U.left.Opens) (hu : Q ≤ U.hom ⁻¹ᵁ O)
    (h₀ : (pullback.snd i U.hom) ⁻¹ᵁ Q ≤
      (pullback.fst i U.hom) ⁻¹ᵁ (i ⁻¹ᵁ O)) (s : Γ(i.ker.toModules, O)),
    (pullback.snd i U.hom).ker.toModulesι.app Q
      (ideal.hom.app Q
        (((tensorPullback (pullback.fst i U.hom)).obj (idealOnReduction i)).val.map
          (homOfLE h₀).op
          (tensorPullbackSection (pullback.fst i U.hom) (idealOnReduction i) (i ⁻¹ᵁ O)
            (tensorPullbackSection i i.ker.toModules O s)))) =
      U.hom.appLE O Q hu (i.ker.toModulesι.app O s)
  hom_eval : ∀ (O : T.Opens) (Q : U.left.Opens) (hu : Q ≤ U.hom ⁻¹ᵁ O)
    (h₀ : (pullback.snd i U.hom) ⁻¹ᵁ Q ≤
      (pullback.fst i U.hom) ⁻¹ᵁ (i ⁻¹ᵁ O))
    (h : Γ(coefficients f i a₀, O))
    (e : Γ((tensorPullback a₀).obj f.relativeDifferentials, i ⁻¹ᵁ O)),
    ((hom.hom.app Q
      (((tensorPullback U.hom).obj (coefficients f i a₀)).val.map (homOfLE hu).op
        (tensorPullbackSection U.hom (coefficients f i a₀) O h))).app
          (op (Over.mk (𝟙 ((pullback.snd i U.hom) ⁻¹ᵁ Q)))))
      (((tensorPullback (pullback.fst i U.hom)).obj
        ((tensorPullback a₀).obj f.relativeDifferentials)).val.map (homOfLE h₀).op
          (tensorPullbackSection (pullback.fst i U.hom)
            ((tensorPullback a₀).obj f.relativeDifferentials) (i ⁻¹ᵁ O) e)) =
    ((tensorPullback (pullback.fst i U.hom)).obj (idealOnReduction i)).val.map
      (homOfLE h₀).op (tensorPullbackSection (pullback.fst i U.hom)
        (idealOnReduction i) (i ⁻¹ᵁ O)
        (h.app (op (Over.mk (𝟙 (i ⁻¹ᵁ O)))) e))

/-- The normalized action, allowed on empty sets of lifts. The last field is the
formula `c^sharp = a^sharp + D`, evaluated on arbitrary local ring sections.
The differential and tensor-composition maps turn the coefficient homomorphism
into exactly the relative derivation of Stacks equation (04FG).
Source: Stacks 061C, 061D, 04FG, 04FJ, 04FK
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent). -/
structure DerivationAction {V W T₀ T : Scheme.{u}}
    (f : V ⟶ W) (i : T₀ ⟶ T) (a₀ : T₀ ⟶ V) (b : T ⟶ W) where
  comparison : ∀ U : T.Etale, CoefficientComparison f i a₀ U
  act : ∀ U : T.Etale, Γ((tensorPullback U.hom).obj (coefficients f i a₀), ⊤) →
    (liftPresheaf f i a₀ b).obj (op U) → (liftPresheaf f i a₀ b).obj (op U)
  zero_act : ∀ U a, act U 0 a = a
  add_act : ∀ U h k a, act U (h + k) a = act U h (act U k a)
  naturality : ∀ {U U' : T.Etale} (v : U' ⟶ U) h a,
    (liftPresheaf f i a₀ b).map v.op (act U h a) =
      act U' (etaleTensorSectionsRestriction (coefficients f i a₀) v h)
        ((liftPresheaf f i a₀ b).map v.op a)
  simply_transitive : ∀ U a, Function.Bijective (fun h ↦ act U h a)
  same_base : ∀ U h a, (act U h a).val.base = a.val.base
  formula : ∀ (U : T.Etale) (h : Γ((tensorPullback U.hom).obj (coefficients f i a₀), ⊤))
    (a : (liftPresheaf f i a₀ b).obj (op U)) (P : V.Opens) (Q : U.left.Opens)
    (ha : Q ≤ a.val ⁻¹ᵁ P) (hc : Q ≤ (act U h a).val ⁻¹ᵁ P)
    (hg : (pullback.snd i U.hom) ⁻¹ᵁ Q ≤ (pullback.fst i U.hom ≫ a₀) ⁻¹ᵁ P)
    (ht : (pullback.snd i U.hom) ⁻¹ᵁ Q ≤ (pullback.snd i U.hom) ⁻¹ᵁ ⊤)
    (x : Γ(V, P)),
    (act U h a).val.appLE P Q hc x = @id Γ(U.left, Q) (a.val.appLE P Q ha x) +
      @id Γ(U.left, Q) ((pullback.snd i U.hom).ker.toModulesι.app Q
        ((comparison U).ideal.hom.app Q
          ((((comparison U).hom.hom.app ⊤ h).app (op (Over.mk (homOfLE ht))))
            (((tensorPullback (pullback.fst i U.hom)).obj
              ((tensorPullback a₀).obj f.relativeDifferentials)).val.map (homOfLE hg).op
              (((tensorSectionsComp (pullback.fst i U.hom) a₀).inv.app
                f.relativeDifferentials).app ((pullback.fst i U.hom ≫ a₀) ⁻¹ᵁ P)
                (tensorPullbackSection (pullback.fst i U.hom ≫ a₀) f.relativeDifferentials P
                  (f.relativeDifferentialsDerivation.d x)))))))

/-- The compatible-lift presheaf is a sheaf, its derivation coefficient is
quasi-coherent, and it has the natural simply transitive action with the specified
addition-of-derivations formula. This asserts no existence of lifts.
Source: Stacks 061A, 061C, 061D and the final paragraph of 02H6
(blueprint: lem-sfb-etale-local-lift-torsor-quasi-coherent).

Proof:
1. On affine charts, finite presentation of the algebra implies finite presentation
   of its differentials (lem-sfb-ring-finite-presentation-differentials). The affine
   criterion (lem-weil-pbc-quasi-coherent-finite-type-affine) and tensor pullback
   (lem-pc-tensor-pullback-finite-presentation) make E finitely presented. The ideal
   on T₀ is I/I² = I, quasi-coherent by its affine description. Apply
   lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent and
   lem-weil-pbc-closed-immersion-pushforward-annihilated to obtain quasi-coherence of H.
2. Glue compatible maps by lem-weil-pbc-fpqc-finer-than-etale and
   lem-weil-pbc-fpqc-representable-descent. Check their two equations by uniqueness,
   using lem-weil-pbc-fpqc-covering-axioms for the base-changed cover of U₀.
3. Etale flatness and lem-weil-pbc-flat-tensor-exact identify the ideal on U with
   the pullback of I. Apply lem-weil-pbc-flat-base-change-hom-finitely-presented,
   lem-weil-pbc-affine-tilde-gamma-adjunction and lem-weil-pbc-tilde-pullback-base-change
   to Hom. The closed immersion is affine (pqf-def-affine-morphism); apply
   lem-weil-pbc-affine-pushforward-base-change. The tensor formula on local sections
   gives precisely the two normalized comparisons above.
4. Tensor composition and lem-pc-module-pullback-adjunction identify coefficients
   with maps from Ω to the pushed-forward ideal. The universal property of relative
   differentials (lem-sfb-relative-differentials-sheaf-universal-property, realized
   by relativeDifferentialsHomEquiv) identifies these maps with W-derivations D.
5. Add D to a^sharp. Square zero kills D(x)D(y), so Leibniz proves multiplicativity;
   the other ring identities and the equation over W follow from derivation identities.
   On each affine target chart use lem-weil-pbc-morphism-into-affine-scheme to obtain
   the scheme map. Its topological map is unchanged, since U₀ and U have the same
   points. These local maps glue, giving the formula in DerivationAction.
6. Conversely the difference of any two lifts lies in the ideal and is a relative
   derivation by the same product expansion. The universal property gives the unique
   coefficient. Addition/subtraction are inverse, proving all orbit bijections.
   The zero and addition identities are the corresponding identities of derivations.
7. Pullback commutes with the sectionwise sum and both normalized comparisons.
   Uniqueness therefore proves restriction compatibility. For an empty lift set,
   every action map and law is the unique empty map or a vacuous assertion. -/
theorem exists_derivationAction {V W T₀ T : Scheme.{u}} (f : V ⟶ W)
    [LocallyOfFinitePresentation f] (i : T₀ ⟶ T) (hi : IsFirstOrderThickening i)
    (a₀ : T₀ ⟶ V) (b : T ⟶ W) (comm : a₀ ≫ f = i ≫ b) :
    (coefficients f i a₀).IsQuasicoherent ∧
      Presheaf.IsSheaf T.smallEtaleTopology (liftPresheaf f i a₀ b) ∧
      Nonempty (DerivationAction f i a₀ b) := by
  sorry

end AlgebraicGeometry.Scheme.InfinitesimalLifts
