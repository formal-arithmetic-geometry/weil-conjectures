/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Balanced scalar comparisons and coefficient tower squares

Source: Stacks Project, sites-modules.tex, Tag 03EK, section-tensor-product;
agent balanced reassociation and coefficient quotient/transition calculation, Steps 1–7
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares).

The positive level m is indexed by n = m - 1. All tensors are the existing
sheafified balanced scalar extension, with the scalar first. Termwise extension
is the degreewise model of the direct-sum total tensor with coefficients in degree zero.
Inverse image uses its canonical corresponding-object model. The auxiliary structures
only collect the coefficient data and equations in this node's hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe t r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme CategoryTheory.CochainPullback

namespace AlgebraicGeometry.ProEtale.ScalarQuotientChain

/-- Coefficients in any universe containing the small site's objects.
Source: Stacks 03EK and 09A5
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev Coeff (W : Scheme.{t}) :=
  Sheaf (ProEt.topology W) CommRingCat.{max r (t + 1)}

/-- Forget only commutativity, retaining the given ring sheaf.
Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev forgetRing (W : Scheme.{t}) :=
  sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})

/-- The existing complex category, with all site and coefficient sizes explicit.
Source: Stacks 03EL
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev moduleComplex (W : Scheme.{t}) (R : Coeff.{t, r} W) :=
  CochainComplex (ringedSiteModules.{max r (t + 1)} ((forgetRing W).obj R)) ℤ

/-- Specialization of the existing scalar-extension functor to the given pro-etale site.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev scalarExtend (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B) :
    moduleComplex W A ⥤ moduleComplex W B :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a).mapHomologicalComplex (.up ℤ)

/-- Specialization of existing scalar restriction on complexes.
Source: Stacks 03D2
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev scalarRestrict (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B) :=
  CochainPullback.restrictComplex.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a

/-- The existing scalar-extension pure tensor with its site explicitly supplied.
Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev pure (W : Scheme.{t}) {A B : Coeff.{t, r} W} (a : A ⟶ B)
    (M : ringedSiteModules.{max r (t + 1)} ((forgetRing W).obj A))
    (U : W.ProEtᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :=
  extensionTmul.{max r (t + 1), t + 1, t} (C := W.ProEt)
    (J := ProEt.topology W) a M U s x

/-- The two towers, coefficient projections and commuting squares of the hypotheses.
Level n denotes the positive level n+1; no map is required to be surjective or flat.
Source: Stacks 03EK, node coefficient data
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
structure Tower (W : Scheme.{t}) where
  R : Coeff.{t, r} W
  S : Coeff.{t, r} W
  A : ℕ → Coeff.{t, r} W
  B : ℕ → Coeff.{t, r} W
  j : R ⟶ S
  i : ∀ n : ℕ, A n ⟶ B n
  piA : ∀ n : ℕ, R ⟶ A n
  piB : ∀ n : ℕ, S ⟶ B n
  qA : ∀ n : ℕ, A (Nat.succ n) ⟶ A n
  qB : ∀ n : ℕ, B (Nat.succ n) ⟶ B n
  transition_i : ∀ n : ℕ, i (Nat.succ n) ≫ qB n = qA n ≫ i n
  projection_A : ∀ n : ℕ, piA (Nat.succ n) ≫ qA n = piA n
  projection_B : ∀ n : ℕ, piB (Nat.succ n) ≫ qB n = piB n
  projection_i : ∀ n : ℕ, j ≫ piB n = piA n ≫ i n

/-- The recorded corresponding-object inverse image on commutative ring sheaves.
Source: Stacks 09A5 and 00WX
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev inverseRing {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}

/-- The four specified coefficient isomorphisms and all their compatibilities.
Source: Stacks 03EK, node coefficient data
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
structure Transport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (DX : Tower.{t, r} X) (DY : Tower.{t, r} Y) where
  cR : (inverseRing g).obj DY.R ≅ DX.R
  cS : (inverseRing g).obj DY.S ≅ DX.S
  cA : ∀ n : ℕ, (inverseRing g).obj (DY.A n) ≅ DX.A n
  cB : ∀ n : ℕ, (inverseRing g).obj (DY.B n) ≅ DX.B n
  j_comm : (inverseRing g).map DY.j ≫ cS.hom = cR.hom ≫ DX.j
  i_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.i n) ≫ (cB n).hom = (cA n).hom ≫ DX.i n
  piA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piA n) ≫ (cA n).hom = cR.hom ≫ DX.piA n
  piB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.piB n) ≫ (cB n).hom = cS.hom ≫ DX.piB n
  qA_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qA n) ≫ (cA n).hom = (cA (Nat.succ n)).hom ≫ DX.qA n
  qB_comm : ∀ n : ℕ,
    (inverseRing g).map (DY.qB n) ≫ (cB n).hom = (cB (Nat.succ n)).hom ≫ DX.qB n

/-- The existing inverse image with its action transported through c inverse.
Source: Stacks 03D2, 09A5 and 00WX
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev inverseModules {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) :
    ringedSiteModules.{max r (t + 1)} ((forgetRing Y).obj RY) ⥤
      ringedSiteModules.{max r (t + 1)} ((forgetRing X).obj RX) :=
  isoSectionwiseModuleInverseImage.{t, r} g
    (RY := (forgetRing Y).obj RY) (RX := (forgetRing X).obj RX)
    ((forgetRing X).map c.hom)

/-- Termwise application of the transported inverse image.
Source: Stacks 03EL and 03D2
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev inverseComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Coeff.{t, r} Y} {RX : Coeff.{t, r} X}
    (c : (inverseRing g).obj RY ≅ RX) : moduleComplex Y RY ⥤ moduleComplex X RX :=
  (inverseModules g c).mapHomologicalComplex (.up ℤ)

variable {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  {DX : Tower.{t, r} X} {DY : Tower.{t, r} Y} (d : Transport g DX DY)

/-- The upper left functor P ↦ G_R(P) tensor S_X.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev left : moduleComplex Y DY.R ⥤ moduleComplex X DX.S := (inverseModules g d.cR ⋙
  extensionFunctor.{max r (t + 1), t + 1, t} DX.j).mapHomologicalComplex (.up ℤ)

/-- The upper right functor P ↦ G_S(P tensor S_Y).
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev right : moduleComplex Y DY.R ⥤ moduleComplex X DX.S :=
  (extensionFunctor.{max r (t + 1), t + 1, t} DY.j ⋙
  inverseModules g d.cS).mapHomologicalComplex (.up ℤ)

/-- The finite source, retaining its B_X,n-linear structure.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev finiteLeft (n : ℕ) : moduleComplex Y DY.R ⥤ moduleComplex X (DX.B n) :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n) ⋙
    inverseModules g (d.cA n) ⋙ extensionFunctor.{max r (t + 1), t + 1, t}
      (DX.i n)).mapHomologicalComplex (.up ℤ)

/-- The finite target, retaining its B_X,n-linear structure.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev finiteRight (n : ℕ) : moduleComplex Y DY.R ⥤ moduleComplex X (DX.B n) :=
  (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙
    inverseModules g (d.cB n)).mapHomologicalComplex (.up ℤ)

/-- The finite source with its S_X-action restricted along piB.
Source: Stacks 03D2 and 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev restrictedLeft (n : ℕ) :=
  finiteLeft g d n ⋙ scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)

/-- The finite target with its S_X-action restricted along piB.
Source: Stacks 03D2 and 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
abbrev restrictedRight (n : ℕ) :=
  finiteRight g d n ⋙ scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)

/-- A local tensor F(p tensor a) tensor s, in the specified finite source.
Source: Stacks 03EK, coefficient reassociation
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def doublePure (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (a : (DY.A n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : (DX.B n).obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((finiteLeft g d n).obj P).X k).val.obj (op U) :=
  pure X (DX.i n)
    ((inverseModules g (d.cA n)).obj ((extensionFunctor.{max r (t + 1), t + 1, t}
      (C := Y.ProEt) (J := ProEt.topology Y) (DY.piA n)).obj (P.X k)))
    (op U) s (pure Y (DY.piA n) (P.X k)
      (op ((proEtaleIsoPostcompose g).obj U)) a p)

/-- A local tensor F(p tensor s) in the specified finite target.
Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def finitePure (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : (DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((finiteRight g d n).obj P).X k).val.obj (op U) :=
  pure Y (DY.j ≫ DY.piB n) (P.X k)
    (op ((proEtaleIsoPostcompose g).obj U)) s p

/-- A local tensor Fp tensor s in the upper source.
Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def leftPure (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : DX.S.obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((left g d).obj P).X k).val.obj (op U) :=
  pure X DX.j ((inverseModules g d.cR).obj (P.X k)) (op U) s p

/-- A local tensor F(p tensor s) in the upper target.
Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def rightPure (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : DY.S.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((right g d).obj P).X k).val.obj (op U) :=
  pure Y DY.j (P.X k) (op ((proEtaleIsoPostcompose g).obj U)) s p

/-- The given upper balanced comparison is normalized on all local pure tensors.
Source: Stacks 03EK, node normalization of b_P
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def UpperFormula (b : left g d ≅ right g d) : Prop :=
  ∀ (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : DY.S.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    ((b.hom.app P).f k).val.app (op U)
      (leftPure g d P k U (d.cS.hom.hom.app (op U) s) p) = rightPure g d P k U s p

/-- Both mutually inverse local rules of the finite comparison.
Source: Stacks 03EK, balanced reassociation, node Steps 2–3
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def FiniteFormulas (bfin : ∀ n : ℕ, finiteLeft g d n ≅ finiteRight g d n) : Prop :=
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (a : (DY.A n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : (DX.B n).obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((bfin n).hom.app P).f k).val.app (op U) (doublePure g d n P k U a s p) =
      finitePure g d n P k U
        ((DY.i n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a *
          (@id ((DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
            ((d.cB n).inv.hom.app (op U) s))) p) ∧
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : (DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((bfin n).inv.app P).f k).val.app (op U) (finitePure g d n P k U s p) =
      doublePure g d n P k U 1 ((d.cB n).hom.hom.app (op U) s) p)

/-- The two coefficient maps on all pure tensors in the upper source and target.
Source: Stacks 03EK, node Step 4
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def QuotientFormulas
    (v : ∀ n : ℕ, left g d ⟶ restrictedLeft g d n)
    (w : ∀ n : ℕ, right g d ⟶ restrictedRight g d n) : Prop :=
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : DX.S.obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((v n).app P).f k).val.app (op U) (leftPure g d P k U s p) =
      doublePure g d n P k U 1 ((DX.piB n).hom.app (op U) s) p) ∧
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : DY.S.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((w n).app P).f k).val.app (op U) (rightPure g d P k U s p) =
      finitePure g d n P k U
        ((DY.piB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p)

/-- The source and target transitions induced by qA and qB on local tensors.
Source: Stacks 03EK, node Step 6
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares). -/
def TransitionFormulas
    (v : ∀ n : ℕ, restrictedLeft g d (Nat.succ n) ⟶ restrictedLeft g d n)
    (w : ∀ n : ℕ, restrictedRight g d (Nat.succ n) ⟶ restrictedRight g d n) : Prop :=
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (a : (DY.A (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : (DX.B (Nat.succ n)).obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((v n).app P).f k).val.app (op U) (doublePure g d (Nat.succ n) P k U a s p) =
      doublePure g d n P k U
        ((DY.qA n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a)
        ((DX.qB n).hom.app (op U) s) p) ∧
  (∀ (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) (U : X.ProEt)
    (s : (DY.B (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((w n).app P).f k).val.app (op U) (finitePure g d (Nat.succ n) P k U s p) =
      finitePure g d n P k U
        ((DY.qB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p)


set_option backward.isDefEq.respectTransparency true

section AdjointTransport

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
  [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
  {L₁ : A₁ ⥤ B₁} {V₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {V₂ : B₂ ⥤ A₂}
  (a₁ : L₁ ⊣ V₁) (a₂ : L₂ ⊣ V₂)
  (G : A₁ ⥤ A₂) (H : B₁ ⥤ B₂) (δ : V₁ ⋙ G ≅ H ⋙ V₂)

private def adjointTransport : G ⋙ L₂ ⟶ L₁ ⋙ H where
  app M := (a₂.homEquiv _ _).symm
    (G.map (a₁.unit.app M) ≫ δ.hom.app (L₁.obj M))
  naturality {M N} f := by
    apply (a₂.homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [a₂.homEquiv_naturality_left, a₂.homEquiv_naturality_right]
    simp only [Functor.comp_obj, Equiv.apply_symm_apply]
    rw [← Category.assoc, ← G.map_comp,
      show f ≫ a₁.unit.app N = a₁.unit.app M ≫ V₁.map (L₁.map f) from
        a₁.unit.naturality f, G.map_comp,
      Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun z ↦ G.map (a₁.unit.app M) ≫ z) (δ.hom.naturality (L₁.map f))

private theorem adjointTransport_transpose (M : A₁) :
    a₂.homEquiv _ _ ((adjointTransport a₁ a₂ G H δ).app M) =
      G.map (a₁.unit.app M) ≫ δ.hom.app (L₁.obj M) :=
  (a₂.homEquiv _ _).apply_symm_apply _

private theorem isIso_of_precomp_on_image [H.EssSurj]
    {P Q : B₂} (f : P ⟶ Q)
    (hf : ∀ N : B₁, Function.Bijective (fun k : Q ⟶ H.obj N ↦ f ≫ k)) : IsIso f := by
  let e := H.objObjPreimageIso P
  obtain ⟨i, hi⟩ := (hf (H.objPreimage P)).2 e.inv
  let j := i ≫ e.hom
  have hj : f ≫ j = 𝟙 P := by simp [j, ← Category.assoc, hi]
  have hj' : j ≫ f = 𝟙 Q := by
    let e' := H.objObjPreimageIso Q
    apply (cancel_mono e'.inv).1
    apply (hf (H.objPreimage Q)).1
    simp only [← Category.assoc, hj, Category.id_comp]
  exact ⟨⟨j, hj, hj'⟩⟩

private theorem adjointTransport_isIso [G.Full] [G.Faithful]
    [H.Full] [H.Faithful] [H.EssSurj] :
    IsIso (adjointTransport a₁ a₂ G H δ) := by
  have hi (M : A₁) : IsIso ((adjointTransport a₁ a₂ G H δ).app M) := by
    apply isIso_of_precomp_on_image H
    intro N
    let E : (H.obj (L₁.obj M) ⟶ H.obj N) ≃
        (G.obj M ⟶ V₂.obj (H.obj N)) :=
      (Functor.FullyFaithful.ofFullyFaithful H).homEquiv.symm |>.trans (a₁.homEquiv M N) |>.trans
        (Functor.FullyFaithful.ofFullyFaithful G).homEquiv |>.trans
          (Iso.homCongr (Iso.refl _) (δ.app N))
    have he (k : H.obj (L₁.obj M) ⟶ H.obj N) :
        a₂.homEquiv _ _ ((adjointTransport a₁ a₂ G H δ).app M ≫ k) = E k := by
      obtain ⟨l, rfl⟩ := H.map_surjective k
      rw [a₂.homEquiv_naturality_right, adjointTransport_transpose]
      have hpre : (Functor.FullyFaithful.ofFullyFaithful H).homEquiv.symm
          (H.map l) = l := (Functor.FullyFaithful.ofFullyFaithful H).preimage_map l
      dsimp only [E, Equiv.trans_apply]
      rw [hpre]
      simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
      change (G.map (a₁.unit.app M) ≫ δ.hom.app (L₁.obj M)) ≫
        V₂.map (H.map l) = G.map (a₁.homEquiv _ _ l) ≫ δ.hom.app N
      have hn := δ.hom.naturality l
      dsimp only [Functor.comp_map] at hn
      rw [Category.assoc, ← hn, ← Category.assoc,
        ← G.map_comp, Adjunction.homEquiv_unit]
    constructor
    · intro k l hkl
      apply E.injective
      exact (he k).symm.trans ((congrArg (a₂.homEquiv _ _) hkl).trans (he l))
    · intro k
      obtain ⟨l, hl⟩ := E.surjective (a₂.homEquiv _ _ k)
      refine ⟨l, (a₂.homEquiv _ _).injective ?_⟩
      rw [he, hl]
  exact NatIso.isIso_of_isIso_app _

attribute [local irreducible] adjointTransport

end AdjointTransport

private def conjugatedMap {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (e : D ≅ E) (f : B ⟶ E) : A ⟶ D := a.hom ≫ f ≫ e.inv

private theorem conjugatedMap_square {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (e : D ≅ E) (f : B ⟶ E) :
    conjugatedMap a e f ≫ e.hom = a.hom ≫ f := by
  simp only [conjugatedMap, Category.assoc, e.inv_hom_id, Category.comp_id]

section ScalarAdjunctions

universe uC vC w
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R S T : Sheaf J CommRingCat.{w}}

set_option backward.isDefEq.respectTransparency false in
private theorem pure_smul (a : R ⟶ S) (M : CochainPullback.Modules.{w, uC, vC} R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    extensionTmul a M U s x = s • extensionTmul a M U 1 x := by
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf a M)).app U
  change η (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
    s • η ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)
  have ht : (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
      s • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) := by
    change s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
      (s * 1) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x
    rw [mul_one]
  exact (congrArg η ht).trans (η.hom.map_smul s _)

private theorem transpose_pure (a : R ⟶ S) (M : CochainPullback.Modules.{w, uC, vC} R)
    (N : CochainPullback.Modules.{w, uC, vC} S)
    (f : (extensionFunctor.{w, uC, vC} a).obj M ⟶ N) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    f.val.app U (extensionTmul a M U s x) =
      s • (show N.val.obj U from ((extensionAdjunction a).homEquiv M N f).val.app U x) := by
  rw [pure_smul, map_smul, Adjunction.homEquiv_unit]
  change _ = s • f.val.app U (((extensionAdjunction a).unit.app M).val.app U x)
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique a)).1 M U x
  change ((extensionAdjunction a).unit.app M).val.app U x = _ at hu
  rw [hu]

private def restrictionComp (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) :
    restrictionFunctor.{w, uC, vC, w} c ⋙ restrictionFunctor.{w, uC, vC, w} a ≅
      restrictionFunctor.{w, uC, vC, w} b :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (c.hom.app U).hom
        (b.hom.app U).hom (congrArg (fun f ↦ (f.hom.app U).hom) h)
        (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

private def extensionComp (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) :
    extensionFunctor.{w, uC, vC} a ⋙ extensionFunctor.{w, uC, vC} c ≅
      extensionFunctor.{w, uC, vC} b :=
  Adjunction.leftAdjointUniq
    (((extensionAdjunction a).comp (extensionAdjunction c)).ofNatIsoRight
      (restrictionComp a c b h)) (extensionAdjunction b)

private theorem extensionComp_pure (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) (M : CochainPullback.Modules.{w, uC, vC} R) (U : Cᵒᵖ)
    (z : T.obj.obj U) (s : S.obj.obj U) (x : M.val.obj U) :
    ((extensionComp a c b h).hom.app M).val.app U
      (extensionTmul c ((extensionFunctor.{w, uC, vC} a).obj M) U z (extensionTmul a M U s x)) =
      extensionTmul b M U (z * c.hom.app U s) x := by
  let f := (extensionComp a c b h).hom.app M
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((extensionAdjunction a).comp (extensionAdjunction c)).ofNatIsoRight
      (restrictionComp a c b h)) (extensionAdjunction b) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  have hx := congrArg (fun k ↦ k.val.app U x) hh
  change (((extensionAdjunction a).homEquiv M _
    ((extensionAdjunction c).homEquiv _ _ f)).val.app U x) =
      ((extensionAdjunction b).unit.app M).val.app U x at hx
  change f.val.app U _ = _
  erw [transpose_pure c _ _ f U z (extensionTmul a M U s x)]
  erw [transpose_pure a M _ ((extensionAdjunction c).homEquiv _ _ f) U s x, hx]
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique b)).1 M U x
  change ((extensionAdjunction b).unit.app M).val.app U x = _ at hu
  rw [hu]
  change z • (c.hom.app U s • extensionTmul b M U 1 x) = _
  rw [pure_smul b M U (z * c.hom.app U s) x, mul_smul]

private def scalarArrow (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) :
    extensionFunctor.{w, uC, vC} a ⟶
      extensionFunctor.{w, uC, vC} b ⋙ restrictionFunctor.{w, uC, vC, w} c :=
  Functor.whiskerLeft (extensionFunctor.{w, uC, vC} a) (extensionAdjunction c).unit ≫
    Functor.whiskerRight (extensionComp a c b h).hom (restrictionFunctor.{w, uC, vC, w} c)

private theorem scalarArrow_pure (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) (M : CochainPullback.Modules.{w, uC, vC} R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    ((scalarArrow a c b h).app M).val.app U (extensionTmul a M U s x) =
      extensionTmul b M U (c.hom.app U s) x := by
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique c)).1
    ((extensionFunctor.{w, uC, vC} a).obj M) U (extensionTmul a M U s x)
  change ((extensionAdjunction c).unit.app _).val.app U _ = _ at hu
  change ((extensionComp a c b h).hom.app M).val.app U
    (((extensionAdjunction c).unit.app _).val.app U (extensionTmul a M U s x)) = _
  rw [hu]
  exact (extensionComp_pure a c b h M U 1 s x).trans (by rw [one_mul])

omit [EssentiallySmall.{w} C] in
private theorem restrictionComp_apply (a : R ⟶ S) (c : S ⟶ T) (b : R ⟶ T)
    (h : b = a ≫ c) (M : CochainPullback.Modules.{w, uC, vC} T) (U : Cᵒᵖ)
    (x : M.val.obj U) : ((restrictionComp a c b h).hom.app M).val.app U x = x := rfl

attribute [local irreducible] extensionComp scalarArrow restrictionComp

end ScalarAdjunctions



section SiteTransport

variable {RY SY : Coeff.{t, r} Y} {RX SX : Coeff.{t, r} X}

set_option backward.isDefEq.respectTransparency false in
private theorem sectionwiseModules_equivalence
    {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX)
    [IsIso c] : (isoSectionwiseModuleInverseImage g c).IsEquivalence := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max r (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, adj]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  exact EM.isEquivalence_functor

set_option backward.isDefEq.respectTransparency false in
private theorem inverseModules_isEquivalence
    (c : (inverseRing g).obj RY ≅ RX) :
    (inverseModules g c).IsEquivalence :=
  sectionwiseModules_equivalence.{t, r} g
    (RY := (forgetRing Y).obj RY) (RX := (forgetRing X).obj RX)
    ((forgetRing X).map c.hom)

private theorem inverse_square (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) :
    inv ((forgetRing X).map cR.hom) ≫
        ((proEtaleIsoPostcompose g).sheafPushforwardContinuous RingCat
          (ProEt.topology X) (ProEt.topology Y)).map ((forgetRing Y).map aY) =
      (forgetRing X).map aX ≫ inv ((forgetRing X).map cS.hom) := by
  have hh : cR.inv ≫ (inverseRing g).map aY = aX ≫ cS.inv := by
    apply (cR.inv_comp_eq).2
    rw [← Category.assoc, ← h]
    simp
  rw [← Functor.map_inv, ← Functor.map_inv]
  have hr : inv cR.hom = cR.inv := IsIso.inv_eq_of_hom_inv_id cR.hom_inv_id
  have hs : inv cS.hom = cS.inv := IsIso.inv_eq_of_hom_inv_id cS.hom_inv_id
  rw [hr, hs]
  ext U x
  have hx := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) hh)
  exact hx x

private theorem inverse_transport_section (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) (U : X.ProEt)
    (s : RX.obj.obj (op U)) :
    aY.hom.app (op ((proEtaleIsoPostcompose g).obj U))
        (@id (RY.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
          (cR.inv.hom.app (op U) s)) =
      cS.inv.hom.app (op U) (aX.hom.app (op U) s) := by
  have hh : cR.inv ≫ (inverseRing g).map aY = aX ≫ cS.inv := by
    apply (cR.inv_comp_eq).2
    rw [← Category.assoc, ← h]
    simp
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op U)) hh) s

set_option backward.isDefEq.respectTransparency false in
private def transportRestriction (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) :
    restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aY ⋙ inverseModules g cR ≅
      inverseModules g cS ⋙ restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aX :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
      (X₁ := (((restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aY) ⋙
        inverseModules g cR).obj M).val.obj U)
      (X₂ := ((inverseModules g cS ⋙
        restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} aX).obj M).val.obj U)
      { __ := AddEquiv.refl _
        map_smul' a x := by
          have he := inverse_square g aY aX cR cS h
          have hx := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) he) a
          exact congrArg
            (fun z ↦ z • (show M.val.obj
              (op ((proEtaleIsoPostcompose g).obj U.unop)) from x)) hx })
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private def transportIso (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX) :
    inverseModules g cR ⋙ extensionFunctor.{max r (t + 1), t + 1, t} aX ≅
      extensionFunctor.{max r (t + 1), t + 1, t} aY ⋙ inverseModules g cS := by
  have := inverseModules_isEquivalence g cR
  have := inverseModules_isEquivalence g cS
  let f := adjointTransport (extensionAdjunction aY) (extensionAdjunction aX)
    (inverseModules g cR) (inverseModules g cS) (transportRestriction g aY aX cR cS h)
  have : IsIso f := adjointTransport_isIso _ _ _ _ _
  exact asIso f

set_option backward.isDefEq.respectTransparency false in
private theorem transportIso_pure (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (inverseRing g).obj RY ≅ RX) (cS : (inverseRing g).obj SY ≅ SX)
    (h : (inverseRing g).map aY ≫ cS.hom = cR.hom ≫ aX)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY) (U : X.ProEt)
    (s : SX.obj.obj (op U))
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((transportIso g aY aX cR cS h).hom.app M).val.app (op U)
      (pure X aX ((inverseModules g cR).obj M) (op U) s x) =
      pure Y aY M (op ((proEtaleIsoPostcompose g).obj U))
        (@id (SY.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
          (cS.inv.hom.app (op U) s)) x := by
  refine (transpose_pure aX ((inverseModules g cR).obj M) _
    ((transportIso g aY aX cR cS h).hom.app M) (op U) s x).trans ?_
  have hh := adjointTransport_transpose (extensionAdjunction aY) (extensionAdjunction aX)
    (inverseModules g cR) (inverseModules g cS) (transportRestriction g aY aX cR cS h) M
  have hx := congrArg (fun f ↦ f.val.app (op U) x) hh
  change (((extensionAdjunction aX).homEquiv _ _
    ((transportIso g aY aX cR cS h).hom.app M)).val.app (op U) x) =
      ((extensionAdjunction aY).unit.app M).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) x at hx
  erw [hx]
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique aY)).1 M
    (op ((proEtaleIsoPostcompose g).obj U)) x
  change ((extensionAdjunction aY).unit.app M).val.app _ x = _ at hu
  rw [hu]
  change (inv ((forgetRing X).map cS.hom)).hom.app (op U) s •
      (show ((extensionFunctor.{max r (t + 1), t + 1, t} aY).obj M).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)) from
        pure Y aY M (op ((proEtaleIsoPostcompose g).obj U)) 1 x) = _
  rw [← Functor.map_inv]
  rw [show inv cS.hom = cS.inv from IsIso.inv_eq_of_hom_inv_id cS.hom_inv_id]
  exact (pure_smul aY M (op ((proEtaleIsoPostcompose g).obj U))
    (cS.inv.hom.app (op U) s) x).symm

attribute [local irreducible] transportIso transportRestriction

end SiteTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def finiteModuleIso (n : ℕ) :
    extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n) ⋙ inverseModules g (d.cA n) ⋙
        extensionFunctor.{max r (t + 1), t + 1, t} (DX.i n) ≅
      extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙ inverseModules g (d.cB n) :=
  Functor.isoWhiskerLeft (extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n))
      (transportIso g (DY.i n) (DX.i n) (d.cA n) (d.cB n) (d.i_comm n)) ≪≫
    Functor.isoWhiskerRight
      (extensionComp (DY.piA n) (DY.i n) (DY.j ≫ DY.piB n) (DY.projection_i n))
      (inverseModules g (d.cB n))

attribute [local irreducible] finiteModuleIso

private def finiteIso (n : ℕ) : finiteLeft g d n ≅ finiteRight g d n :=
  NatIso.mapHomologicalComplex (finiteModuleIso g d n) (.up ℤ)

private theorem finiteIso_hom_component (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) :
    ((finiteIso g d n).hom.app P).f k = (finiteModuleIso g d n).hom.app (P.X k) := rfl

private theorem finiteIso_hom_pure (n : ℕ) (P : moduleComplex Y DY.R)
    (k : ℤ) (U : X.ProEt)
    (a : (DY.A n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : (DX.B n).obj.obj (op U))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((finiteIso g d n).hom.app P).f k).val.app (op U)
        (doublePure g d n P k U a s p) =
      finitePure g d n P k U
        ((DY.i n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a *
          (@id ((DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
            ((d.cB n).inv.hom.app (op U) s))) p := by
  rw [finiteIso_hom_component]
  unfold finiteModuleIso
  change ((extensionComp (DY.piA n) (DY.i n) (DY.j ≫ DY.piB n)
      (DY.projection_i n)).hom.app (P.X k)).val.app
      (op ((proEtaleIsoPostcompose g).obj U))
      (((transportIso g (DY.i n) (DX.i n) (d.cA n) (d.cB n) (d.i_comm n)).hom.app
        ((extensionFunctor.{max r (t + 1), t + 1, t} (DY.piA n)).obj (P.X k))).val.app (op U)
        (pure X (DX.i n) _ (op U) s
          (pure Y (DY.piA n) (P.X k) (op ((proEtaleIsoPostcompose g).obj U)) a p))) = _
  rw [transportIso_pure]
  refine (extensionComp_pure (DY.piA n) (DY.i n) (DY.j ≫ DY.piB n)
    (DY.projection_i n) (P.X k) (op ((proEtaleIsoPostcompose g).obj U))
    ((d.cB n).inv.hom.app (op U) s) a p).trans ?_
  exact congrArg (fun z ↦ pure Y (DY.j ≫ DY.piB n) (P.X k)
    (op ((proEtaleIsoPostcompose g).obj U)) z p) (mul_comm _ _)

attribute [local irreducible] finiteIso

private theorem finiteIso_inv_pure (n : ℕ) (P : moduleComplex Y DY.R)
    (k : ℤ) (U : X.ProEt)
    (s : (DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((finiteIso g d n).inv.app P).f k).val.app (op U)
        (finitePure g d n P k U s p) =
      doublePure g d n P k U 1 ((d.cB n).hom.hom.app (op U) s) p := by
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op U)) (d.cB n).hom_inv_id) s
  change (d.cB n).inv.hom.app (op U) ((d.cB n).hom.hom.app (op U) s) = s at hc
  have hh := finiteIso_hom_pure g d n P k U 1 ((d.cB n).hom.hom.app (op U) s) p
  rw [map_one, one_mul, hc] at hh
  have hi := congrArg (fun f ↦ (f.f k).val.app (op U)
    (doublePure g d n P k U 1 ((d.cB n).hom.hom.app (op U) s) p))
    ((finiteIso g d n).hom_inv_id_app P)
  exact (congrArg ((((finiteIso g d n).inv.app P).f k).val.app (op U)) hh).symm.trans hi

private def rightModuleArrow {RY SY TY : Coeff.{t, r} Y} {SX TX : Coeff.{t, r} X}
    (a : RY ⟶ SY) (c : SY ⟶ TY) (b : RY ⟶ TY) (h : b = a ≫ c)
    (cS : (inverseRing g).obj SY ≅ SX) (cT : (inverseRing g).obj TY ≅ TX)
    (cX : SX ⟶ TX) (hc : (inverseRing g).map c ≫ cT.hom = cS.hom ≫ cX) :
    extensionFunctor.{max r (t + 1), t + 1, t} a ⋙ inverseModules g cS ⟶
      extensionFunctor.{max r (t + 1), t + 1, t} b ⋙ inverseModules g cT ⋙
        restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} cX :=
  Functor.whiskerRight (scalarArrow a c b h) (inverseModules g cS) ≫
    Functor.whiskerLeft (extensionFunctor.{max r (t + 1), t + 1, t} b)
      (transportRestriction g c cX cS cT hc).hom

private theorem rightModuleArrow_pure
    {RY SY TY : Coeff.{t, r} Y} {SX TX : Coeff.{t, r} X}
    (a : RY ⟶ SY) (c : SY ⟶ TY) (b : RY ⟶ TY) (h : b = a ≫ c)
    (cS : (inverseRing g).obj SY ≅ SX) (cT : (inverseRing g).obj TY ≅ TX)
    (cX : SX ⟶ TX) (hc : (inverseRing g).map c ≫ cT.hom = cS.hom ≫ cX)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY) (U : X.ProEt)
    (s : SY.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((rightModuleArrow g a c b h cS cT cX hc).app M).val.app (op U)
      (pure Y a M (op ((proEtaleIsoPostcompose g).obj U)) s x) =
        pure Y b M (op ((proEtaleIsoPostcompose g).obj U))
          (c.hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) x :=
  by
    unfold rightModuleArrow transportRestriction
    exact scalarArrow_pure a c b h M (op ((proEtaleIsoPostcompose g).obj U)) s x


private def liftRestrictedArrow
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ C) (G : A ⥤ B) (R : B ⥤ C)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    (a : F ⟶ G ⋙ R) :
    F.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex a (.up ℤ)

private def liftRestrictedTransition
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (R : B ⥤ D) (G : A ⥤ C) (S : C ⥤ D)
    [F.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] [S.PreservesZeroMorphisms]
    (a : F ⋙ R ⟶ G ⋙ S) :
    F.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex a (.up ℤ)

private def quotientRight (n : ℕ) : right g d ⟶ restrictedRight g d n :=
  liftRestrictedArrow
    (extensionFunctor.{max r (t + 1), t + 1, t} DY.j ⋙ inverseModules g d.cS)
    (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙
      inverseModules g (d.cB n))
    (restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB n))
    (rightModuleArrow g DY.j (DY.piB n) (DY.j ≫ DY.piB n) rfl
      d.cS (d.cB n) (DX.piB n) (d.piB_comm n))

private theorem transition_composite (n : ℕ) :
    DY.j ≫ DY.piB n = (DY.j ≫ DY.piB (Nat.succ n)) ≫ DY.qB n := by
  rw [Category.assoc, DY.projection_B n]

private def restrictedArrow
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (L : A ⥤ B) (M : B ⥤ C) (N : C ⥤ F)
    (L' : A ⥤ D) (M' : D ⥤ E) (N' : E ⥤ F) (K : E ⥤ C)
    (a : L ⋙ M ⟶ L' ⋙ M' ⋙ K) (e : K ⋙ N ≅ N') :
    L ⋙ M ⋙ N ⟶ L' ⋙ M' ⋙ N' :=
  Functor.whiskerRight a N ≫ Functor.whiskerLeft (L' ⋙ M') e.hom

private def transitionModuleRight (n : ℕ) :
    extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB (Nat.succ n)) ⋙
        inverseModules g (d.cB (Nat.succ n)) ⋙
          restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB (Nat.succ n)) ⟶
      extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙
        inverseModules g (d.cB n) ⋙
          restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB n) :=
  restrictedArrow
    (A := CochainPullback.Modules.{max r (t + 1), t + 1, t} DY.R)
    (B := CochainPullback.Modules.{max r (t + 1), t + 1, t} (DY.B (Nat.succ n)))
    (C := CochainPullback.Modules.{max r (t + 1), t + 1, t} (DX.B (Nat.succ n)))
    (D := CochainPullback.Modules.{max r (t + 1), t + 1, t} (DY.B n))
    (E := CochainPullback.Modules.{max r (t + 1), t + 1, t} (DX.B n))
    (F := CochainPullback.Modules.{max r (t + 1), t + 1, t} DX.S)
    (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB (Nat.succ n)))
    (inverseModules g (d.cB (Nat.succ n)))
    (restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB (Nat.succ n)))
    (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n))
    (inverseModules g (d.cB n))
    (restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB n))
    (restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.qB n))
    (rightModuleArrow g (DY.j ≫ DY.piB (Nat.succ n)) (DY.qB n) (DY.j ≫ DY.piB n)
      (transition_composite (DY := DY) n) (d.cB (Nat.succ n)) (d.cB n)
      (DX.qB n) (d.qB_comm n))
    (restrictionComp.{t + 1, t, max r (t + 1)}
      (C := X.ProEt) (J := ProEt.topology X)
      (R := DX.S) (S := DX.B (Nat.succ n)) (T := DX.B n)
      (DX.piB (Nat.succ n)) (DX.qB n) (DX.piB n) (DX.projection_B n).symm)

attribute [local irreducible] transitionModuleRight

private def transitionRight (n : ℕ) : restrictedRight g d (Nat.succ n) ⟶
    restrictedRight g d n :=
  liftRestrictedTransition
    (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB (Nat.succ n)) ⋙
      inverseModules g (d.cB (Nat.succ n)))
    (restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB (Nat.succ n)))
    (extensionFunctor.{max r (t + 1), t + 1, t} (DY.j ≫ DY.piB n) ⋙
      inverseModules g (d.cB n))
    (restrictionFunctor.{max r (t + 1), t + 1, t, max r (t + 1)} (DX.piB n))
    (transitionModuleRight g d n)

private theorem quotientRight_component (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) :
    ((quotientRight g d n).app P).f k =
      (rightModuleArrow g DY.j (DY.piB n) (DY.j ≫ DY.piB n) rfl
        d.cS (d.cB n) (DX.piB n) (d.piB_comm n)).app (P.X k) := rfl

private theorem transitionRight_component (n : ℕ) (P : moduleComplex Y DY.R) (k : ℤ) :
    ((transitionRight g d n).app P).f k =
      (transitionModuleRight g d n).app (P.X k) := rfl

attribute [local irreducible] quotientRight transitionRight
attribute [local irreducible] finitePure rightPure

private theorem quotientRight_pure (n : ℕ) (P : moduleComplex Y DY.R)
    (k : ℤ) (U : X.ProEt)
    (s : DY.S.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((quotientRight g d n).app P).f k).val.app (op U) (rightPure g d P k U s p) =
      finitePure g d n P k U
        ((DY.piB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p := by
  rw [quotientRight_component]
  unfold rightPure finitePure
  exact rightModuleArrow_pure g DY.j (DY.piB n) (DY.j ≫ DY.piB n) rfl
    d.cS (d.cB n) (DX.piB n) (d.piB_comm n) (P.X k) U s p

private theorem transitionModuleRight_pure (n : ℕ)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} DY.R) (U : X.ProEt)
    (s : (DY.B (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((transitionModuleRight g d n).app M).val.app (op U)
      (pure Y (DY.j ≫ DY.piB (Nat.succ n)) M
        (op ((proEtaleIsoPostcompose g).obj U)) s p) =
      pure Y (DY.j ≫ DY.piB n) M (op ((proEtaleIsoPostcompose g).obj U))
        ((DY.qB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p := by
  unfold transitionModuleRight restrictedArrow
  change ((restrictionComp (DX.piB (Nat.succ n)) (DX.qB n) (DX.piB n)
      (DX.projection_B n).symm).hom.app
        ((inverseModules g (d.cB n)).obj
          ((extensionFunctor.{max r (t + 1), t + 1, t}
            (DY.j ≫ DY.piB n)).obj M))).val.app (op U)
      (((rightModuleArrow g (DY.j ≫ DY.piB (Nat.succ n)) (DY.qB n) (DY.j ≫ DY.piB n)
        (transition_composite (DY := DY) n) (d.cB (Nat.succ n)) (d.cB n)
        (DX.qB n) (d.qB_comm n)).app M).val.app (op U)
        (pure Y (DY.j ≫ DY.piB (Nat.succ n)) M
          (op ((proEtaleIsoPostcompose g).obj U)) s p)) = _
  refine (restrictionComp_apply (DX.piB (Nat.succ n)) (DX.qB n) (DX.piB n)
    (DX.projection_B n).symm
    ((inverseModules g (d.cB n)).obj
      ((extensionFunctor.{max r (t + 1), t + 1, t}
        (DY.j ≫ DY.piB n)).obj M)) (op U) _).trans ?_
  exact rightModuleArrow_pure g (DY.j ≫ DY.piB (Nat.succ n)) (DY.qB n) (DY.j ≫ DY.piB n)
    (transition_composite (DY := DY) n) (d.cB (Nat.succ n)) (d.cB n)
    (DX.qB n) (d.qB_comm n) M U s p

private theorem transitionRight_pure (n : ℕ) (P : moduleComplex Y DY.R)
    (k : ℤ) (U : X.ProEt)
    (s : (DY.B (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (p : (P.X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((transitionRight g d n).app P).f k).val.app (op U)
        (finitePure g d (Nat.succ n) P k U s p) =
      finitePure g d n P k U
        ((DY.qB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) s) p := by
  rw [transitionRight_component]
  unfold finitePure
  exact transitionModuleRight_pure g d n (P.X k) U s p

attribute [local irreducible] rightModuleArrow

attribute [local irreducible] doublePure leftPure

private def quotientLeft (b : left g d ≅ right g d) (n : ℕ) :
    left g d ⟶ restrictedLeft g d n :=
  conjugatedMap b
    (Functor.isoWhiskerRight (finiteIso g d n)
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n))) (quotientRight g d n)

private def transitionLeft (n : ℕ) :
    restrictedLeft g d (Nat.succ n) ⟶ restrictedLeft g d n :=
  conjugatedMap
    (Functor.isoWhiskerRight (finiteIso g d (Nat.succ n))
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB (Nat.succ n))))
    (Functor.isoWhiskerRight (finiteIso g d n)
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n))) (transitionRight g d n)

private theorem quotientFormulas_proof (b : left g d ≅ right g d)
    (hb : UpperFormula g d b) :
    QuotientFormulas g d (quotientLeft g d b) (quotientRight g d) := by
  refine ⟨?_, quotientRight_pure g d⟩
  intro n P k U s p
  let sY := d.cS.inv.hom.app (op U) s
  have hs : d.cS.hom.hom.app (op U) sY = s :=
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op U)) d.cS.inv_hom_id) s
  change (((finiteIso g d n).inv.app P).f k).val.app (op U)
    ((((quotientRight g d n).app P).f k).val.app (op U)
      (((b.hom.app P).f k).val.app (op U) (leftPure g d P k U s p))) = _
  rw [← hs, hb]
  rw [quotientRight_pure, finiteIso_inv_pure]
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op U)) (d.piB_comm n)) sY
  change (d.cB n).hom.hom.app (op U)
    ((DY.piB n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) sY) =
      (DX.piB n).hom.app (op U) (d.cS.hom.hom.app (op U) sY) at hc
  rw [hc]

private theorem transitionFormulas_proof :
    TransitionFormulas g d (transitionLeft g d) (transitionRight g d) := by
  refine ⟨?_, transitionRight_pure g d⟩
  intro n P k U a s p
  change (((finiteIso g d n).inv.app P).f k).val.app (op U)
    ((((transitionRight g d n).app P).f k).val.app (op U)
      ((((finiteIso g d (Nat.succ n)).hom.app P).f k).val.app (op U)
        (doublePure g d (Nat.succ n) P k U a s p))) = _
  rw [finiteIso_hom_pure]
  rw [transitionRight_pure]
  have he : (DY.qB n).hom.app (op ((proEtaleIsoPostcompose g).obj U))
      ((DY.i (Nat.succ n)).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a *
        (@id ((DY.B (Nat.succ n)).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
          ((d.cB (Nat.succ n)).inv.hom.app (op U) s))) =
      (DY.i n).hom.app (op ((proEtaleIsoPostcompose g).obj U))
        ((DY.qA n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a) *
          (@id ((DY.B n).obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
            ((d.cB n).inv.hom.app (op U) ((DX.qB n).hom.app (op U) s))) := by
    rw [map_mul]
    congr 1
    · exact ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.hom.app (op ((proEtaleIsoPostcompose g).obj U)))
          (DY.transition_i n)) a
    · exact inverse_transport_section g (DY.qB n) (DX.qB n)
        (d.cB (Nat.succ n)) (d.cB n) (d.qB_comm n) U s
  rw [he]
  have hh := finiteIso_hom_pure g d n P k U
    ((DY.qA n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a)
    ((DX.qB n).hom.app (op U) s) p
  have hi := congrArg (fun f ↦ (f.f k).val.app (op U)
    (doublePure g d n P k U
      ((DY.qA n).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a)
      ((DX.qB n).hom.app (op U) s) p)) ((finiteIso g d n).hom_inv_id_app P)
  exact (congrArg ((((finiteIso g d n).inv.app P).f k).val.app (op U)) hh).symm.trans hi

private theorem quotientLeft_square (b : left g d ≅ right g d) (n : ℕ) :
    quotientLeft g d b n ≫ Functor.whiskerRight (finiteIso g d n).hom
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)) =
        b.hom ≫ quotientRight g d n :=
  conjugatedMap_square b
    (Functor.isoWhiskerRight (finiteIso g d n)
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n))) (quotientRight g d n)

private theorem transitionLeft_square (n : ℕ) :
    transitionLeft g d n ≫ Functor.whiskerRight (finiteIso g d n).hom
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)) =
        Functor.whiskerRight (finiteIso g d (Nat.succ n)).hom
          (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB (Nat.succ n))) ≫
            transitionRight g d n :=
  conjugatedMap_square
    (Functor.isoWhiskerRight (finiteIso g d (Nat.succ n))
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB (Nat.succ n))))
    (Functor.isoWhiskerRight (finiteIso g d n)
      (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n))) (transitionRight g d n)

attribute [local irreducible] quotientLeft transitionLeft

/-- Natural finite balanced isomorphisms, with coefficient and transition chain squares.
Source: Stacks Project, sites-modules.tex, Tag 03EK, section-tensor-product;
agent balanced reassociation and coefficient calculation
(blueprint: lem-weil-isomorphism-scalar-quotient-chain-squares).

Proof:
1. Scalar extension is the normalized left adjoint to scalar restriction. Composing
adjunctions and identifying composite scalar restrictions gives the canonical
reassociation isomorphism; its rule is z tensor (a tensor p) mapped to z*i(a) tensor p.
2. The corresponding-object inverse-image functor on modules is an equivalence.
Its scalar restriction square commutes by the coefficient compatibility. Transposing
this square along the normalized extension adjunctions gives the scalar transport
isomorphism, whose rule transports a scalar through the inverse coefficient isomorphism.
The mate is invertible because the two vertical module functors are equivalences.
3. Compose scalar transport with reassociation to obtain the finite comparisons.
Their forward formula follows from the two normalized adjunction units; applying the
inverse to the forward formula with inner coefficient 1 proves the inverse formula.
4. Transpose the scalar-extension unit to construct the right coefficient map. The
restriction square transports it to X. Define the left coefficient map by conjugating
with the given upper comparison and the finite comparison. The upper normalization
and the coefficient square give its required formula; cancellation gives the square.
5. Apply the same construction to qB and identify the two scalar restrictions using
the tower projection identity. Conjugate by the finite comparisons to define the left
transition. Its formula follows from qB*i = i*qA and compatibility of cB with qB.
Cancellation gives the transition square.
6. Lift all module functors, natural transformations and isomorphisms termwise to
unbounded cochain complexes. Naturality supplies differential compatibility and chain-map
naturality. These constructions use only adjunctions and coefficient identities, so zero
rings, zero complexes, nonflat maps and nonsurjective transitions are included. -/
theorem scalar_quotient_chain_squares (b : left g d ≅ right g d)
    (hb : UpperFormula g d b) :
    ∃ (bfin : ∀ n : ℕ, finiteLeft g d n ≅ finiteRight g d n)
      (v : ∀ n : ℕ, left g d ⟶ restrictedLeft g d n)
      (w : ∀ n : ℕ, right g d ⟶ restrictedRight g d n)
      (vtrans : ∀ n : ℕ, restrictedLeft g d (Nat.succ n) ⟶ restrictedLeft g d n)
      (wtrans : ∀ n : ℕ, restrictedRight g d (Nat.succ n) ⟶ restrictedRight g d n),
      FiniteFormulas g d bfin ∧ QuotientFormulas g d v w ∧
      TransitionFormulas g d vtrans wtrans ∧
      (∀ n : ℕ,
        v n ≫ Functor.whiskerRight (bfin n).hom
          (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)) =
          b.hom ≫ w n) ∧
      (∀ n : ℕ,
        vtrans n ≫ Functor.whiskerRight (bfin n).hom
          (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB n)) =
          Functor.whiskerRight (bfin (Nat.succ n)).hom
            (scalarRestrict.{t, r, max r (t + 1)} X (DX.piB (Nat.succ n))) ≫ wtrans n) := by
  exact ⟨finiteIso g d, quotientLeft g d b, quotientRight g d,
    transitionLeft g d, transitionRight g d,
    ⟨finiteIso_hom_pure g d, finiteIso_inv_pure g d⟩,
    quotientFormulas_proof g d b hb,
    transitionFormulas_proof g d,
    quotientLeft_square g d b, transitionLeft_square g d⟩

end AlgebraicGeometry.ProEtale.ScalarQuotientChain
