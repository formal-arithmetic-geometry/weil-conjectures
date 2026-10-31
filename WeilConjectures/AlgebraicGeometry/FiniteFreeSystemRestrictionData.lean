/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

public import WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites

/-! # Finite-free coefficient restriction on entire derived systems

Source: finite-free coefficient tensor in the blueprint coefficient comparison;
Stacks 07A6, 03DI, 03DJ and 0F7B--0F7F
(blueprint: lem-coef-finite-free-system-restriction).

Natural transformations below live on the ordinary unbounded derived categories
of strict semilinear systems, before evaluation and inverse limit.
The data are recorded by (blueprint: def-coef-finite-free-system-data).
Index n means positive exponent n+1. The upper coefficients are S/pi^(n+1)S,
including ramification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
open WeilConjectures.SemilinearSections
namespace WeilConjectures.FiniteFreeSystemRestriction

universe v w

/-- Componentwise scalar comparison for a compactification.
Source: formal proper/open pasting in proof Step 13
(blueprint: def-coef-finite-free-system-data). -/
def compactScalarIso {XB WB YB XA WA YA : Type v}
    [Category.{w} XB] [Category.{w} WB] [Category.{w} YB]
    [Category.{w} XA] [Category.{w} WA] [Category.{w} YA]
    (Ux : XB ⥤ XA) (Uw : WB ⥤ WA) (Uy : YB ⥤ YA)
    (Jb : XB ⥤ WB) (Rb : WB ⥤ YB) (Ja : XA ⥤ WA) (Ra : WA ⥤ YA)
    (cj : Jb ⋙ Uw ≅ Ux ⋙ Ja) (cp : Rb ⋙ Uy ≅ Uw ⋙ Ra) :
    (Jb ⋙ Rb) ⋙ Uy ≅ Ux ⋙ (Ja ⋙ Ra) :=
  NatIso.ofComponents (fun M ↦ cp.app (Jb.obj M) ≪≫ Ra.mapIso (cj.app M)) (by
    intro M N f
    have hp := cp.hom.naturality (Jb.map f)
    have hj := cj.hom.naturality f
    dsimp only [Functor.comp_map] at hp hj
    dsimp only [Functor.comp_map, Functor.comp_obj, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc]
    rw [reassoc_of% hp, ← Functor.map_comp, hj, Functor.map_comp])

/-- The component word formed from a right mate and two compositors.
Source: formal compactification word in proof Step 13
(blueprint: def-coef-finite-free-system-data). -/
def compactWord {X V W S T Z : Type v}
    [Category.{w} X] [Category.{w} V] [Category.{w} W]
    [Category.{w} S] [Category.{w} T] [Category.{w} Z]
    (Jj : X ⥤ V) (Jk : V ⥤ W) (Ja : S ⥤ T) (Jjk : X ⥤ W)
    (Rr : V ⥤ S) (Rp : W ⥤ T) (Rq : T ⥤ Z) (Rpq : W ⥤ Z)
    (gamma : Rr ⋙ Ja ⟶ Jk ⋙ Rp) (jc : Jj ⋙ Jk ≅ Jjk) (sc : Rp ⋙ Rq ≅ Rpq) :
    (Jj ⋙ Rr) ⋙ (Ja ⋙ Rq) ⟶ Jjk ⋙ Rpq where
  app M := Rq.map (gamma.app (Jj.obj M)) ≫
    Rq.map (Rp.map (jc.hom.app M)) ≫ sc.hom.app (Jjk.obj M)
  naturality M N f := by
    have hg := congrArg Rq.map (gamma.naturality (Jj.map f))
    have hj := congrArg (fun z ↦ Rq.map (Rp.map z)) (jc.hom.naturality f)
    have hs := sc.hom.naturality (Jjk.map f)
    dsimp only [Functor.comp_map] at hg hj hs
    simp only [Functor.map_comp] at hg hj
    dsimp only [Functor.comp_map, Functor.comp_obj]
    rw [reassoc_of% hg, reassoc_of% hj, hs]
    simp only [Category.assoc]

/-- Quotient by the indicated uniformizer power, with its actual exponent.
Source: the coefficient quotient in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev quotient (R : Type (u + 1)) [CommRing R] (pi : R) (n : ℕ) :=
  R ⧸ (Ideal.span {pi}) ^ (n + 1)

/-- The quotient transition is induced by the identity of the integer ring.
Source: the coefficient quotient in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def quotientTransition (R : Type (u + 1)) [CommRing R] (pi : R) (n : ℕ) :
    quotient R pi (n + 1) →+* quotient R pi n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- Inclusion followed by quotient, with the source uniformizer on both sides.
Source: the compatible coefficient inclusion in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def quotientMap {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (pi : R) (n : ℕ) :
    quotient R pi n →+* quotient S (f pi) n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp f) (by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    simpa only [map_pow] using map_dvd f hx)

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

/-- Lower coefficient ring at positive exponent n+1.
Source: the A tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev A (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))

/-- Upper coefficient ring, using the image of the lower uniformizer.
Source: the B tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev B (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (quotient (Padic.coefficientExtensionIntegers l L)
    (integralScalarIntegerInclusion l E L i (Padic.coefficientExtensionUniformizer l E)) n)

/-- Actual lower quotient transitions.
Source: the A tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev aTransition (n : ℕ) : A l E (n + 1) ⟶ A l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1))

/-- Actual upper quotient transitions, retaining all ramified levels en.
Source: the B tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev bTransition (n : ℕ) : B l E L i (n + 1) ⟶ B l E L i n :=
  CommRingCat.ofHom (quotientTransition _ _ n)

/-- The specified compatible inclusion at each positive coefficient level.
Source: the A-to-B map in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev levelMap (n : ℕ) : A l E n ⟶ B l E L i n :=
  CommRingCat.ofHom (quotientMap (integralScalarIntegerInclusion l E L i)
    (Padic.coefficientExtensionUniformizer l E) n)


/-- The specified level maps commute with the actual quotient transitions.
Source: coefficient inclusion in the node
(blueprint: lem-coef-finite-free-system-restriction).
Proof: quotient induction reduces both composites to x mapped to the residue of i(x).
Ring-homomorphism extensionality then gives their equality. -/
theorem levelMap_transition (n : ℕ) :
    levelMap l E L i (n + 1) ≫ bTransition l E L i n =
      aTransition l E n ≫ levelMap l E L i n := by
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

/-- The level map on constant ring sheaves.
Source: sectionwise coefficient inclusion in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev sheafMap (X : Scheme.{u}) (n : ℕ) :
    coefficients (A l E) X n ⟶ coefficients (B l E L i) X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (levelMap l E L i n)

/-- The coefficient map on the single ringed sequence site, retaining all transitions.
Source: proof Step 1 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def systemInclusion (X : Scheme.{u}) :
    ringSystem (A l E) (aTransition l E) X ⟶
      ringSystem (B l E L i) (bTransition l E L i) X :=
  systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients (A l E) X) (transition (A l E) (aTransition l E) X)
    (coefficients (B l E L i) X) (transition (B l E L i) (bTransition l E L i) X)
    (sheafMap l E L i X) (fun n ↦ by
      simpa only [sheafMap, AlgebraicGeometry.ProEtale.SemilinearProperOpen.transition,
        ← Functor.map_comp] using
        congrArg ((constantSheaf.{u, u + 1, u + 1, u + 2}
          (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map)
          (levelMap_transition l E L i n))

/-- Ordinary termwise restriction along the actual coefficient-system map.
Source: proof Step 1 of the node, using the dependency's restriction functor
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev U0 (X : Scheme.{u}) := res.{u + 1, u, u + 1} (systemInclusion l E L i X)

/-- Derived restriction, computed by termwise localization.
Source: proof Step 5 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
@[reducible] def U (X : Scheme.{u}) :
    Derived (B l E L i) (bTransition l E L i) X ⥤
      Derived (A l E) (aTransition l E) X :=
  resD.{u + 1, u, u + 1} (systemInclusion l E L i X)

/-- The upper coefficient system considered as an ordinary lower-coefficient system.
Source: the coefficient system B in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev coefficientModule (X : Scheme.{u}) :=
  (U0 l E L i X).obj (SheafOfModules.unit
    (ring.{u + 1, u, u + 1} (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology X))
      (ringSystem (B l E L i) (bTransition l E L i) X)))

/-- The upper coefficient system in degree zero, with the restricted action.
Source: the normalized coefficient system in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev coefficientObject (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (Modules (A l E) (aTransition l E) X) 0).obj
    (coefficientModule l E L i X)

/-- Restrict a module over a sheafified constant commutative ring along its constant
section map. This is coefficient transport into the dependency's fixed-ring predicates.
Source: Stacks 03CY, canonical constant scalar action
(blueprint: lem-coef-finite-free-system-restriction). -/
def fixedModule (X : Scheme.{u}) (C : CommRingCat.{u + 1})
    (M : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      ((constantSheaf.{u, u + 1, u + 1, u + 2}
        (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj C)) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C) :=
  let P := (PresheafOfModules.restrictScalars.{u + 1}
    (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj C))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj M.val
  ⟨{ obj := P.obj
     map := fun f ↦ P.map f
     map_id := fun V ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id V)
     map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x },
    Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology X) _
      (forget₂ (ModuleCat.{u + 1} C) AddCommGrpCat.{u + 1}) M.isSheaf⟩

/-- The finite-type separated k-schemes occurring in this statement, using the
standard bundled category of schemes over the field and the existing properties.
Source: geometric hypotheses of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev Spaces (D : FiniteFieldDatum.{u}) :=
  { X : Over (Spec (CommRingCat.of D.k)) //
    IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom }

/-- All scalar assertions on one whole-system category. The stored derived scalar
model and adjunction are the dependency's normalized ones, including x mapped to
1 tensor x and its derived transpose formula.
Source: coefficient normalization and exact adjunction clauses of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
structure ScalarAssertions (X : Scheme.{u}) where
  /-- The actual lower system calculus supplies its canonical reduction maps. -/
  lower : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients (A l E) X) (transition (A l E) (aTransition l E) X)
  /-- The actual upper system calculus, for normalized constructible inputs. -/
  upper : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients (B l E L i) X) (transition (B l E L i) (bTransition l E L i) X)
  /-- The canonical normalized scalar extension and scalar adjunction. -/
  scalar : ScalarData.{u + 1, u, u + 1} (systemInclusion l E L i X)
  /-- Ordinary extension is exact. Restriction is the exact published res. -/
  extension_exact : PreservesFiniteLimits scalar.model.E ∧
    PreservesFiniteColimits scalar.model.E
  /-- Termwise localization computes the derived scalar extension on every complex. -/
  extension_computes : ∀ K : CochainComplex (Modules (A l E) (aTransition l E) X) ℤ,
    IsIso (scalar.model.ε.app K)
  /-- Restriction preserves K-injectivity on the entire sequence site. -/
  restriction_kInjective : ∀ K : CochainComplex
    (Modules (B l E L i) (bTransition l E L i) X) ℤ,
    K.IsKInjective → CochainComplex.IsKInjective
      (((U0 l E L i X).mapHomologicalComplex (.up ℤ)).obj K)
  /-- The canonical transition adjuncts B_m tensor A_n to B_n are invertible. -/
  normalized : Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients (A l E) X)
    (transition (A l E) (aTransition l E) X) lower.scalar (coefficientObject l E L i X)
  /-- Each coefficient level is constructible, in the recorded fixed-ring encoding. -/
  constructible : ∀ n : ℕ, AlgebraicGeometry.ProEtale.IsConstructible (A l E n)
    (fixedModule X (A l E n)
      ((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients (A l E) X)
        (transition (A l E) (aTransition l E) X) n).obj (coefficientModule l E L i X)))
  /-- Each coefficient level has Tor amplitude exactly contained in [0,0]. -/
  torAmplitude : ∀ n : ℕ,
    AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (A l E n)) X
      0 0 ((DerivedCategory.singleFunctor _ 0).obj
        (fixedModule X (A l E n)
          ((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients (A l E) X)
            (transition (A l E) (aTransition l E) X) n).obj (coefficientModule l E L i X))))


/-- The section-normalized ordinary inverse-image/direct-image scalar square.
Source: proof Step 6 of the node; the mate equation includes both geometric
adjunction unit and counit compatibilities
(blueprint: lem-coef-finite-free-system-restriction). -/
structure OrdinarySquare {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The direct-image comparison is identity on the same section groups. -/
  push : AlgebraicGeometry.ProEtale.SemilinearProperOpen.push
      (B l E L i) (bTransition l E L i) f ⋙ U0 l E L i Y ≅
    U0 l E L i X ⋙ AlgebraicGeometry.ProEtale.SemilinearProperOpen.push
      (A l E) (aTransition l E) f
  /-- Identity on sections, simultaneously in the level and site directions. -/
  push_section : ∀ (M : Modules (B l E L i) (bTransition l E L i) X)
    (V : (ℕ × Y.ProEt)ᵒᵖ),
    HEq (fun x ↦ (push.hom.app M).val.app V x)
      (fun x : ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.push
        (B l E L i) (bTransition l E L i) f).obj M).val.obj V ↦ x)
  /-- Pullback is the inverse adjunct of the sectionwise comparison. -/
  pull : AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull
      (B l E L i) (bTransition l E L i) f ⋙ U0 l E L i X ≅
    U0 l E L i Y ⋙ AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull
      (A l E) (aTransition l E) f
  /-- The ordinary comparison respects the specified adjunctions. -/
  mate : (mateEquiv (ordinaryAdj (B l E L i) (bTransition l E L i) f)
    (ordinaryAdj (A l E) (aTransition l E) f)
      (TwoSquare.mk _ _ _ _ pull.inv)).natTrans = push.hom

/-- The exact pullback comparison on entire derived systems.
Source: proof Step 8 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def OrdinarySquare.derivedPull {X Y : Scheme.{u}} {f : X ⟶ Y}
    (q : OrdinarySquare l E L i f) :
    P (B l E L i) (bTransition l E L i) f ⋙ U l E L i X ≅
      U l E L i Y ⋙ P (A l E) (aTransition l E) f :=
  Functor.mapDerivedCategorySquareIso q.pull

/-- The derived pushforward comparison is the specified geometric right mate.
Source: proof Step 8 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def OrdinarySquare.derivedPush {X Y : Scheme.{u}} {f : X ⟶ Y}
    (q : OrdinarySquare l E L i f) :
    R (B l E L i) (bTransition l E L i) f ⋙ U l E L i Y ⟶
      U l E L i X ⋙ R (A l E) (aTransition l E) f :=
  (mateEquiv (adj (B l E L i) (bTransition l E L i) f)
    (adj (A l E) (aTransition l E) f)
      (TwoSquare.mk _ _ _ _ (q.derivedPull l E L i).inv)).natTrans

/-- The inverse open-extension comparison is the specified open-adjunction mate.
Its invertibility is asserted separately, never inferred merely from a mate formula.
Source: proof Step 9 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def OrdinarySquare.derivedOpenInv {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsOpenImmersion f] (q : OrdinarySquare l E L i f) :
    U l E L i X ⋙ J (A l E) (aTransition l E) f ⟶
      J (B l E L i) (bTransition l E L i) f ⋙ U l E L i Y :=
  ((mateEquiv (jAdj (B l E L i) (bTransition l E L i) f)
    (jAdj (A l E) (aTransition l E) f)).symm
      (TwoSquare.mk _ _ _ _ (q.derivedPull l E L i).hom)).natTrans

/-- The simultaneous geometric comparisons on the specified finite-type k-schemes.
Source: geometric comparison clauses of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
structure Geometry (D : FiniteFieldDatum.{u}) where
  /-- The comparisons already exist on the abelian system categories. -/
  ordinary : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    OrdinarySquare l E L i f
  /-- The derived geometric right mate is invertible. -/
  push_isIso : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    IsIso ((ordinary X Y f).derivedPush l E L i)
  /-- The derived open-adjunction mate is invertible. -/
  open_isIso : ∀ (X Y : Spaces D) (j : X.val.left ⟶ Y.val.left)
    [IsOpenImmersion j], IsIso ((ordinary X Y j).derivedOpenInv l E L i)
  /-- Constant coefficient sections give the actual ordinary pushforward map. -/
  coefficient_push : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    coefficientModule l E L i Y.val.left ⟶
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.push (A l E) (aTransition l E) f).obj
        (coefficientModule l E L i X.val.left)
  /-- Its sections are exactly the structural constant-section map for B. -/
  coefficient_push_section : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left)
    (V : (ℕ × Y.val.left.ProEt)ᵒᵖ),
    HEq (fun x ↦ (coefficient_push X Y f).val.app V x)
      (fun x ↦ (coefficientMap (B l E L i) (bTransition l E L i) f).hom.app V x)
  /-- Its ordinary pullback adjunct is invertible; exact localization gives the
  coefficient pullback isomorphism with precisely this constant-section normalization. -/
  coefficient_pull_isIso : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    IsIso (((ordinaryAdj (A l E) (aTransition l E) f).homEquiv _ _).symm
      (coefficient_push X Y f))

/-- The specified derived direct-image scalar comparison as an isomorphism.
Source: geometric comparison clause of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def Geometry.pushIso {D : FiniteFieldDatum.{u}} (G : Geometry l E L i D)
    (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left) :
    R (B l E L i) (bTransition l E L i) f ⋙ U l E L i Y.val.left ≅
      U l E L i X.val.left ⋙ R (A l E) (aTransition l E) f := by
  letI := G.push_isIso X Y f
  exact asIso ((G.ordinary X Y f).derivedPush l E L i)

/-- The specified derived open-extension scalar comparison as an isomorphism.
Source: geometric comparison clause of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def Geometry.openIso {D : FiniteFieldDatum.{u}} (G : Geometry l E L i D)
    (X Y : Spaces D) (j : X.val.left ⟶ Y.val.left) [IsOpenImmersion j] :
    J (B l E L i) (bTransition l E L i) j ⋙ U l E L i Y.val.left ≅
      U l E L i X.val.left ⋙ J (A l E) (aTransition l E) j := by
  letI := G.open_isIso X Y j
  exact (asIso ((G.ordinary X Y j).derivedOpenInv l E L i)).symm


/-- Preservation of the specified geometric generators. All equations are on whole
system objects and use the published compositors, clopen projector and intrinsic mates.
Source: proof Steps 10--12 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
structure Compatibility {D : FiniteFieldDatum.{u}} (G : Geometry l E L i D) : Prop where
  /-- The specified direct-image identity comparison is preserved. -/
  push_id : ∀ (X : Spaces D)
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    (U l E L i X.val.left).map
      ((sId (B l E L i) (bTransition l E L i) X.val.left).hom.app M) =
    (G.pushIso l E L i X X (𝟙 X.val.left)).hom.app M ≫
      (sId (A l E) (aTransition l E) X.val.left).hom.app
        ((U l E L i X.val.left).obj M)
  /-- The specified open-extension identity comparison is preserved. -/
  open_id : ∀ (X : Spaces D)
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    (U l E L i X.val.left).map
      ((jId (B l E L i) (bTransition l E L i) X.val.left).hom.app M) =
    (G.openIso l E L i X X (𝟙 X.val.left)).hom.app M ≫
      (jId (A l E) (aTransition l E) X.val.left).hom.app
        ((U l E L i X.val.left).obj M)
  /-- The specified pullback identity comparison is preserved. -/
  pull_id : ∀ (X : Spaces D)
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    (U l E L i X.val.left).map
      ((pId (B l E L i) (bTransition l E L i) X.val.left).hom.app M) =
    ((G.ordinary X X (𝟙 X.val.left)).derivedPull l E L i).hom.app M ≫
      (pId (A l E) (aTransition l E) X.val.left).hom.app
        ((U l E L i X.val.left).obj M)
  /-- The direct-image compositors are preserved. -/
  push_comp : ∀ (X Y Z : Spaces D) (f : X.val.left ⟶ Y.val.left)
    (g : Y.val.left ⟶ Z.val.left)
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    (U l E L i Z.val.left).map
        ((sComp (B l E L i) (bTransition l E L i) f g).hom.app M) ≫
      (G.pushIso l E L i X Z (f ≫ g)).hom.app M =
    (G.pushIso l E L i Y Z g).hom.app
        ((R (B l E L i) (bTransition l E L i) f).obj M) ≫
      (R (A l E) (aTransition l E) g).map ((G.pushIso l E L i X Y f).hom.app M) ≫
      (sComp (A l E) (aTransition l E) f g).hom.app ((U l E L i X.val.left).obj M)
  /-- The open-extension compositors are preserved. -/
  open_comp : ∀ (X Y Z : Spaces D) (f : X.val.left ⟶ Y.val.left)
    (g : Y.val.left ⟶ Z.val.left) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Derived (B l E L i) (bTransition l E L i) X.val.left),
    (U l E L i Z.val.left).map
        ((jComp (B l E L i) (bTransition l E L i) f g).hom.app M) ≫
      (G.openIso l E L i X Z (f ≫ g)).hom.app M =
    (G.openIso l E L i Y Z g).hom.app
        ((J (B l E L i) (bTransition l E L i) f).obj M) ≫
      (J (A l E) (aTransition l E) g).map ((G.openIso l E L i X Y f).hom.app M) ≫
      (jComp (A l E) (aTransition l E) f g).hom.app ((U l E L i X.val.left).obj M)
  /-- The pullback compositors are preserved. -/
  pull_comp : ∀ (X Y Z : Spaces D) (f : X.val.left ⟶ Y.val.left)
    (g : Y.val.left ⟶ Z.val.left)
    (M : Derived (B l E L i) (bTransition l E L i) Z.val.left),
    (U l E L i X.val.left).map
        ((pComp (B l E L i) (bTransition l E L i) f g).hom.app M) ≫
      ((G.ordinary X Y f).derivedPull l E L i).hom.app
        ((P (B l E L i) (bTransition l E L i) g).obj M) ≫
      (P (A l E) (aTransition l E) f).map
        (((G.ordinary Y Z g).derivedPull l E L i).hom.app M) =
    ((G.ordinary X Z (f ≫ g)).derivedPull l E L i).hom.app M ≫
      (pComp (A l E) (aTransition l E) f g).hom.app ((U l E L i Z.val.left).obj M)
  /-- Clopen projectors, including their identity/zero normalization, are preserved. -/
  clopen : ∀ (X Y : Spaces D) (s : X.val.left ⟶ Y.val.left)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (M : Derived (B l E L i) (bTransition l E L i) Y.val.left),
    (U l E L i Y.val.left).map ((pi (B l E L i) (bTransition l E L i) s).app M) ≫
      (G.openIso l E L i X Y s).hom.app
        ((P (B l E L i) (bTransition l E L i) s).obj M) ≫
      (J (A l E) (aTransition l E) s).map
        (((G.ordinary X Y s).derivedPull l E L i).hom.app M) =
    (pi (A l E) (aTransition l E) s).app ((U l E L i Y.val.left).obj M)
  /-- The normalized Cartesian open comparison is preserved. -/
  beta : ∀ (V W S T : Spaces D) (k : V.val.left ⟶ W.val.left)
    (r : V.val.left ⟶ S.val.left) (p : W.val.left ⟶ T.val.left)
    (j : S.val.left ⟶ T.val.left) [IsOpenImmersion k] [IsOpenImmersion j]
    (h : k ≫ p = r ≫ j) (sq : IsPullback r k j p)
    (M : Derived (B l E L i) (bTransition l E L i) S.val.left),
    (U l E L i W.val.left).map
        ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.beta
          (B l E L i) (bTransition l E L i) r k j p h.symm sq).hom.app M) ≫
      (G.openIso l E L i V W k).hom.app
        ((P (B l E L i) (bTransition l E L i) r).obj M) ≫
      (J (A l E) (aTransition l E) k).map
        (((G.ordinary V S r).derivedPull l E L i).hom.app M) =
    ((G.ordinary W T p).derivedPull l E L i).hom.app
        ((J (B l E L i) (bTransition l E L i) j).obj M) ≫
      (P (A l E) (aTransition l E) p).map ((G.openIso l E L i S T j).hom.app M) ≫
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.beta
        (A l E) (aTransition l E) r k j p h.symm sq).hom.app ((U l E L i S.val.left).obj M)
  /-- The intrinsic proper/open alpha comparison is preserved. -/
  alpha : ∀ (V W S T : Spaces D) (k : V.val.left ⟶ W.val.left)
    (r : V.val.left ⟶ S.val.left) (p : W.val.left ⟶ T.val.left)
    (j : S.val.left ⟶ T.val.left) [IsOpenImmersion k] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact j] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ j)
    (M : Derived (B l E L i) (bTransition l E L i) S.val.left),
    (U l E L i W.val.left).map
        ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.alpha
          (B l E L i) (bTransition l E L i) k r p j h).app M) ≫
      (G.openIso l E L i V W k).hom.app
        ((P (B l E L i) (bTransition l E L i) r).obj M) ≫
      (J (A l E) (aTransition l E) k).map
        (((G.ordinary V S r).derivedPull l E L i).hom.app M) =
    ((G.ordinary W T p).derivedPull l E L i).hom.app
        ((J (B l E L i) (bTransition l E L i) j).obj M) ≫
      (P (A l E) (aTransition l E) p).map ((G.openIso l E L i S T j).hom.app M) ≫
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.alpha
        (A l E) (aTransition l E) k r p j h).app ((U l E L i S.val.left).obj M)
  /-- The well-typed right mate J_j R_r to R_p J_k is preserved. -/
  gamma : ∀ (V W S T : Spaces D) (k : V.val.left ⟶ W.val.left)
    (r : V.val.left ⟶ S.val.left) (p : W.val.left ⟶ T.val.left)
    (j : S.val.left ⟶ T.val.left) [IsOpenImmersion k] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact j] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ j)
    (M : Derived (B l E L i) (bTransition l E L i) V.val.left),
    (U l E L i T.val.left).map
        ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma
          (B l E L i) (bTransition l E L i) k r p j h).app M) ≫
      (G.pushIso l E L i W T p).hom.app
        ((J (B l E L i) (bTransition l E L i) k).obj M) ≫
      (R (A l E) (aTransition l E) p).map ((G.openIso l E L i V W k).hom.app M) =
    (G.openIso l E L i S T j).hom.app
        ((R (B l E L i) (bTransition l E L i) r).obj M) ≫
      (J (A l E) (aTransition l E) j).map ((G.pushIso l E L i V S r).hom.app M) ≫
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma
        (A l E) (aTransition l E) k r p j h).app ((U l E L i V.val.left).obj M)

/-- Preservation of any already invertible factor in a compactification word.
This supplies inverses of proper/open refinement factors without asserting that a
proper/open factor is invertible. Whiskering and composing this equation gives the
same assertion for every finite word in the specified generators and their inverses.
Source: proof Step 13 of the node
(blueprint: lem-coef-finite-free-system-restriction).
Proof: conjugate the assumed hom square by the two inverse arrows. Functoriality
and the hom-inv and inv-hom identities cancel the hom arrows, leaving precisely
the displayed inverse square. Thus no conservativity or new invertibility is used. -/
theorem inverse_compatibility (X : Scheme.{u})
    {M N : Derived (B l E L i) (bTransition l E L i) X}
    {M' N' : Derived (A l E) (aTransition l E) X}
    (a : M ≅ N) (b : M' ≅ N')
    (x : (U l E L i X).obj M ≅ M') (y : (U l E L i X).obj N ≅ N')
    (_h : (U l E L i X).map a.hom ≫ y.hom = x.hom ≫ b.hom) :
    (U l E L i X).map a.inv ≫ x.hom = y.hom ≫ b.inv := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, b.inv_hom_id, Category.comp_id]
  rw [← _h, ← Category.assoc, ← Functor.map_comp, a.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The strict-system realization of a fixed compactification h = pj.
Source: the compact-support clause of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def compact (C : ℕ → CommRingCat.{u + 1}) (t : ∀ n, C (n + 1) ⟶ C n)
    {X W Y : Scheme.{u}} (j : X ⟶ W) (p : W ⟶ Y) [IsOpenImmersion j] :=
  J C t j ⋙ R C t p

/-- Restriction past a fixed compactification: first past proper direct image,
then past open extension, exactly as in the node's proof.
Source: proof Step 13 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def Geometry.compactIso {D : FiniteFieldDatum.{u}} (G : Geometry l E L i D)
    (X W Y : Spaces D) (j : X.val.left ⟶ W.val.left)
    (p : W.val.left ⟶ Y.val.left) [IsOpenImmersion j] :
    compact (B l E L i) (bTransition l E L i) j p ⋙ U l E L i Y.val.left ≅
      U l E L i X.val.left ⋙ compact (A l E) (aTransition l E) j p :=
  compactScalarIso
    (XB := Derived (B l E L i) (bTransition l E L i) X.val.left)
    (WB := Derived (B l E L i) (bTransition l E L i) W.val.left)
    (YB := Derived (B l E L i) (bTransition l E L i) Y.val.left)
    (XA := Derived (A l E) (aTransition l E) X.val.left)
    (WA := Derived (A l E) (aTransition l E) W.val.left)
    (YA := Derived (A l E) (aTransition l E) Y.val.left)
    (U l E L i X.val.left) (U l E L i W.val.left)
    (U l E L i Y.val.left) (J (B l E L i) (bTransition l E L i) j)
    (R (B l E L i) (bTransition l E L i) p)
    (J (A l E) (aTransition l E) j) (R (A l E) (aTransition l E) p)
    (G.openIso l E L i X W j) (G.pushIso l E L i W Y p)

/-- The specified compactification-composition word. Its middle factor is precisely
the proper/open right mate, followed by the published open and proper compositors.
No inverse of a proper/open map, or new invertibility assertion, is introduced here.
Source: compactification word in proof Step 13 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def compactCompositionWord (C : ℕ → CommRingCat.{u + 1})
    (t : ∀ n, C (n + 1) ⟶ C n) {X V W S T Z : Scheme.{u}}
    (j : X ⟶ V) (r : V ⟶ S) (a : S ⟶ T) (q : T ⟶ Z)
    (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion a] [IsOpenImmersion k]
    [QuasiCompact a] [QuasiCompact k] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ a) :
    compact C t j r ⋙ compact C t a q ⟶ compact C t (j ≫ k) (p ≫ q) :=
  compactWord (X := Derived C t X) (V := Derived C t V) (W := Derived C t W)
    (S := Derived C t S) (T := Derived C t T) (Z := Derived C t Z)
    (J C t j) (J C t k) (J C t a) (J C t (j ≫ k))
    (R C t r) (R C t p) (R C t q) (R C t (p ≫ q))
    (gamma C t k r p a h) (jComp C t j k) (sComp C t p q)


/-- The source's levelwise bounded constructible finite-Tor condition, using the
recorded level tensor and constructibility definitions. The Tor interval is chosen
inside the quantifier over n, so no uniform interval is imposed.
Source: the input class of the compactification-composition clause
(blueprint: lem-coef-finite-free-system-restriction). -/
def levelwiseCtf (C : ℕ → CommRingCat.{u + 1}) (t : ∀ n, C (n + 1) ⟶ C n)
    (X : Scheme.{u}) (c : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients C X) (transition C t X)) (M : Derived C t X) : Prop :=
  ∀ n : ℕ,
    Set.Finite {j : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients C X) (transition C t X) n).obj M))} ∧
    (∀ j : ℤ, AlgebraicGeometry.ProEtale.IsConstructible (C n)
      (fixedModule X (C n) ((DerivedCategory.homologyFunctor _ j).obj
        ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (coefficients C X) (transition C t X) n).obj M)))) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ (N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (coefficients C X n)) (j : ℤ),
      (j < a ∨ b < j) → IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((c.levelClosed n).tensor.obj
          (((e.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
            (coefficients C X) (transition C t X) n).obj M),
            (DerivedCategory.singleFunctor _ 0).obj N)))

end WeilConjectures.FiniteFreeSystemRestriction
