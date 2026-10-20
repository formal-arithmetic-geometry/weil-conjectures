/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q63, Q92
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.PurInverseImageTensorHom

/-! # Isomorphism inverse image of completed coefficient reduction towers

Source: blueprint main-20261015, ordinary compact cohomology, coefficient paragraph;
Stacks Tags 03EL, 03EK, 06YS, 06YY and 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Index n denotes the positive exponent n+1. Inverse image is the recorded sectionwise
model of the site equivalence, with its module action transported by the inverse
of the canonical coefficient map. All coefficients have size max u (t+1).

## Main definitions and statements

- `isoReductionCompletedMap`: the limit coefficient isomorphism fixed by projections.
- `isoReductionIntegralInverse`, `isoReductionFiniteInverse`: recorded inverse image
  with scalar action transported through the canonical ring isomorphisms.
- `isomorphismReductionTower`: normalized complex isomorphisms, quotient and
  transition identities, naturality and canonical resolution compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t u r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Abelian sheafification in a coefficient universe containing the site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance (priority := 4000) isoReductionAbSheafify (W : Scheme.{t})
    [EssentiallySmall.{r} W.ProEt] :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse

/-- The local-bijection criterion in the same coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance (priority := 4000) isoReductionAbBijective (W : Scheme.{t})
    [EssentiallySmall.{r} W.ProEt] :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The site has a small model in the explicit coefficient universe.
Source: blueprint size convention
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance (priority := 4000) isoReductionSiteSmall (W : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf _

private theorem isoReductionConstant_hom_ext (W : Scheme.{t})
    (A B : CommRingCat.{max u (t + 1)})
    (f h : (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj A) ⟶
      (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj B))
    (hf : ∀ (U : W.ProEt) (a : A),
      f.hom.app (op U)
          ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
            (op U) a) =
        h.hom.app (op U)
          ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
            (op U) a)) : f = h := by
  let S := sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have he : S.preimage f = S.preimage h := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology W) _ _
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj B).property
    ext U a
    have ef := congrArg (fun z ↦ z.hom.app U) (S.map_preimage f)
    have eh := congrArg (fun z ↦ z.hom.app U) (S.map_preimage h)
    change ((S.map (S.preimage f)).hom.app U) _ =
      ((S.map (S.preimage h)).hom.app U) _
    rw [ef, eh]
    exact hf U.unop a
  simpa only [S.map_preimage] using congrArg S.map he

private theorem isoReductionConstant_map (W : Scheme.{t})
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) (U : W.ProEt) (a : A) :
    (((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).map f).hom.app (op U))
        (((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
          (op U)) a) =
      ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj B)).app
        (op U)) (f a) := by
  exact (congrArg (fun e ↦ (e.app (op U)) a)
    (toSheafify_naturality (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map f))).symm

private theorem isoReductionConstant_naturality
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f)) ≫
      isoSectionwiseConstantMap g B =
    isoSectionwiseConstantMap g A ≫
      (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f) := by
  let cA := isoSectionwiseConstantMap g A
  let cB := isoSectionwiseConstantMap g B
  have hA := (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
  have hB := (isoSectionwiseConstantMap_existsUnique g B).exists.choose_spec
  apply (cancel_epi (inv cA)).1
  apply isoReductionConstant_hom_ext X A B
  intro U a
  have hi : (inv cA).hom.app (op U)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op U) a) =
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U)) a := by
    rw [← hA U a]
    exact congrArg (fun e ↦ e.hom.app (op U)
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U)) a)) (IsIso.hom_inv_id cA)
  change cB.hom.app (op U)
      ((((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv cA).hom.app (op U) _)) =
    (((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f).hom.app (op U))
      (cA.hom.app (op U) ((inv cA).hom.app (op U) _))
  erw [hi, isoReductionConstant_map, hB, hA, isoReductionConstant_map]

/-- The completed coefficient comparison is uniquely specified by its projections.
Source: Stacks Tags 09A5, 03CO
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Proof: inverse image preserves the limit by the recorded site equivalence. The
constant comparisons commute with coefficient reductions by their normalization
on constants. Their inverse-limit comparison is invertible, has the displayed
projections, and is unique because limit projections are jointly monic. -/
theorem isoReductionCompletedMap_existsUnique :
    ∃! c : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
        completedIntegralCoefficientSheafUnrestricted l E X,
      ∀ n : ℕ, c.hom ≫ limit.π (integralCoefficientSheafSystem l E X) (op n) =
        (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
          isoSectionwiseConstantMap g
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let F := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  let A := integralCoefficientSheafSystem l E Y
  let B := integralCoefficientSheafSystem l E X
  let α : A ⋙ F ⟶ B := NatTrans.ofOpSequence
    (fun n ↦ isoSectionwiseConstantMap g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (fun n ↦ by
      simp only [Functor.comp_map, A, B, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact isoReductionConstant_naturality g _)
  have : ∀ n, IsIso (α.app n) := fun n ↦ isoSectionwiseConstantMap_isIso g _
  let e : A ⋙ F ≅ B := NatIso.ofComponents (fun n ↦ asIso (α.app n))
    (fun f ↦ α.naturality f)
  have : PreservesLimitsOfSize.{0, 0} F :=
    (isoSectionwiseInverseImage_equivalence g RingCat.{max u (t + 1)}).2.1
  let d : F.obj (limit A) ≅ limit B :=
    preservesLimitIso F A ≪≫ HasLimit.isoOfNatIso e
  have hd : ∀ n : ℕ, d.hom ≫ limit.π B (op n) =
      F.map (limit.π A (op n)) ≫ α.app (op n) := by
    intro n
    simp only [d, Iso.trans_hom, Category.assoc,
      HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc, e,
      NatIso.ofComponents_hom_app, asIso_hom]
  refine ⟨d, hd, ?_⟩
  intro c hc
  apply Iso.ext
  apply (limit.isLimit B).hom_ext
  intro n
  exact (hc n.unop).trans (hd n.unop).symm

/-- The actual limit comparison followed by the limit of constant comparisons.
Source: Stacks Tag 03CO
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def isoReductionCompletedMap :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
      completedIntegralCoefficientSheafUnrestricted l E X :=
  (isoReductionCompletedMap_existsUnique l E g).exists.choose

/-- Relabelling with scalar action transported along the completed comparison.
Source: Stacks Tags 00WX, 03D2
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionIntegralInverse :
    scalarReductionSource l E Y ⥤ scalarReductionSource l E X :=
  isoSectionwiseModuleInverseImage g (isoReductionCompletedMap l E g).hom

/-- Relabelling over the positive finite coefficient quotient.
Source: Stacks Tags 00WX, 03D2
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionFiniteInverse (n : ℕ) :
    scalarReductionTarget l E Y n ⥤ scalarReductionTarget l E X n :=
  isoSectionwiseModuleInverseImage g (isoSectionwiseConstantMap g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- Exactness of finite inverse image, using the recorded independent-size interface.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance isoReductionFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (isoReductionFiniteInverse l E g n) :=
  isoSectionwiseModuleInverseImage_limits.{t, u} g _

/-- Exactness of finite inverse image, using the recorded independent-size interface.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance isoReductionFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (isoReductionFiniteInverse l E g n) :=
  isoSectionwiseModuleInverseImage_colimits.{t, u} g _

/-- The completed inverse image applied termwise.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionIntegralComplex :=
  (isoReductionIntegralInverse l E g).mapHomologicalComplex (.up ℤ)

/-- The finite inverse image applied termwise.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionFiniteComplex (n : ℕ) :=
  (isoReductionFiniteInverse l E g n).mapHomologicalComplex (.up ℤ)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The K-flat and flat-term conditions of the statement, with independent sizes.
Source: Stacks Tags 06YN, 03ER
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def IsoReductionFlatComplex (W : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E W) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The finite derived inverse image, expressed on represented complexes.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def isoReductionFiniteDerived (n : ℕ) :
    DerivedCategory (scalarReductionTarget l E Y n) ⥤
      DerivedCategory (scalarReductionTarget l E X n) :=
  (isoReductionFiniteInverse l E g n).mapDerivedCategory

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The image of the canonical resolution comparison, expressed at the termwise
inverse-image complexes using the canonical localization factorization.
Source: Stacks Tags 015F, 06YY
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def isoReductionImageComparison (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q') :=
  ((isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.app _).symm ≪≫
    (isoReductionFiniteDerived l E g n).mapIso
      (unrestrictedTowerFiniteComparison l E Y n q q' hq hq') ≪≫
    (isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.app _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Exact relabelling preserves the quasi-isomorphism of an augmentation.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Proof: the recorded inverse image is additive and exact. It commutes with cohomology
by preserving kernels and cokernels. Therefore a cohomology isomorphism remains
an isomorphism in every degree. -/
theorem isoReductionMapQuasiIso
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (hq : QuasiIso q) :
    QuasiIso ((isoReductionIntegralComplex l E g).map q) := by
  have : QuasiIso q := hq
  exact HomologicalComplex.quasiIso_map_of_preservesHomology q
    (isoReductionIntegralInverse l E g)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The normalized tensor identifications intertwine quotient arrows, transitions,
chain maps and the canonical finite-coefficient resolution comparisons.
Source: blueprint main-20261015, ordinary compact cohomology, coefficient paragraph;
Stacks Tags 03EL, 03EK, 06YS, 06YY and 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Proof:
1. Inverse image preserves the completed coefficient limit. Naturality of the finite
constant comparisons makes their inverse limit a ring isomorphism with the stated
projection squares (lem-weil-proetale-isomorphism-inverse-image).
2. Apply lem-pur-isomorphism-inverse-image-tensor-hom degreewise, then transport
coefficients along those ring isomorphisms. The projection square verifies the
balanced relation; the inverse uses the inverse coefficient isomorphisms.
3. The coefficient factor has degree zero. Tensor naturality for d_P makes these
maps and their inverses chain maps (def-pc-tensor-complex-sheaves).
4. The local formula sends x tensor 1 to F(x) tensor 1 because c is unital.
This is precisely the quotient-arrow equation (def-weil-integral-reduction-tower).
5. Naturality of c for coefficient reductions identifies the two transition maps
on pure tensors. Tensor generation and sheafification extend this to all sections.
6. Tensor naturality in P gives the displayed chain-map naturality equation.
7. Exact inverse image preserves quasi-isomorphisms and homotopies by
lem-weil-pbc-exact-functor-derived-factorization, so it descends to derived categories.
8. Apply lem-pur-quasi-isos-saturated-triangulated to find a common roof for q,q'.
Resolve its source by lem-pc-kflat-resolution. Pullback preserves K-flatness and
flat terms by lem-weil-pbc-ringed-pullback-preserves-kflat; scalar-isomorphism
normalization identifies it with inverse image (lem-weil-sheaf-scalar-extension-ring-iso).
9. The universal derived-change-of-rings counit identifies theta with
[a_n] inverse followed by [b_n], using lem-pur-derived-change-of-rings and
lem-pur-left-derived-from-kflat-class. These are exactly the comparisons of
lem-weil-integral-reduction-tower-well-defined on both schemes.
10. Apply chain-map naturality to a,b and cancel the invertible reductions of a.
This yields the final equality in the finite-coefficient derived category on X. -/
theorem isomorphismReductionTower
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      IsoReductionFlatComplex l E Y P → ∀ n : ℕ,
        (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
          unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P),
      (∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
        (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (((β P hP n).hom.f i).val.app (op U))
          (unrestrictedTowerTensorSection l E Y n (P.X i)
            (op ((proEtaleIsoPostcompose g).obj U)) a x) =
          unrestrictedTowerTensorSection l E X n
            (((isoReductionIntegralComplex l E g).obj P).X i) (op U)
            ((isoSectionwiseConstantMap g (CommRingCat.of
              (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
                (op U) a) x) ∧
      (∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
        (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (((β P hP n).hom.f i).val.app (op U))
          (((unrestrictedTowerUnit l E Y P n).f i).val.app
            (op ((proEtaleIsoPostcompose g).obj U)) x) =
          (((unrestrictedTowerUnit l E X ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app
             (op U)) x) ∧
      (∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
        (z : ((unrestrictedTowerFiniteComplex l E Y (n + 1) P).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((β P hP n).hom.f i).val.app (op U))
          (((unrestrictedTowerTransition l E Y P n).f i).val.app
            (op ((proEtaleIsoPostcompose g).obj U)) z) =
          (((unrestrictedTowerTransition l E X
            ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app (op U))
              ((((β P hP (n + 1)).hom.f i).val.app (op U)) z)) ∧
      (∀ (P P' : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (hP' : IsoReductionFlatComplex l E Y P')
        (a : P ⟶ P') (n : ℕ),
        (isoReductionFiniteComplex l E g n).map
            (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).map a) ≫
          (β P' hP' n).hom =
        (β P hP n).hom ≫
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).map
            ((isoReductionIntegralComplex l E g).map a)) ∧
      (∀ (P P' K : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (hP' : IsoReductionFlatComplex l E Y P')
        (q : P ⟶ K) (q' : P' ⟶ K) (hq : QuasiIso q) (hq' : QuasiIso q')
        (hFP : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          ((isoReductionIntegralComplex l E g).obj P))
        (hFP' : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          ((isoReductionIntegralComplex l E g).obj P')) (n : ℕ),
        (isoReductionImageComparison l E g n q q' ⟨hq, hP.1⟩ ⟨hq', hP'.1⟩).hom ≫
          DerivedCategory.Q.map (β P' hP' n).hom =
        DerivedCategory.Q.map (β P hP n).hom ≫
          (unrestrictedTowerFiniteComparison l E X n
            ((isoReductionIntegralComplex l E g).map q)
            ((isoReductionIntegralComplex l E g).map q')
            ⟨isoReductionMapQuasiIso l E g q hq, hFP⟩
            ⟨isoReductionMapQuasiIso l E g q' hq', hFP'⟩).hom) := by
  sorry

end WeilConjectures
