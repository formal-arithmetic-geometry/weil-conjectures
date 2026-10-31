/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicFibreComparisonCoherence
import WeilConjectures.AlgebraicGeometry.NormalizedPullbackObjects
import WeilConjectures.AlgebraicGeometry.NormalizedPullbackNaturality
import WeilConjectures.AlgebraicGeometry.NormalizedPullbackCoherence

/-! # Normalized geometric fibres and actual completed pullback

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Remark 6.8.15;
Stacks Tag 03Q1(3) (blueprint: lem-per-adic-normalized-fibre-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- The pullback part of normalized fibre comparisons, without scalar or rank assertions.
The existing Fibres, PullLimit, heartPull, germ and pullModelMap definitions are used
literally. The local field spells out the derived-counit and integral reduction equations:
neither the target lattice presentation nor its rational comparison may absorb a scalar.
Source: BS 6.8.4(1),(4),(6), 6.8.15; Stacks 03Q1(3)
(blueprint: lem-per-adic-normalized-fibre-pullback). -/
structure NormalizedPullback (ω : Fibres (k := k) l R) where
  pull : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    heartPull l A R g ⋙ ((ω A Y).point κ y).functor ≅
      ((ω A X).point κ (y ≫ g)).functor
  identity : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k),
    ∃ e : heartPull l A R (𝟙 X.scheme) ≅ 𝟭 _,
      (∀ F, HEq (e.hom.app F).hom ((R.identity A (base l X)).raw.hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        HEq ((pull A (𝟙 X.scheme) κ x).hom.app F)
          (((ω A X).point κ x).functor.map (e.hom.app F))
  composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X Y Z : FiniteTypeBase k)
    (g : Y.scheme ⟶ X.scheme) (h : Z.scheme ⟶ Y.scheme),
    ∃ e : heartPull l A R (h ≫ g) ≅ heartPull l A R g ⋙ heartPull l A R h,
      (∀ F, HEq (e.hom.app F).hom
        ((R.composition A (X := base l Y) (Y := base l X) (Z := base l Z) g h).raw.hom.app
          F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (z : Spec (.of κ) ⟶ Z.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        HEq ((pull A (h ≫ g) κ z).hom.app F)
          (((ω A Z).point κ z).functor.map (e.hom.app F) ≫
            (pull A h κ z).hom.app ((heartPull l A R g).obj F) ≫
              (pull A g κ (z ≫ h)).hom.app F)
  unit_normalization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l A (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme A))
    (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M),
    ∃ e' : (R.realization A (base l Y)).J.obj ((heartPull l A R g).obj F).obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((modulePull g (R.along A (X := base l Y) (Y := base l X) g).coefficient).obj M),
      e'.hom = pullModelMap l R A g F M e ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (U : X.scheme.ProEt)
        (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange (y ≫ g)).obj U)
        (q' : ProEt.mk (𝟙 (Spec (.of κ))) ⟶
          (proEtaleBaseChange y).obj ((proEtaleBaseChange g).obj U))
        (_hq : q.left ≫ pullback.fst U.hom (y ≫ g) =
          q'.left ≫ pullback.fst ((proEtaleBaseChange g).obj U).hom y ≫
            pullback.fst U.hom g) (m : M.val.obj (op U)),
        (presentedFibre l R A ω X F M e κ (y ≫ g)).hom
          (((pull A g κ y).hom.app F)
            ((presentedFibre l R A ω Y ((heartPull l A R g).obj F) _ e' κ y).inv
              (germ l A _ κ y ((proEtaleBaseChange g).obj U) q'
                (moduleUnit g (R.along A (X := base l Y) (Y := base l X) g).coefficient
                  M U m)))) = germ l A M κ (y ≫ g) U q m
  local_normalization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l A (base l X)) (C : NormalizedFibre.Chart l (base l X))
    (hC : C.Adapted l A (R.realization A (base l X)) F)
    (N : NormalizedFibre.Lattice l A C.scheme)
    (φ : (C.restrict l A (R.realization A (base l X))).obj F ≅ N.rational l A)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
    (s : Spec (.of κ) ⟶ C.scheme) (hs : s ≫ C.map = y ≫ g)
    (W₀ : (pullback g C.map).affineOpens)
    (t₀ : Spec (.of κ) ⟶ W₀.1.toScheme)
    (_ht₀ : t₀ ≫ W₀.1.ι = pullback.lift y s hs.symm),
    ∃ (D : NormalizedFibre.Chart l (base l Y)) (f : D.scheme ⟶ C.scheme)
      (t : Spec (.of κ) ⟶ D.scheme) (i₀ : D.scheme ≅ W₀.1.toScheme)
      (hD : D.Adapted l A (R.realization A (base l Y)) ((heartPull l A R g).obj F))
      (M : NormalizedFibre.Lattice l A D.scheme)
      (ψ : (D.restrict l A (R.realization A (base l Y))).obj
        ((heartPull l A R g).obj F) ≅ M.rational l A)
      (hsystem : M.system = N.system ⋙ Etale.upperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)) f)
      (q : (D.restrict l A (R.realization A (base l Y))).obj
        ((heartPull l A R g).obj F) ≅
          (modulePull f (NormalizedFibre.coefficient l A f)).obj
            ((C.restrict l A (R.realization A (base l X))).obj F))
      (η : (modulePull f (NormalizedFibre.coefficient l A f)).obj
        (N.rational l A) ≅ M.rational l A)
      (P : PullLimit l A f N M κ t
        (pullTowerIso l A f N M (eqToIso hsystem) κ t)),
      D.map = i₀.hom ≫ W₀.1.ι ≫ pullback.fst g C.map ∧
      f = i₀.hom ≫ W₀.1.ι ≫ pullback.snd g C.map ∧ t ≫ i₀.hom = t₀ ∧
      D.map ≫ g = f ≫ C.map ∧ t ≫ D.map = y ∧ t ≫ f = s ∧
      (∃ (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((NormalizedFibre.realize l A (base l X) (R.realization A (base l X))).obj F))
    (e' : (R.realization A (base l Y)).J.obj ((heartPull l A R g).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((modulePull g (R.along A (X := base l Y) (Y := base l X) g).coefficient).obj
          ((NormalizedFibre.realize l A (base l X) (R.realization A (base l X))).obj F))),
    ((DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).hom = 𝟙 _ ∧
    e'.hom = pullModelMap l R A g F _ e ∧
    ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ D.scheme)
      (W : X.scheme.ProEt)
      (a : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange t).obj
        ((proEtaleBaseChange D.map).obj ((proEtaleBaseChange g).obj W)))
      (b : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange t).obj
        ((proEtaleBaseChange f).obj ((proEtaleBaseChange C.map).obj W)))
      (_hab : a.left ≫ pullback.fst _ t ≫ pullback.fst _ D.map ≫ pullback.fst W.hom g =
        b.left ≫ pullback.fst _ t ≫ pullback.fst _ f ≫ pullback.fst W.hom C.map)
      (m : ((NormalizedFibre.realize l A (base l X)
        (R.realization A (base l X))).obj F).val.obj (op W)),
      (NormalizedFibre.ambient l A κ t).map q.hom
        (germ l A _ κ t _ a
          (moduleUnit D.map (NormalizedFibre.coefficient l A D.map) _ _
            (((DerivedCategory.homologyFunctor _ 0).mapIso e' ≪≫
                (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).inv.val.app
                  (op ((proEtaleBaseChange g).obj W))
              (moduleUnit g (R.along A (X := base l Y) (Y := base l X) g).coefficient
                _ W m)))) =
        germ l A _ κ t _ b (moduleUnit f (NormalizedFibre.coefficient l A f) _ _
          (moduleUnit C.map (NormalizedFibre.coefficient l A C.map) _ W m))) ∧
      (∃ δ : (NormalizedFibre.forgetIntegral l A C.scheme).obj N.integral ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((NormalizedFibre.forgetIntegral l A D.scheme).obj M.integral),
    (∀ n : ℕ, δ ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        (M.reduction.app (op n)) = N.reduction.app (op n) ≫
      ((supportSiteProEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).inv.app _ ≫
          (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} D.scheme).map
            ((supportSiteEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
              |>.symm
        ((sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map
          ((supportSiteEtaleComparisonAdjunction
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)) f).unit.app
              (N.system.obj (op n))) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
            ((sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map
              ((eqToIso hsystem).inv.app (op n)))))))) ∧
    ∀ (W : C.scheme.ProEt) (m : N.integral.val.obj (op W)),
      η.hom.val.app (op ((proEtaleBaseChange f).obj W))
        (moduleUnit f (NormalizedFibre.coefficient l A f) (N.rational l A) W
          (pbcTensorSection (integralRationalCoefficientMap l A C.scheme) N.integral
            (op W) 1 m)) =
        pbcTensorSection (integralRationalCoefficientMap l A D.scheme) M.integral
          (op ((proEtaleBaseChange f).obj W)) 1 (δ.hom.app (op W) m)) ∧
      ψ.hom = q.hom ≫ (modulePull f (NormalizedFibre.coefficient l A f)).map φ.hom ≫
        η.hom ∧
      HEq ((pull A g κ y).hom.app F)
        (((ω A Y).normalization D ((heartPull l A R g).obj F) hD M ψ κ t).hom ≫
          (ModuleCat.extendScalars.{u, u, u + 1}
            (Padic.coefficientExtensionIntegers l A).subtype).map
            P.iso.hom ≫
          ((ω A X).normalization C F hC N φ κ (t ≫ f)).inv)


private theorem pullLimit_unique (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {U V : Scheme.{u}} (g : V ⟶ U)
    (N : NormalizedFibre.Lattice l A U) (M : NormalizedFibre.Lattice l A V)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ V)
    (e : M.system ⋙ (pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)) ≅
      N.system ⋙ (pointSmallEtale (x ≫ g)).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)))
    (P Q : PullLimit l A g N M κ x e) : P = Q := by
  have hi : P.iso = Q.iso := by
    apply Iso.ext
    apply limit.hom_ext
    intro j
    exact (P.projection j.unop).trans (Q.projection j.unop).symm
  cases P
  cases Q
  cases hi
  rfl


/-- Normalized fibres commute with every actual completed rational pullback.
The coefficient fields are quantified in Fibres and NormalizedPullback; the fixed
algebraic closure and a further finite extension play no role in this pullback assertion.

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Remark 6.8.15; Stacks 03Q1(3)
(blueprint: lem-per-adic-normalized-fibre-pullback).

Proof plan (the eight steps of the node):
1. Finite-type schemes over the field are noetherian and finite-dimensional, by
lem-weil-pbc-finite-type-over-noetherian and lem-fin-finite-type-fibre-dimension-bound.
The prime is invertible by the stated base-field hypothesis.
2. Use lem-per-adic-normalized-fibre-exactness to choose an adapted affine etale chart
and its normalized lattice. The realization J of
lem-per-continuous-rational-derived-realization identifies actual completed pullback
with derived module inverse image, compatibly with stratum and chart restriction.
The heart and finite-free local models come from lem-per-adic-stratified-pullback-texact.
Use lem-per-lisse-completed-system-comparison to reconstruct the pulled lattice from
its pulled reductions. Finite free modules are already flat resolutions. The ordinary
balanced tensor sends b tensor e_j to b e_j. On a non-affine pulled chart, restrict to
any chosen affine open neighbourhood of its lifted geometric point.
3. Apply lem-weil-pbc-inverse-image-stalk-germ at each positive quotient level. Its
canonical map sends each pulled section germ to its original germ. Naturality in
multiplication maps gives coefficient linearity; naturality in reduction gives quotient
compatibility. These maps constitute the existing pullTowerIso of the stalk towers.
4. On inverse limits send (m_n) to (c_n(m_n)); the componentwise inverse is its inverse.
The projection equations are exactly PullLimit.projection. Localize at the uniformizer
and conjugate by the normalized fibre identifications to obtain pull.
5. Finite-level naturality gives naturality on integral lattice maps. For a map divided
by a uniformizer power both sides acquire the same inverse scalar, using the dependency's
fractions equation. If two fractions are equal, a power kills their cleared difference;
after rationalization that scalar is invertible, so their fibre maps coincide. Integral
Hom modules are not assumed torsion-free.
6. On an affine common refinement, full faithfulness of raw lattice rationalization
in lem-per-lisse-completed-system-comparison represents the comparison of two lattices
and its inverse by fractions. Step 5 conjugates their pullback comparisons into one
another. This is precisely independence of lattice and fractional representative.
7. Compare charts on pointed affine etale refinements. For different stratifications,
use intersections of the strata, then the same construction. The restriction comparisons
of J and the completed-system equivalence identify both with the same intrinsic fibre.
Step 6 therefore gives the same pull map. A common refinement for source and target
of an arbitrary heart arrow and step 5 give the stated natural isomorphism.
8. At each finite level, the identity and the two composite-pullback maps have the same
germ formula. They therefore agree under the actual inverse-image unit and associator.
The completed-system and J comparisons preserve these equations. Take inverse limits
and localize to obtain identity and composition with the specified raw comparisons.
No flatness of the scheme map or coefficient map, and no exchange of arbitrary
pro-etale stalks with inverse limits, is used. Empty strata and rank zero are included. -/
theorem adic_normalized_fibre_pullback :
    ∃ ω : Fibres (k := k) l R, Nonempty (NormalizedPullback l R ω) := by
  obtain ⟨ω, ⟨p⟩⟩ := objectwise_normalized_fibre_pullback (k := k) l R
  let α (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme) :
      heartPull l A R g ⋙ ((ω A Y).point κ y).functor ≅
        ((ω A X).point κ (y ≫ g)).functor :=
    NatIso.ofComponents (p.component A g κ y)
      (fun f ↦ objectwise_normalized_pullback_naturality l R ω p A g κ y f)
  obtain ⟨hid, hcomp⟩ := objectwise_normalized_pullback_coherence l R ω p
  refine ⟨ω, ⟨{
    pull := α
    identity := hid
    composition := hcomp
    unit_normalization := p.unit_normalization
    local_normalization := ?_ }⟩⟩
  intro A _ _ _ X Y g F C hC N φ κ _ _ y s hs W₀ t₀ ht₀
  obtain ⟨D, f, t, i₀, hD, M, ψ, hsystem, q, η, P, h⟩ :=
    p.local_normalization A X Y g F C hC N φ κ y s hs W₀ t₀ ht₀
  let e := pullTowerIso l A f N M (eqToIso hsystem) κ t
  let Q : PullLimit l A f N M κ t e :=
    { iso := HasLimit.isoOfNatIso e
      projection := fun n ↦ HasLimit.isoOfNatIso_hom_π e (op n) }
  have hPQ : P = Q := pullLimit_unique l A f N M κ t e P Q
  refine ⟨D, f, t, i₀, hD, M, ψ, hsystem, q, η, Q, ?_⟩
  rw [hPQ] at h
  exact h

end AlgebraicGeometry.Scheme.AdicFibreComparison
