/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConfigurationExteriorHom
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.CategoryTheory.Sites.OverPullbackPreservesInjectives
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # The alternating configuration spectral sequence

Source: Stacks Project, spaces-cohomology.tex, Tags 0727 and 0728,
lemma-twist and lemma-alternating-spectral-sequence
(blueprint: lem-sfb-space-alternating-sign-cohomology-spectral).

The sign line is specified by its sections: maps from the free represented sheaf
on the covering object to the constant integers, transforming by the sign character.
This is the sign subsheaf of the direct image of the constant integers. The spectral
sequence and its finite filtration live in the coefficient functor category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Constant integral coefficients, in the site's coefficient universe.
Source: Stacks Tag 0727 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationIntegers {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Global sections as additive maps from the constant integer sheaf.
Source: Stacks Tags 0725 and 0728
(blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationSections {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj (op (configurationIntegers X))

/-- The additive structure of this canonical global sections functor.
Source: Stacks Tag 0728 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
instance configurationSections_additive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (configurationSections X).Additive :=
  inferInstanceAs (preadditiveCoyoneda.obj (op (configurationIntegers X))).Additive

/-- Injective resolutions in the fixed coefficient size, without adding a size hypothesis.
Source: Stacks Tag 079H (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
instance configurationEnoughInjectives {S : Scheme.{u}} (X : AlgebraicSpace S) :
    EnoughInjectives (Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- The right derived global sections functors on abelian sheaves.
Source: Stacks Tags 01FT and 0728
(blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationCohomology {S : Scheme.{u}} (X : AlgebraicSpace S) (q : ℕ) :
    Sheaf X.etaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (configurationSections X).rightDerived q

/-- Étale inverse image is restriction along the existing small-site inclusion.
Source: Stacks Tag 0728 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationRestriction {S : Scheme.{u}} {Q X : AlgebraicSpace S}
    (g : Q ⟶ X) (hg : IsEtale g.hom.hom) :
    Sheaf X.etaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Q.etaleTopology AddCommGrpCat.{u + 1} :=
  letI := etaleMap_isContinuous g hg
  (etaleMap g hg).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    Q.etaleTopology X.etaleTopology

/-- Tensor with a fixed abelian sheaf: sectionwise integral tensor, then sheafification.
Source: Stacks Tags 03EK and 0728
(blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationTwist {S : Scheme.{u}} (Q : AlgebraicSpace S)
    (L : Sheaf Q.etaleTopology AddCommGrpCat.{u + 1}) :
    Sheaf Q.etaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Q.etaleTopology AddCommGrpCat.{u + 1} :=
  sheafToPresheaf Q.etaleTopology AddCommGrpCat.{u + 1} ⋙
    tensorRight L.obj ⋙ presheafToSheaf Q.etaleTopology AddCommGrpCat.{u + 1}

/-- The map on the already defined free represented sheaf induced by an object map.
Source: Stacks Tag 0726 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationFreeMap {S : Scheme.{u}} (Q : AlgebraicSpace S)
    {W V : Q.EtaleSite} (a : W ⟶ V) :
    configurationFreeSheaf Q W ⟶ configurationFreeSheaf Q V :=
  (presheafToSheaf Q.etaleTopology AddCommGrpCat.{u + 1}).map
    (Functor.whiskerRight (uliftYoneda.{u + 1}.map a) AddCommGrpCat.free)

/-- Sign-transforming sections of the direct image of the constant integers, expressed
by the free represented sheaf adjunction on every localized site.
Source: Stacks Tag 0727 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationSignSections {S : Scheme.{u}} (Q : AlgebraicSpace S)
    (W : Q.EtaleSite) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* Aut W) (V : Q.EtaleSite) :
    AddSubgroup (((Over.forget V).op ⋙ (configurationFreeSheaf Q W).obj) ⟶
      ((Over.forget V).op ⋙ (configurationIntegers Q).obj)) where
  carrier := {φ | ∀ σ : Equiv.Perm (Fin n),
    Functor.whiskerLeft (Over.forget V).op (configurationFreeMap Q (ρ σ).hom).hom ≫ φ =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • φ)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb σ
    simp only [Preadditive.comp_add, ha σ, hb σ, smul_add]
  neg_mem' := by
    intro a ha σ
    simp only [Preadditive.comp_neg, ha σ, smul_neg]

/-- The sign subsheaf, including compatibility of its section description with restriction
and its trivialization on the torsor. Surjectivity of the torsor makes this rank one locally.
Source: Stacks Tag 0727 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def IsConfigurationSignLine {S : Scheme.{u}} (Q : AlgebraicSpace S)
    (W : Q.EtaleSite) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* Aut W)
    (L : Sheaf Q.etaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  (∃ e : ∀ V : Q.EtaleSite, L.obj.obj (op V) ≃+ configurationSignSections Q W n ρ V,
    ∀ (V V' : Q.EtaleSite) (a : V' ⟶ V) (s : L.obj.obj (op V)),
      (e V' (L.obj.map a.op s)).val =
        Functor.whiskerLeft (Over.map a).op (e V s).val) ∧
    Nonempty (L.over W ≅ (configurationIntegers Q).over W)

/-- The orbit presheaf, as the pointwise coequalizer of all permutations and projection.
Source: Stacks Tag 0728 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationOrbitPresheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (W : X.EtaleSite) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* Aut W) :
    (Over S)ᵒᵖ ⥤ Type u :=
  coequalizer
    (Sigma.desc (fun σ : Equiv.Perm (Fin n) ↦ yoneda.map (ρ σ).hom.hom.left))
    (Sigma.desc (fun _ : Equiv.Perm (Fin n) ↦ 𝟙 (yoneda.obj W.obj.left)))

/-- The canonical arrow from the covering scheme to its orbit presheaf.
Source: Stacks Tag 0728 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def configurationOrbitMap {S : Scheme.{u}} (X : AlgebraicSpace S)
    (W : X.EtaleSite) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* Aut W) :
    yoneda.obj W.obj.left ⟶ configurationOrbitPresheaf X W n ρ :=
  coequalizer.π _ _

/-- An étale torsor for the constant permutation group: two lifts of the same section
are related by a unique permutation étale locally. Empty tests impose no uniqueness.
Source: Stacks Tags 0727 and 0728
(blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
def IsConfigurationTorsor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (W : X.EtaleSite) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* Aut W)
    (Q : AlgebraicSpace S) (π : yoneda.obj W.obj.left ⟶ Q.obj.obj) : Prop :=
  ∀ (T : Over S) (a b : T ⟶ W.obj.left),
    π.app (op T) a = π.app (op T) b →
      ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over S) T ∧
        ∀ (V : Over S) (h : V ⟶ T), R h → Nonempty V.left →
          ∃! σ : Equiv.Perm (Fin n), h ≫ a ≫ (ρ σ).hom.hom.left = h ≫ b

/-- The configuration scheme, its free permutation action, and the algebraic-space orbit
quotient. The unit's universal property specifies fppf sheafification, including its map.
The covering chart over the quotient is identified with the original configuration scheme.
Source: Stacks Tag 0728 (blueprint: lem-sfb-space-alternating-sign-cohomology-spectral). -/
structure ConfigurationQuotient {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : X.EtaleSite) (p : ℕ) where
  /-- The nonempty iterated fibre product over X. -/
  T : X.EtaleSite
  /-- The ordered projections. -/
  pr : Fin (p + 1) → (T ⟶ U)
  /-- Its universal property in the small étale site. -/
  product : Nonempty (IsLimit (Fan.mk T pr))
  /-- The distinct-tuple locus. -/
  W : X.EtaleSite
  /-- Its inclusion into the product. -/
  j : W ⟶ T
  /-- The coordinate-permutation action. -/
  ρ : Equiv.Perm (Fin (p + 1)) →* Aut W
  /-- The distinct locus is open. -/
  openImmersion : IsOpenImmersion (X.etaleForget.map j)
  /-- The distinct locus is closed. -/
  closedImmersion : IsClosedImmersion (X.etaleForget.map j)
  /-- Exactly the complement of the pairwise equality loci. -/
  distinct : Set.range (X.etaleForget.map j).base =
    configurationDistinctSet X U T (p + 1) pr
  /-- The action is the specified permutation of coordinates. -/
  coordinates : ∀ (σ : Equiv.Perm (Fin (p + 1))) (i : Fin (p + 1)),
    (ρ σ).hom ≫ j ≫ pr i = j ≫ pr (σ.symm i)
  /-- Freeness, including scheme-valued tests, rather than only geometric points. -/
  free : ∀ (V : Scheme.{u}) (a : V ⟶ X.etaleForget.obj W)
    (σ : Equiv.Perm (Fin (p + 1))), Nonempty V →
      a ≫ X.etaleForget.map (ρ σ).hom = a → σ = 1
  /-- The quotient is an algebraic space over S. -/
  Q : AlgebraicSpace S
  /-- The fppf sheafification unit of the orbit presheaf. -/
  η : configurationOrbitPresheaf X W (p + 1) ρ ⟶ Q.obj.obj
  /-- The full universal property of that sheafification. -/
  sheafification : ∀ F : Sheaf (Scheme.fppfTopology.over S) (Type u),
    Function.Bijective (fun h : Q.obj.obj ⟶ F.obj ↦ η ≫ h)
  /-- The canonical quotient arrow is representable étale. -/
  quotientEtale : IsEtale (configurationOrbitMap X W (p + 1) ρ ≫ η)
  /-- The canonical quotient arrow is representable surjective. -/
  quotientSurjective : IsSurjective (configurationOrbitMap X W (p + 1) ρ ≫ η)
  /-- The quotient arrow is a torsor for the constant permutation group. -/
  torsor : IsConfigurationTorsor X W (p + 1) ρ Q
    (configurationOrbitMap X W (p + 1) ρ ≫ η)
  /-- The same covering scheme viewed on the small site of the quotient. -/
  chart : Q.EtaleSite
  /-- The identification of the two underlying schemes over S. -/
  chartIso : chart.obj.left ≅ W.obj.left
  /-- It identifies the chart map with the canonical quotient arrow. -/
  chartMap : chart.obj.hom =
    yoneda.map chartIso.hom ≫ configurationOrbitMap X W (p + 1) ρ ≫ η
  /-- The permutation action on the chart over Q. -/
  chartAction : Equiv.Perm (Fin (p + 1)) →* Aut chart
  /-- The transported action is precisely the coordinate action. -/
  chartAction_eq : ∀ σ : Equiv.Perm (Fin (p + 1)),
    (chartAction σ).hom.hom.left ≫ chartIso.hom = chartIso.hom ≫ (ρ σ).hom.hom.left
  /-- The induced map from the quotient to X. -/
  g : Q ⟶ X
  /-- This induced map is étale. -/
  gEtale : IsEtale g.hom.hom
  /-- The induced map is the descent of the configuration map to X. -/
  triangle : (configurationOrbitMap X W (p + 1) ρ ≫ η) ≫ g.hom.hom = W.obj.hom

/-- The natural integral alternating configuration spectral sequence, including the
quotient geometry, sign lines, stabilization, and finite natural abutment filtrations.
Source: Stacks Project, spaces-cohomology.tex, Tags 0727 and 0728
(blueprint: lem-sfb-space-alternating-sign-cohomology-spectral).

Proof:
1. Apply lem-sfb-etale-cover-trace-koszul-resolution to the free sheaf Z[U/X].
   The contraction augments its exterior powers to an exact resolution of Z.
   Lemma lem-sfb-etale-configuration-exterior-hom gives the clopen distinct loci,
   their free coordinate actions, and Hom from an exterior power as sign sections.
2. Form the action relation as the finite scheme coproduct indexed by permutations
   (lem-weil-pbc-scheme-coproduct-family). Its two projections are étale and its
   map into W times W is monic by freeness. Lemma lem-trf-etale-relation-quotient
   constructs its algebraic-space quotient. Its relation classes are the orbit
   classes locally on the finite clopen decomposition of a test scheme, so their
   fppf sheafifications agree. The kernel pair identifies the map as a torsor.
   Lemma lem-trf-space-etale-source-atlas-detection descends étaleness to g.
3. Lemma lem-sfb-finite-torsor-character-line gives the sign subsheaf of pi_* Z,
   its rank one and trivialization on W, and L tensor L isomorphic to Z.
   Its section formula and the exterior Hom identification agree naturally in
   every coefficient sheaf. The site comparison of
   lem-trf-space-enlarged-etale-ringed-site-model identifies all restrictions.
4. Choose injective resolutions using lem-weil-pbc-site-sheaves-enough-injectives.
   Restriction along g preserves injectives by new-over-pullback-preserves-injectives
   on the enlarged site. Transport by lem-weil-pbc-equivalence-injective-resolutions
   to the small sites and then through the exact equivalence tensor L.
5. Form D^(p,q) = Hom(exterior^(p+1) Z[U/X], I^q), with precomposition horizontally
   and postcomposition vertically. The differentials commute; use the total sign
   of def-sp-double-complex-total. Its column cohomology is the displayed twisted
   cohomology by def-sp-left-exact-additive and def-weil-pbc-sites-and-cohomology.
6. The extension property in def-sp-injective-resolutions makes Hom(-, I^q) exact
   on the augmented exterior resolution. Thus row cohomology is Gamma(X,I^q)
   in horizontal degree zero and vanishes in positive horizontal degrees.
7. Apply thm-sp-double-complex-spectral-sequences. The row sequence degenerates
   and identifies total cohomology with H^*(X,A). The column sequence has the
   asserted E1 page. First-quadrant convergence gives stabilization and the finite
   filtration, top at zero and bottom at m+1, with the stated stable graded pieces.
8. Maps of resolutions exist by lem-weil-pbc-injective-resolution-lift-exists and
   are homotopic by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy. Column
   homotopies give the same E1 map; total homotopies use the sign (-1)^p so cross
   terms cancel. Hence pages, filtration, and abutment are natural and independent
   of resolution. No group order or factorial was inverted. -/
theorem space_alternating_sign_cohomology_spectral {S : Scheme.{u}}
    (X : AlgebraicSpace S) (U : X.EtaleSite) (hsurj : IsSurjective U.obj.hom)
    (hsep : IsSeparatedPresheafMap U.obj.hom) :
    ∃ (D : ∀ p : ℕ, ConfigurationQuotient X U p)
      (L : ∀ p : ℕ, Sheaf (D p).Q.etaleTopology AddCommGrpCat.{u + 1}),
      (∀ p : ℕ, IsConfigurationSignLine (D p).Q (D p).chart (p + 1)
        (D p).chartAction (L p)) ∧
      ∃ (E : CohomologicalSpectralSequenceNat.{u + 2, u + 2}
          (Sheaf X.etaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) 1),
        (∀ p q : ℕ, Nonempty ((E.page 1 (by decide)).X (p, q) ≅
          configurationRestriction (D p).g (D p).gEtale ⋙
            configurationTwist (D p).Q (L p) ⋙ configurationCohomology (D p).Q q)) ∧
        ∃ F : ∀ m : ℕ, DecreasingFiltration (configurationCohomology X m),
          (∀ m : ℕ, IsIso ((F m).step 0).arrow ∧
            IsZero ((F m).step (m + 1) :
              Sheaf X.etaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})) ∧
          (∀ p q : ℕ, Nonempty ((F (p + q)).gr (p : ℤ) ≅
            (E.page ((p + q + 2 : ℕ) : ℤ) (by omega)).X (p, q))) ∧
          (∀ (p q : ℕ) (r : ℤ) (hr : 1 ≤ r),
            max (p : ℤ) ((q : ℤ) + 1) < r →
              Nonempty ((E.page r hr).X (p, q) ≅
                (E.page ((p + q + 2 : ℕ) : ℤ) (by omega)).X (p, q))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
