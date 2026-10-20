/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
public import Sheaf.CategoryTheory.Sites.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import Sheaf.Paper.SupportedCupFunctoriality
import Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns
import Sheaf.AlgebraicGeometry.PurityRelativeCone
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Sheaf.Paper.PurityFrameIndependence
import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The canonical Kummer class of a Cartier divisor

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-divisor-class (blueprint: lem-pur-divisor-class).

The relative normalization is the published torsor-extension specification, including
its specified section off the divisor. Classes are represented by Ext, then transported
by the published supported-Hom site comparison. Heterogeneous equalities identify
the identical representations without asking the kernel to renormalize the full
localization data. The singleton range in the frame clause is equal to {f} by
Set.range_const; HEq therefore also expresses that exact support-index transport.
This is the supported cohomology of
`def-pur-support-cohomology`, via `supported_cohomology_hom`. No module structure on
G_m is used. The coefficient exponent is ell^n for every positive coefficient level n.

## Main definitions and statement

* `DivisorEtaleClasses` and `DivisorEtaleNormalized` record the relative construction.
* `DivisorLocalEquations`, `DivisorAdditive`, and `DivisorChern` spell out its compatibilities.
* `divisor_class` asserts that construction and every compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The etale representatives of divisor classes on T, indexed by actual Cartier
immersions. Source: blueprint lem-pur-divisor-class, global relative construction
(blueprint: lem-pur-divisor-class). -/
structure DivisorEtaleClasses (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) where
  /-- The etale class of each Cartier immersion. Source: blueprint relative construction
  (blueprint: lem-pur-divisor-class). -/
  classOf : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
    i.ker.IsInvertible → Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2
  /-- The same class in the published supported-Hom interface. Source: blueprint comparison
  (blueprint: lem-pur-divisor-class). -/
  homClassOf : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
    i.ker.IsInvertible → P.FunctorialCupH false i 2 1
  /-- Exact identity of the two realizations. Source: Mathlib Ext.hom and blueprint comparison
  (blueprint: lem-pur-divisor-class). -/
  realizes : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible), HEq (classOf i hI).hom (homClassOf i hI)

/-- The relative torsor Kummer normalization, in the existing extension model.
In particular the divisor section, rather than an arbitrary lift of the Picard class,
is retained. Source: blueprint lem-pur-divisor-class, second sentence
(blueprint: lem-pur-divisor-class). -/
def DivisorEtaleNormalized (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T) : Prop :=
  ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible),
    Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a) (C.classOf i hI)

/-- The actual site-comparison image of a supported etale Hom representative.
Source: blueprint lem-pur-divisor-class, coefficient map
(blueprint: lem-pur-divisor-class). -/
def divisorProEtale (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (c : P.FunctorialCupH false i 2 1) :
    P.FunctorialCupH true i 2 1 := P.functorialCupCompare i 2 1 c

/-- Both local descriptions of the fixed global relative class, for every etale
principal presentation of its support, with minus the frame boundary in the Yoneda
normalization of SupportedKummerBoundary. Source: blueprint lem-pur-divisor-class,
clause (a) and frame comparison (blueprint: lem-pur-divisor-class). -/
def DivisorLocalEquations (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  ∀ (U : Scheme.{u}) (e : U ⟶ T) [Etale e] (f : Γ(U, ⊤))
  (t : U.zeroLocusSubscheme {f} ⟶ D)
  (sq : ChosenCartesianSquare t (U.zeroLocusSubschemeι {f}) i e),
  HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (-(P.frameBoundary U (e ≫ a) f)) ∧
  HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (-(P.frameBoundaryProduct U (e ≫ a) 1 (fun _ : Fin 1 ↦ f)))

/-- Product-ideal addition in the common union support. The quantified support
inclusions are unique because s is monic. Source: blueprint lem-pur-divisor-class,
clause (b) (blueprint: lem-pur-divisor-class). -/
def DivisorAdditive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (C : P.DivisorEtaleClasses T) : Prop :=
  ∀ {D₁ D₂ Z : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (s : Z ⟶ T)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion s]
  (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
  (_hs : s.ker = i₁.ker * i₂.ker),
  ∃ (hsum : s.ker.IsInvertible) (a₁ : D₁ ⟶ Z) (a₂ : D₂ ⟶ Z)
    (ha₁ : a₁ ≫ s = i₁) (ha₂ : a₂ ≫ s = i₂),
    P.divisorProEtale s (C.homClassOf s hsum) =
      P.functorialCupChangeSupport true s i₁ a₁ ha₁ 2 1
          (P.divisorProEtale i₁ (C.homClassOf i₁ h₁)) +
        P.functorialCupChangeSupport true s i₂ a₂ ha₂ 2 1
          (P.divisorProEtale i₂ (C.homClassOf i₂ h₂))

/-- Ordinary Kummer normalization and its equality with forgetting the supported
class, through the identical site comparison. Source: blueprint lem-pur-divisor-class,
final paragraph (blueprint: lem-pur-divisor-class). -/
def DivisorChern (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  ∃ (c₁ : Abelian.Ext (P.constantEtale T) (P.frameTwistEtale T 1) 2)
    (α₁ : P.FunctorialCupOrdinaryH false T 2 1),
  HEq c₁.hom α₁ ∧
  HEq (Etale.ordinaryFiniteClass P.Coefficient T (P.frameTwistEtale T 1) 2 c₁.hom)
    (Etale.supportedKummerChern P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a)) ∧
  P.functorialCupForget true i 2 1 (P.divisorProEtale i (C.homClassOf i hI)) =
    P.functorialCupOrdinaryCompare T 2 1 α₁

/-- The canonical divisor class, its local equation, addition, and ordinary Chern class.

The existential family is uniquely fixed by the relative normalization. Its pro-etale
image is divisorProEtale, not an unspecified class or comparison. The Cartier condition
on the smooth divisor is a conclusion. The local neighbourhood is arbitrary etale,
without a quasi-compactness or open-immersion restriction. For addition, s has the
product Cartier ideal; a1 and a2 are its uniquely determined closed-support inclusions.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-divisor-class, clauses (a), (b), and final paragraph
(blueprint: lem-pur-divisor-class).

Proof, following the eight DAG steps:
1. Finite type over k makes the schemes Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Smooth-pair coordinates
   (lem-pur-smooth-pair-local-coordinates) give a regular sequence for the ideal.
   Successive dimension drops (lem-weil-pbc-dimension-quotient-nonzerodivisor)
   and the codimension-one equality make that sequence have length one.
   Thus the smooth divisor is Cartier, including the empty divisor.
2. Use the dual of the Cartier ideal as O(D), with the section dual to its inclusion
   (def-pc-divisor-line-bundle). Off D it is a frame of that invertible module.
3. The frame torsor, with this specified section, gives a global relative H1 class
   (lem-sc-line-bundle-torsor and lem-amb-relative-torsor-cohomology). Realize it
   by the extension specified in def-asd-ordinary-supported-kummer-boundary, whose
   lifting torsor over one is this frame torsor and sends its open section to zero.
4. Apply the relative connecting map, in this Yoneda extension presentation,
   of the abelian Kummer sequence at ell^n
   (lem-amb-kummer-any-base). The annihilator is available for every n>=1, without
   a ramification-divisibility condition (def-pur-conventions, sk-def-purity-conv).
5. The support and relative groups are identified by lem-pur-divisor-relative-cone
   and def-pur-support-cohomology. Realize the class by the normalized Yoneda product
   of def-asd-ordinary-supported-kummer-boundary, then apply its roots coefficient
   map and the canonical site comparison to obtain divisorProEtale. The supported-Hom
   realization and scalar adjunction make this normalization unique.
6. On an etale neighbourhood with equation f, let e be the frame 1/f of O(D).
   Its canonical section is tau=f times e. Equivariance and F(tau)=0 imply
   F(e)=-a(f). Thus the extension is the pushout of the localization sequence
   along 1 to f inverse. Its Yoneda product with the Kummer extension is
   -boundary(kappa(f)); the coefficient and site maps preserve that sign. The
   signed-cone relativeConnecting calculation in lem-pur-divisor-torsor-boundary-signs
   gives a positive cone boundary, but that cone calculation is not the Yoneda
   normalization used here. Both local clauses are therefore minus the rank-one
   frame boundary of def-pur-frame-class. Independence follows from the unchanged
   relative pair, consistently with lem-pur-frame-independence.
7. O(D1+D2)=O(D1) tensor O(D2), with the tensor of their sections. Contracted product
   adds the relative torsor classes. After restricting both complementary opens to
   the complement of their union, naturality of connecting maps and their addition
   give the asserted equality in the union support. Use
   lem-amb-relative-torsor-cohomology and
   lem-weil-pbc-complex-ses-long-exact-naturality. Locally the equation is f1*f2.
8. Forgetting the specified open section gives the ordinary frame-torsor class;
   forgetting support commutes with the Kummer connecting map
   (lem-amb-relative-torsor-cohomology). Apply the identical roots coefficient map
   and site comparison. This is the displayed ordinary Chern normalization globally,
   without testing an ordinary degree-two class only on trivializing opens. -/
theorem divisor_class (P : PurityFiniteSetting.{u}) {B T D : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) [IsSeparated b] [LocallyOfFiniteType b]
    [QuasiCompact b] (v : T ⟶ B) (d : ℕ) [SmoothOfRelativeDimension d v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ T) [IsClosedImmersion i] [Smooth (i ≫ v)]
    (hcodim : ∀ z : D, ringKrullDim (T.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞)) :
    ∃ C : P.DivisorEtaleClasses T,
      P.DivisorEtaleNormalized T (v ≫ b) C ∧
      (∀ C' : P.DivisorEtaleClasses T,
        P.DivisorEtaleNormalized T (v ≫ b) C' → C' = C) ∧
      ∃ hI : i.ker.IsInvertible,
        P.DivisorLocalEquations (v ≫ b) C i hI ∧
        P.DivisorAdditive T C ∧ P.DivisorChern (v ≫ b) C i hI := by
  sorry

/-- The relative construction exists uniquely for every Cartier divisor on T.
Source: lem-pur-divisor-class, second paragraph (blueprint: lem-pur-divisor-class).
Proof: for each Cartier immersion apply ordinary_supported_kummer at ell^n and A.
Its SupportedKummerBoundary specifies the frame torsor of the dual Cartier ideal,
with the canonical frame off the divisor sent to zero. Its uniqueness gives a
unique Ext class. Take its canonical Ext.hom as the Hom realization. Ext.hom is
injective, and HEq with that realization determines homClassOf, so these classes
assemble to a unique DivisorEtaleClasses. No smoothness is needed. -/
theorem existsUnique_generalDivisorEtaleClasses (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃! C : P.DivisorEtaleClasses T, P.DivisorEtaleNormalized T a C := by
  sorry

/-- The unique normalized etale family, retaining the relative trivialization.
Source: lem-pur-divisor-class, general construction (blueprint: lem-pur-divisor-class).
-/
def generalDivisorEtaleClasses (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] : P.DivisorEtaleClasses T :=
  (P.existsUnique_generalDivisorEtaleClasses T a).choose

/-- The general divisor class in the recorded supported-Hom realization.
This is the existing divisorProEtale construction on the uniquely normalized family.
Source: lem-pur-divisor-class, general construction (blueprint: lem-pur-divisor-class).
-/
def generalDivisorClass (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : P.FunctorialCupH true i 2 1 :=
  P.divisorProEtale i ((P.generalDivisorEtaleClasses T a).homClassOf i hI)

end WeilConjectures.PurityFiniteSetting
