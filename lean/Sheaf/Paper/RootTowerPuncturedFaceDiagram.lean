/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.RootTowerCoordinateFace
public import Sheaf.Paper.RootTowerPunctureInvariance
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.KInjectiveComputes
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Paper.RootTowerProfiniteBaseChange
import Sheaf.Paper.CleanOpenUnitParametrizedExchange
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting
import Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.Paper.CoefficientHeartStratificationDefs
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

/-! # Normalized punctured root-tower coordinate-face diagrams

Source: latest blueprint, direct-image stability proof, paragraph (3), agent-extracted
normalized face-diagram obligation (blueprint: lem-sfb-root-tower-punctured-face-diagram).

The comparison arrows use the actual adjunction units and counit mates. Their inverses
are normalized by equality, so the compatibility statements concern specified arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PuncturedFaceDiagram
open RootCoordinateFace

/-- The commuting open/structural diagram used in the node.
Source: direct-image proof (3), q_P, f_P, a and the puncture inclusion
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
structure Diagram where
  U : Scheme.{u}
  V : Scheme.{u}
  T : Scheme.{u}
  O : Scheme.{u}
  a : V ⟶ U
  q : T ⟶ U
  f : O ⟶ V
  j : O ⟶ T
  square : j ≫ q = f ≫ a

/-- One cartesian coordinate face of the base open diagram.
Source: direct-image proof (3), U_J and V_J
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
structure Face (D : Diagram.{u}) where
  A : Scheme.{u}
  B : Scheme.{u}
  g : A ⟶ D.U
  d : B ⟶ D.V
  b : B ⟶ A
  square : d ≫ D.a = b ≫ g

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- H_P, the unpunctured total direct image.
Source: direct-image proof (3), H_P (blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
abbrev full (D : Diagram.{u}) (N : DerivedCategory (Modules Λ D.T)) := (lower Λ D.q).obj N

/-- K_P, the punctured total direct image on the outer open.
Source: direct-image proof (3), K_P (blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
abbrev punctured (D : Diagram.{u}) (N : DerivedCategory (Modules Λ D.T)) :=
  (lower Λ D.f).obj ((upper Λ D.j).obj N)

/-- The actual closed restriction followed by exact closed direct image, interpreted
in the ordinary unbounded derived category by its canonical total derived functor.
Source: direct-image proof (3), the face terms
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
abbrev faceTerm {X Z : Scheme.{u}} (g : Z ⟶ X) (K : DerivedCategory (Modules Λ X)) :=
  (lower Λ g).obj ((upper Λ g).obj K)

/-- The pushed actual open unit H_P → Ra_*K_P, with adjunction-normalized composition.
Source: direct-image proof (3), inverse of lambda_P
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def openUnit (D : Diagram.{u}) (N : DerivedCategory (Modules Λ D.T)) :
    full Λ D N ⟶ (lower Λ D.a).obj (punctured Λ D N) :=
  (lower Λ D.q).map ((adjunction Λ D.j).unit.app N) ≫
    (lowerComp Λ D.j D.q).inv.app ((upper Λ D.j).obj N) ≫
    eqToHom (congrArg (fun f ↦ (lower Λ f).obj ((upper Λ D.j).obj N)) D.square) ≫
    (lowerComp Λ D.f D.a).hom.app ((upper Λ D.j).obj N)

/-- The canonical comparison opposite to mu. It pulls the open unit to the base face,
then uses the counit mate for the open/closed square and normalized composition.
Source: direct-image proof (3), steps 3--5, before inversion
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def faceUnit (D : Diagram.{u}) (C : Face D) (N : DerivedCategory (Modules Λ D.T)) :
    faceTerm Λ C.g (full Λ D N) ⟶
      (lower Λ D.a).obj (faceTerm Λ C.d (punctured Λ D N)) :=
  (lower Λ C.g).map ((upper Λ C.g).map (openUnit Λ D N)) ≫
    (lower Λ C.g).map
      ((exchange Λ C.d C.b D.a C.g C.square).app (punctured Λ D N)) ≫
    (lowerComp Λ C.b C.g).inv.app ((upper Λ C.d).obj (punctured Λ D N)) ≫
    eqToHom (congrArg
      (fun f ↦ (lower Λ f).obj ((upper Λ C.d).obj (punctured Λ D N))) C.square.symm) ≫
    (lowerComp Λ C.d D.a).hom.app ((upper Λ C.d).obj (punctured Λ D N))

/-- The actual successive closed restriction map, formed from the smaller face's unit.
Source: direct-image proof (3), J contained in J'
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def successive {X Z Z' : Scheme.{u}} (g : Z ⟶ X) (g' : Z' ⟶ X) (k : Z' ⟶ Z)
    (w : k ≫ g = g') (K : DerivedCategory (Modules Λ X)) :
    faceTerm Λ g K ⟶ faceTerm Λ g' K :=
  (lower Λ g).map ((adjunction Λ k).unit.app ((upper Λ g).obj K)) ≫
    (lowerComp Λ k g).inv.app ((upper Λ k).obj ((upper Λ g).obj K)) ≫
    (lower Λ (k ≫ g)).map ((upperComp Λ k g).inv.app K) ≫
    eqToHom (congrArg (fun f ↦ faceTerm Λ f K) w)

/-- The normalization equation is the equation of the actual closed units, using the
inverses specified by openUnit and faceUnit.
Source: direct-image proof (3), displayed equation for mu and lambda
(blueprint: lem-sfb-root-tower-punctured-face-diagram).
Proof: paste the mates for the open/closed square. Both composites transpose to the
identity on the module restricted to the closed face of the puncture. The definitions
of lowerComp normalize composition to this same composite adjunction. Before inversion
this gives v followed by faceUnit = openUnit followed by Ra_*(u). Cancel the two
normalized isomorphisms to get the displayed equality. This is step 5 of the DAG proof. -/
theorem normalization (D : Diagram.{u}) (C : Face D)
    (N : DerivedCategory (Modules Λ D.T))
    (lam : (lower Λ D.a).obj (punctured Λ D N) ≅ full Λ D N)
    (μ : (lower Λ D.a).obj (faceTerm Λ C.d (punctured Λ D N)) ≅
      faceTerm Λ C.g (full Λ D N))
    (hlam : lam.inv = openUnit Λ D N) (hμ : μ.inv = faceUnit Λ D C N) :
    (lower Λ D.a).map ((adjunction Λ C.d).unit.app (punctured Λ D N)) ≫ μ.hom =
      lam.hom ≫ (adjunction Λ C.g).unit.app (full Λ D N) := by
  sorry

/-- Compatibility of the entire face diagram, with the actual successive closed units.
Source: direct-image proof (3), nested faces
(blueprint: lem-sfb-root-tower-punctured-face-diagram).
Proof: successive coordinate substitutions compose. Paste the two closed squares with
the open square and transpose under the composite adjunction. Both routes are the mate
of the same pulled-back identity. Naturality of the open unit and cancellation of the
normalized face isomorphisms give this equation. With normalization it is precisely the
augmented finite diagram of steps 5--6 of the DAG proof. -/
theorem nested (D : Diagram.{u}) (C C' : Face D)
    (k : C'.A ⟶ C.A) (l : C'.B ⟶ C.B)
    (wg : k ≫ C.g = C'.g) (wd : l ≫ C.d = C'.d) (wb : l ≫ C.b = C'.b ≫ k)
    (N : DerivedCategory (Modules Λ D.T))
    (μ : (lower Λ D.a).obj (faceTerm Λ C.d (punctured Λ D N)) ≅
      faceTerm Λ C.g (full Λ D N))
    (μ' : (lower Λ D.a).obj (faceTerm Λ C'.d (punctured Λ D N)) ≅
      faceTerm Λ C'.g (full Λ D N))
    (hμ : μ.inv = faceUnit Λ D C N) (hμ' : μ'.inv = faceUnit Λ D C' N) :
    (lower Λ D.a).map (successive Λ C.d C'.d l wd (punctured Λ D N)) ≫ μ'.hom =
      μ.hom ≫ successive Λ C.g C'.g k wg (full Λ D N) := by
  sorry

/-- A morphism of the actual structural/open diagrams. Such maps include parameter
restrictions, base changes, and root-tower actions on entire profinite test schemes.
Source: direct-image proof (3), naturality and equivariance
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
structure DiagramMap (D' D : Diagram.{u}) where
  u : D'.U ⟶ D.U
  v : D'.V ⟶ D.V
  t : D'.T ⟶ D.T
  o : D'.O ⟶ D.O
  a_square : v ≫ D.a = D'.a ≫ u
  q_square : t ≫ D.q = D'.q ≫ u
  f_square : o ≫ D.f = D'.f ≫ v
  j_square : o ≫ D.j = D'.j ≫ t

/-- A compatible map of the indicated coordinate faces.
Source: direct-image proof (3), face-preserving naturality
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
structure FaceMap {D' D : Diagram.{u}} (M : DiagramMap D' D) (C' : Face D') (C : Face D) where
  c : C'.A ⟶ C.A
  e : C'.B ⟶ C.B
  g_square : c ≫ C.g = C'.g ≫ M.u
  d_square : e ≫ C.d = C'.d ≫ M.v
  b_square : e ≫ C.b = C'.b ≫ c

variable {D' D : Diagram.{u}} (M : DiagramMap D' D)
  (N : DerivedCategory (Modules Λ D.T)) (N' : DerivedCategory (Modules Λ D'.T))
  (m : (upper Λ M.t).obj N ⟶ N')

/-- Restriction of the actual supplied module map to the puncture.
Source: direct-image proof (3), module and family maps
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def openModuleMap : (upper Λ M.o).obj ((upper Λ D.j).obj N) ⟶
    (upper Λ D'.j).obj N' :=
  (squareUpper Λ M.o D'.j D.j M.t M.j_square).inv.app N ≫ (upper Λ D'.j).map m

/-- The canonical map on H: exchange followed by the supplied module map.
Source: direct-image proof (3), naturality of H_P
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def fullMap : (upper Λ M.u).obj (full Λ D N) ⟶ full Λ D' N' :=
  (exchange Λ M.t D'.q D.q M.u M.q_square).app N ≫ (lower Λ D'.q).map m

/-- The canonical map on K: exchange followed by the restricted module map.
Source: direct-image proof (3), naturality of K_P
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def puncturedMap : (upper Λ M.v).obj (punctured Λ D N) ⟶ punctured Λ D' N' :=
  (exchange Λ M.o D'.f D.f M.v M.f_square).app ((upper Λ D.j).obj N) ≫
    (lower Λ D'.f).map (openModuleMap Λ M N N' m)

/-- The actual comparison on Ra_*K, retaining the entire parametrized source.
Source: direct-image proof (3), naturality of the augmented term
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def ambientMap : (upper Λ M.u).obj ((lower Λ D.a).obj (punctured Λ D N)) ⟶
    (lower Λ D'.a).obj (punctured Λ D' N') :=
  (exchange Λ M.v D'.a D.a M.u M.a_square).app (punctured Λ D N) ≫
    (lower Λ D'.a).map (puncturedMap Λ M N N' m)

/-- The actual closed-face comparison on H, using the closed counit mate.
Source: direct-image proof (3), naturality on the unpunctured face
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def fullFaceMap (C : Face D) (C' : Face D') (L : FaceMap M C' C) :
    (upper Λ M.u).obj (faceTerm Λ C.g (full Λ D N)) ⟶
      faceTerm Λ C'.g (full Λ D' N') :=
  (exchange Λ L.c C'.g C.g M.u L.g_square).app ((upper Λ C.g).obj (full Λ D N)) ≫
    (lower Λ C'.g).map
      ((squareUpper Λ L.c C'.g C.g M.u L.g_square).inv.app (full Λ D N) ≫
        (upper Λ C'.g).map (fullMap Λ M N N' m))

/-- The actual closed-face comparison on Ra_*K, using exchange on both squares.
Source: direct-image proof (3), naturality on the punctured face
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def puncturedFaceMap (C : Face D) (C' : Face D') (L : FaceMap M C' C) :
    (upper Λ M.u).obj ((lower Λ D.a).obj (faceTerm Λ C.d (punctured Λ D N))) ⟶
      (lower Λ D'.a).obj (faceTerm Λ C'.d (punctured Λ D' N')) :=
  (exchange Λ M.v D'.a D.a M.u M.a_square).app (faceTerm Λ C.d (punctured Λ D N)) ≫
    (lower Λ D'.a).map
      ((exchange Λ L.e C'.d C.d M.v L.d_square).app
          ((upper Λ C.d).obj (punctured Λ D N)) ≫
        (lower Λ C'.d).map
          ((squareUpper Λ L.e C'.d C.d M.v L.d_square).inv.app (punctured Λ D N) ≫
            (upper Λ C'.d).map (puncturedMap Λ M N N' m)))

/-- Naturality of the specified forward comparisons on the whole diagram. No hypothesis
that the geometric exchange maps are isomorphisms is needed for these squares.
Source: direct-image proof (3), parameter, module, base-change and action naturality
(blueprint: lem-sfb-root-tower-punctured-face-diagram).
Proof: unit naturality and the triangle identities give the open square. Paste the
closed exchange square with it; horizontal and vertical mate pasting give the face
square. The two routes around the commuting cube have the same pulled-back counit.
This is step 7 of the DAG proof, before inversion. For a family indexed by Q the
schemes in DiagramMap are the entire Q-parametrized terms; m is the supplied family
action. Thus this proves equality there, with no evaluation at individual points. -/
theorem forward_naturality (C : Face D) (C' : Face D') (L : FaceMap M C' C) :
    (upper Λ M.u).map (openUnit Λ D N) ≫ ambientMap Λ M N N' m =
        fullMap Λ M N N' m ≫ openUnit Λ D' N' ∧
    (upper Λ M.u).map (faceUnit Λ D C N) ≫ puncturedFaceMap Λ M N N' m C C' L =
        fullFaceMap Λ M N N' m C C' L ≫ faceUnit Λ D' C' N' := by
  sorry

/-- Naturality of lambda and mu with their uniquely fixed normalization. Applied to
maps of P, supplied module maps, pro-etale base changes and face-preserving tower
automorphisms this is every requested square, including supplied equivariant actions.
For profinite families apply the same formula on the entire Q-parametrized diagrams.
Source: direct-image proof (3), all naturality and equivariance clauses
(blueprint: lem-sfb-root-tower-punctured-face-diagram).
Proof: use forward_naturality. Substitute the four normalization equations and cancel
the invertible comparisons on either side. Functors preserve inverses, giving these
equalities. Composition and inversion therefore preserve the entire face diagram,
including its augmentation and successive restriction maps. This is step 7 of the
DAG proof. The equality already lives on the whole parametrized term. -/
theorem inverse_naturality (C : Face D) (C' : Face D') (L : FaceMap M C' C)
    (lam : (lower Λ D.a).obj (punctured Λ D N) ≅ full Λ D N)
    (lam' : (lower Λ D'.a).obj (punctured Λ D' N') ≅ full Λ D' N')
    (mu : (lower Λ D.a).obj (faceTerm Λ C.d (punctured Λ D N)) ≅
      faceTerm Λ C.g (full Λ D N))
    (mu' : (lower Λ D'.a).obj (faceTerm Λ C'.d (punctured Λ D' N')) ≅
      faceTerm Λ C'.g (full Λ D' N'))
    (hlam : lam.inv = openUnit Λ D N) (hlam' : lam'.inv = openUnit Λ D' N')
    (hmu : mu.inv = faceUnit Λ D C N) (hmu' : mu'.inv = faceUnit Λ D' C' N') :
    ambientMap Λ M N N' m ≫ lam'.hom =
        (upper Λ M.u).map lam.hom ≫ fullMap Λ M N N' m ∧
    puncturedFaceMap Λ M N N' m C C' L ≫ mu'.hom =
        (upper Λ M.u).map mu.hom ≫ fullFaceMap Λ M N N' m C C' L := by
  sorry

variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)

/-- The outer principal open D(product of outer parameters).
Source: direct-image proof (3), V (blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def outer (out : Finset (Fin r)) : (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen (∏ i ∈ out, t i)

/-- The punctured test-tower projection lands in the specified outer open.
Source: direct-image proof (3), W contained in V
(blueprint: lem-sfb-root-tower-punctured-face-diagram).
Proof: the full parameter product is invertible on the puncture, so every factor and
every subproduct is invertible there. Pullback to a profinite test preserves this.
The inverse image of D(product over out) is therefore the entire punctured test. -/
theorem punctured_range (out : Finset (Fin r)) (P : Profinite.{u}) :
    Set.range ((test (rootCoordinateOpen p t Finset.univ).toScheme P).hom ≫
      (rootCoordinateOpen p t Finset.univ).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p t)))) ⊆
        Set.range (outer t out).ι := by
  sorry

/-- The canonical punctured-tower projection to V, obtained by the open universal property.
Source: direct-image proof (3), f_P
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def puncturedProjection (out : Finset (Fin r)) (P : Profinite.{u}) :=
  IsOpenImmersion.lift (outer t out).ι
    ((test (rootCoordinateOpen p t Finset.univ).toScheme P).hom ≫
      (rootCoordinateOpen p t Finset.univ).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p t))))
    (punctured_range p t out P)

/-- The actual puncture/test projection square, needed to construct the normalized unit.
Source: direct-image proof (3), q_P j_P = a f_P
(blueprint: lem-sfb-root-tower-punctured-face-diagram).
Proof: testMap commutes with its second pullback projection. Compose with the tower
projection. The open lift factors through its target by IsOpenImmersion.lift_fac. -/
theorem diagram_square (out : Finset (Fin r)) (P : Profinite.{u}) :
    testMap (rootCoordinateOpen p t Finset.univ).ι P ≫ towerProjection p t P =
      puncturedProjection p t out P ≫ (outer t out).ι := by
  sorry

/-- The specified root-tower diagram; every structural map is constructed canonically.
Source: direct-image proof (3), the test diagram
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def rootDiagram (out : Finset (Fin r)) (P : Profinite.{u}) : Diagram.{u} where
  U := Spec (.of R)
  V := (outer t out).toScheme
  T := (test (Spec (.of (tameRootAlgebra p t))) P).left
  O := (test (rootCoordinateOpen p t Finset.univ).toScheme P).left
  a := (outer t out).ι
  q := towerProjection p t P
  f := puncturedProjection p t out P
  j := testMap (rootCoordinateOpen p t Finset.univ).ι P
  square := diagram_square p t out P

/-- U_J = Spec(R/(t_j)) and its cartesian restriction V_J over the outer open.
Source: direct-image proof (3), the coordinate faces
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def rootFace (out J : Finset (Fin r)) (P : Profinite.{u}) : Face (rootDiagram p t out P) where
  A := Spec (.of (R ⧸ baseIdeal t J))
  B := pullback (baseInclusion t J) (outer t out).ι
  g := baseInclusion t J
  d := pullback.snd _ _
  b := pullback.fst _ _
  square := (pullback.condition (f := baseInclusion t J) (g := (outer t out).ι)).symm

/-- One coefficient's nonnegative direct images and normalized comparison isomorphisms.
Source: direct-image proof (3), H_P, K_P, lambda_P and mu_(J,P)
(blueprint: lem-sfb-root-tower-punctured-face-diagram). -/
def Assertion (F : Type u) [NormedField F] : Prop :=
  ∀ (out : Finset (Fin r)), (Finset.univ \ out).Nonempty →
  ∀ (Z : Scheme.{u}) (h : Z ⟶ (outer t out).toScheme)
    [IsClosedImmersion h] [IsReduced Z],
    Set.range h = {x | (outer t out).ι x ∉
      (PrimeSpectrum.basicOpen (∏ i, t i) : (Spec (.of R)).Opens)} →
  ∀ (N : Modules (Profinite.continuousCoefficientRingObj F)
      (Spec (.of (tameRootAlgebra p t)))),
    IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj F) N →
  ∀ P : Profinite.{u},
    (full (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
      (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P)).IsGE 0 ∧
    (punctured (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
      (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P)).IsGE 0 ∧
    ∃ lam :
      (lower (Profinite.continuousCoefficientRingObj F) (outer t out).ι).obj
        (punctured (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
          (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P)) ≅
      full (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
        (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P),
      lam.inv = openUnit (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
        (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P) ∧
      ∀ (J : Finset (Fin r)), J.Nonempty → J ⊆ Finset.univ \ out →
        ∃ μ :
          (lower (Profinite.continuousCoefficientRingObj F) (outer t out).ι).obj
            (faceTerm (Profinite.continuousCoefficientRingObj F) (rootFace p t out J P).d
              (punctured (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
                (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P))) ≅
          faceTerm (Profinite.continuousCoefficientRingObj F) (rootFace p t out J P).g
            (full (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
              (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P)),
          μ.inv = faceUnit (Profinite.continuousCoefficientRingObj F) (rootDiagram p t out P)
            (rootFace p t out J P)
            (testModuleComplex (Profinite.continuousCoefficientRingObj F) N P)

/-- The normalized entire punctured coordinate-face diagram for both coefficient fields.
Source: latest blueprint direct-image proof (3), extracted normalized face diagram
(blueprint: lem-sfb-root-tower-punctured-face-diagram).

Proof: (1) Transport to Grothendieck module categories. Nonnegative injective resolutions
are K-injective, and left-exact pushforward preserves their zero negative terms.
(2) Apply puncture invariance to the outer coordinates and to all coordinates. Open-slice
pasting and its K-injective model identify their units; normalized composition makes
lambda the inverse of the pushed actual unit.
(3) On each zero-root face the restricted module stays lisse by exact pullback. Residual
SNC charts identify the remaining tower; puncture invariance on active outer coordinates
makes its specified open unit invertible. Open localization and sheaf gluing globalize it.
(4) Coordinate-face exchange is counit-normalized. Its comparisons over U and V, and the
face open-unit inverse, show that faceUnit is invertible; take mu to be its inverse.
Closed images are exact because the complementary principal opens are quasi-compact.
(5) Mate pasting proves normalization; both transposes are the same restricted identity.
(6) Successive coordinate substitutions and open units commute, giving nested.
(7) Naturality of units, exchange mates, composition and inverses gives the naturality
squares below, including entire Q-parametrized terms. Empty out yields identity outer
opens; empty charts, empty tests and rank zero are included. No boundary trivialization
or internal Hom enters. These are the seven steps of the node proof. -/
theorem rootTower_punctured_face_diagram
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (s : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, s i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({s i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type u) [CommRing R]
    (a : A →+* R) [WeaklyEtale (Spec.map (CommRingCat.ofHom a))] :
    Assertion p (fun i ↦ a (s i)) E ∧ Assertion p (fun i ↦ a (s i)) Ω := by
  sorry

end AlgebraicGeometry.ProEtale.PuncturedFaceDiagram
