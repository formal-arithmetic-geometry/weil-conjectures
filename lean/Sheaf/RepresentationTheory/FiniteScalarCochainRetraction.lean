module

public import Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Algebra.Tower

/-!
# Scalar retractions on finite-coordinate continuous cochains

Source: latest blueprint, six-functors basics, direct-images proof paragraph (3),
agent-written scalar-retraction expansion; Stacks Project Tag 0DVG supplies the
continuous cochain convention.
(blueprint: lem-sfb-finite-scalar-cochain-retraction).

The helper structure records the maps of the already specified cochain complexes.
Its evaluation formulas prescribe postcomposition, rather than arbitrary split maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w' t r

open CategoryTheory

namespace ContinuousCohomology

/-- The six postcomposition cochain maps associated to a scalar retraction, with
both coordinate squares, splitting identities, and the cocycle and vanishing clauses.
Being morphisms of complexes includes all six differential identities.
Source: blueprint direct-images proof (3), agent scalar-retraction expansion;
Stacks Tag 0DVG for the differential convention.
(blueprint: lem-sfb-finite-scalar-cochain-retraction). -/
structure ScalarCochainRetraction
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (W : Type w') [AddCommGroup W] [Module E W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul E W]
    (ρV : G →* V ≃ₗ[E] V) (ρW : G →* W ≃ₗ[E] W)
    (i : V →L[E] W) (p : W →L[E] V) (q : W →L[E] W)
    [HasDerivedCategory.{r} (ModuleCat.{t} E)]
    (BV CV BW CW : CochainComplex (ModuleCat.{t} E) ℤ)
    (DV : JointContinuousCochainCoordinates E G V ρV BV CV)
    (DW : JointContinuousCochainCoordinates E G W ρW BW CW) where
  /-- Homogeneous projection. -/
  bP : BW ⟶ BV
  /-- Homogeneous inclusion. -/
  bI : BV ⟶ BW
  /-- Homogeneous complementary projection. -/
  bQ : BW ⟶ BW
  /-- Inhomogeneous projection. -/
  cP : CW ⟶ CV
  /-- Inhomogeneous inclusion. -/
  cI : CV ⟶ CW
  /-- Inhomogeneous complementary projection. -/
  cQ : CW ⟶ CW
  /-- bP is postcomposition by the specified coefficient map. -/
  bP_eval : ∀ (n : ℕ) (c : BW.X (n : ℤ))
      (x : Fin (n + 1) → G),
    DV.bEval n ((bP.f (n : ℤ)).hom c) x = p (DW.bEval n c x)
  /-- bI is postcomposition by the specified coefficient map. -/
  bI_eval : ∀ (n : ℕ) (c : BV.X (n : ℤ))
      (x : Fin (n + 1) → G),
    DW.bEval n ((bI.f (n : ℤ)).hom c) x = i (DV.bEval n c x)
  /-- bQ is postcomposition by the specified coefficient map. -/
  bQ_eval : ∀ (n : ℕ) (c : BW.X (n : ℤ))
      (x : Fin (n + 1) → G),
    DW.bEval n ((bQ.f (n : ℤ)).hom c) x = q (DW.bEval n c x)
  /-- cP is postcomposition by the specified coefficient map. -/
  cP_eval : ∀ (n : ℕ) (c : CW.X (n : ℤ))
      (x : Fin (n) → G),
    DV.cEval n ((cP.f (n : ℤ)).hom c) x = p (DW.cEval n c x)
  /-- cI is postcomposition by the specified coefficient map. -/
  cI_eval : ∀ (n : ℕ) (c : CV.X (n : ℤ))
      (x : Fin (n) → G),
    DW.cEval n ((cI.f (n : ℤ)).hom c) x = i (DV.cEval n c x)
  /-- cQ is postcomposition by the specified coefficient map. -/
  cQ_eval : ∀ (n : ℕ) (c : CW.X (n : ℤ))
      (x : Fin (n) → G),
    DW.cEval n ((cQ.f (n : ℤ)).hom c) x = q (DW.cEval n c x)
  /-- The projection retracts the inclusion. -/
  b_retract : bI ≫ bP = 𝟙 _
  /-- The complementary projection is one minus inclusion followed by projection. -/
  b_complement : bQ = 𝟙 _ - bP ≫ bI
  /-- The projection retracts the inclusion. -/
  c_retract : cI ≫ cP = 𝟙 _
  /-- The complementary projection is one minus inclusion followed by projection. -/
  c_complement : cQ = 𝟙 _ - cP ≫ cI
  /-- Compatibility of P with Phi. -/
  phi_P : DW.iso.hom ≫ cP = bP ≫ DV.iso.hom
  /-- Compatibility of P with Psi. -/
  psi_P : DW.iso.inv ≫ bP = cP ≫ DV.iso.inv
  /-- Compatibility of I with Phi. -/
  phi_I : DV.iso.hom ≫ cI = bI ≫ DW.iso.hom
  /-- Compatibility of I with Psi. -/
  psi_I : DV.iso.inv ≫ bI = cI ≫ DW.iso.inv
  /-- Compatibility of Q with Phi. -/
  phi_Q : DW.iso.hom ≫ cQ = bQ ≫ DW.iso.hom
  /-- Compatibility of Q with Psi. -/
  psi_Q : DW.iso.inv ≫ bQ = cQ ≫ DW.iso.inv
  /-- Homogeneous cocycles remain cocycles under P. -/
  cocycle_P : ∀ (n : ℕ) (c : BW.X (n : ℤ)),
    (BW.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom c = 0 →
      (BV.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom
        ((bP.f (n : ℤ)).hom c) = 0
  /-- Homogeneous cocycles remain cocycles under Q. -/
  cocycle_Q : ∀ (n : ℕ) (c : BW.X (n : ℤ)),
    (BW.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom c = 0 →
      (BW.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom
        ((bQ.f (n : ℤ)).hom c) = 0
  /-- Vanishing on any subset on which the original cochain is F-valued. -/
  vanishing : ∀ (n : ℕ) (c : BW.X (n : ℤ)) (S : Set (Fin (n + 1) → G)),
    (∀ x ∈ S, ∃ y : V, DW.bEval n c x = i y) →
      ∀ x ∈ S, DW.bEval n ((bQ.f (n : ℤ)).hom c) x = 0

/-- A continuous E-linear retraction of fields extends coordinatewise and induces
split maps on both continuous cochain complexes, naturally for every subgroup.
The action formulas specify the original E-matrices included in F and L. The
ContinuousSMul assumptions encode continuity of E's inclusions: over topological
fields this is equivalent to continuity of their algebra maps (evaluate at 1
in one direction and multiply in the other). The tower gives the composite E to L.

Source: latest blueprint direct-images proof (3), agent-written scalar-retraction
expansion, and Stacks Tag 0DVG for the cochain convention.
(blueprint: lem-sfb-finite-scalar-cochain-retraction).

Proof: (1) Each matrix entry is continuous by evaluating the given action on a
standard basis vector. Include these entries in F or L and take finite sums of
products. The resulting actions are jointly continuous; the matrix action laws
and inverses are preserved by the field inclusions. This also gives the usual
continuous vector-space operations. (2) Coordinate inclusion and coordinatewise p
are continuous E-linear maps. Their difference q = 1 - i p is continuous E-linear.
E-linearity of p commutes with every E-valued matrix, proving equivariance of p;
the same calculation proves that of i and q. Since p fixes F, p i = 1 and q i = 0.
(3) Apply lem-sfb-joint-continuous-coordinate-naturality to p, i, q and the identity
group map. Postcomposition preserves the specified evaluation images, commutes
with both differentials and with Phi and Psi, including degree zero.
(4) Evaluate on every tuple: p i = 1 gives the two cochain retractions, and
q = 1 - i p gives their complementary projections. Evaluation injectivity makes
these identities of cochain maps. Negative degrees have their unique zero maps.
(5) For every subgroup, precompose with its continuous inclusion in every
argument. This commutes with all three coefficient maps, in both conventions.
The restricted action is jointly continuous by composition with inclusion times
identity. Differential compatibility carries cocycles to cocycles; q i = 0
proves vanishing wherever the original cocycle is F-valued.
(6) For d = 0 every vector space is zero and the formulas remain valid. Empty
inhomogeneous tuples give degree zero, with d(v)(g) = gv - v. Only continuity,
E-linearity and p's identity on F are used, without multiplicativity or completeness. -/
theorem exists_finiteScalarCochainRetraction
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (F : Type w) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (L : Type w') [Field L] [TopologicalSpace L] [IsTopologicalDivisionRing L]
    [Algebra E F] [Algebra F L] [Algebra E L] [IsScalarTower E F L]
    [ContinuousSMul E F] [ContinuousSMul E L]
    (hFL : Continuous (algebraMap F L)) (p : L →L[E] F)
    (hp : ∀ a : F, p (algebraMap F L a) = a)
    (d : ℕ) (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* (Fin d → E) ≃ₗ[E] (Fin d → E))
    (hρ : Continuous (fun z : G × (Fin d → E) ↦ ρ z.1 z.2))
    [HasDerivedCategory.{r} (ModuleCat.{max v w w' t} E)] :
    ∃ (ρF : G →* (Fin d → F) ≃ₗ[E] (Fin d → F))
      (ρL : G →* (Fin d → L) ≃ₗ[E] (Fin d → L))
      (i : (Fin d → F) →L[E] (Fin d → L))
      (P : (Fin d → L) →L[E] (Fin d → F))
      (Q : (Fin d → L) →L[E] (Fin d → L)),
      (∀ (g : G) (x : Fin d → F) (a : Fin d),
        ρF g x a = ∑ b : Fin d, algebraMap E F (ρ g (Pi.single b 1) a) * x b) ∧
      (∀ (g : G) (x : Fin d → L) (a : Fin d),
        ρL g x a = ∑ b : Fin d, algebraMap E L (ρ g (Pi.single b 1) a) * x b) ∧
      Continuous (fun z : G × (Fin d → F) ↦ ρF z.1 z.2) ∧
      Continuous (fun z : G × (Fin d → L) ↦ ρL z.1 z.2) ∧
      (∀ (x : Fin d → F) (a : Fin d), i x a = algebraMap F L (x a)) ∧
      (∀ (x : Fin d → L) (a : Fin d), P x a = p (x a)) ∧
      Q = ContinuousLinearMap.id E (Fin d → L) - i.comp P ∧
      (∀ (g : G) (x : Fin d → F), i (ρF g x) = ρL g (i x)) ∧
      (∀ (g : G) (x : Fin d → L), P (ρL g x) = ρF g (P x)) ∧
      (∀ (g : G) (x : Fin d → L), Q (ρL g x) = ρL g (Q x)) ∧
      P.comp i = ContinuousLinearMap.id E (Fin d → F) ∧ Q.comp i = 0 ∧
      ∀ (BF CF BL CL : CochainComplex (ModuleCat.{max v w w' t} E) ℤ)
        (DF : JointContinuousCochainCoordinates E G (Fin d → F) ρF BF CF)
        (DL : JointContinuousCochainCoordinates E G (Fin d → L) ρL BL CL),
        ∃ R : ScalarCochainRetraction E G (Fin d → F) (Fin d → L)
            ρF ρL i P Q BF CF BL CL DF DL,
          ∀ (H : Subgroup G)
            (BF' CF' BL' CL' : CochainComplex (ModuleCat.{max v w w' t} E) ℤ)
            (DF' : JointContinuousCochainCoordinates E H (Fin d → F)
              (ρF.comp H.subtype) BF' CF')
            (DL' : JointContinuousCochainCoordinates E H (Fin d → L)
              (ρL.comp H.subtype) BL' CL'),
            Continuous (fun z : H × (Fin d → F) ↦ ρF (z.1 : G) z.2) ∧
            Continuous (fun z : H × (Fin d → L) ↦ ρL (z.1 : G) z.2) ∧
            ∃ (R' : ScalarCochainRetraction E H (Fin d → F) (Fin d → L)
                (ρF.comp H.subtype) (ρL.comp H.subtype) i P Q
                BF' CF' BL' CL' DF' DL')
              (bF : BF ⟶ BF') (cF : CF ⟶ CF') (bL : BL ⟶ BL') (cL : CL ⟶ CL'),
              (∀ (n : ℕ) (c : BF.X (n : ℤ)) (x : Fin (n + 1) → H),
                DF'.bEval n ((bF.f (n : ℤ)).hom c) x =
                  DF.bEval n c (fun a ↦ (x a : G))) ∧
              (∀ (n : ℕ) (c : BL.X (n : ℤ)) (x : Fin (n + 1) → H),
                DL'.bEval n ((bL.f (n : ℤ)).hom c) x =
                  DL.bEval n c (fun a ↦ (x a : G))) ∧
              (∀ (n : ℕ) (c : CF.X (n : ℤ)) (x : Fin (n) → H),
                DF'.cEval n ((cF.f (n : ℤ)).hom c) x =
                  DF.cEval n c (fun a ↦ (x a : G))) ∧
              (∀ (n : ℕ) (c : CL.X (n : ℤ)) (x : Fin (n) → H),
                DL'.cEval n ((cL.f (n : ℤ)).hom c) x =
                  DL.cEval n c (fun a ↦ (x a : G))) ∧
              R.bP ≫ bF = bL ≫ R'.bP ∧
              R.bI ≫ bL = bF ≫ R'.bI ∧
              R.bQ ≫ bL = bL ≫ R'.bQ ∧
              R.cP ≫ cF = cL ≫ R'.cP ∧
              R.cI ≫ cL = cF ≫ R'.cI ∧
              R.cQ ≫ cL = cL ≫ R'.cQ := by
  sorry

end ContinuousCohomology
