/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.RingTheory.StrictHenselizationPresentationIn

/-!
# Full parameter-root algebras

Source: blueprint main-20261015, ctf-stability direct-images proof (3), tame-boundary
expansion (blueprint: def-sfb-full-parameter-root-tower).

The presentation has a variable for every positive prime-to-p order and every parameter.
Its second family of relations is exactly the power transition for divisibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The actual compatible-root algebra. This is the presentation of the filtered colimit
of the finite root algebras, rather than a choice of a ring admitting some roots.
Source: tame-boundary expansion, root-tower formula
(blueprint: def-sfb-full-parameter-root-tower). -/
abbrev FullParameterRootAlgebra (p : ℕ) {J : Type u} [Fintype J] {R : Type u} [CommRing R]
    (t : J → R) :=
  tameRootAlgebra p (fun i : Fin (Fintype.card J) ↦ t ((Fintype.equivFin J).symm i))

/-- The specified root at order n. Source: tame-boundary expansion, root-tower formula
(blueprint: def-sfb-full-parameter-root-tower). -/
def fullParameterRoot (p : ℕ) {J : Type u} [Fintype J] {R : Type u} [CommRing R] (t : J → R)
    (n : TameRootOrder p) (i : J) : FullParameterRootAlgebra p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X ((Fintype.equivFin J) i, n))

/-- Structural map of the full tower over an affine scheme.
Source: tame-boundary expansion, root-tower formula
(blueprint: def-sfb-full-parameter-root-tower). -/
def fullParameterRootMap (p : ℕ) {J : Type u} [Fintype J] (U : Scheme.{u}) [IsAffine U]
    (t : J → Γ(U, ⊤)) : Spec (.of (FullParameterRootAlgebra p t)) ⟶ U :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) (FullParameterRootAlgebra p t))) ≫
    U.isoSpec.inv

/-- The specified root as a global section of the tower.
Source: tame-boundary expansion, root-tower formula
(blueprint: def-sfb-full-parameter-root-tower). -/
def fullParameterRootSection (p : ℕ) {J : Type u} [Fintype J] {R : Type u} [CommRing R]
    (t : J → R) (n : TameRootOrder p) (i : J) :
    Γ(Spec (.of (FullParameterRootAlgebra p t)), ⊤) :=
  (Scheme.ΓSpecIso (.of (FullParameterRootAlgebra p t))).inv (fullParameterRoot p t n i)

/-- The full tame inertia group, with its product topology; multiplicative notation denotes
addition in each q-adic factor. Source: tame-boundary expansion, displayed G_I
(blueprint: def-sfb-full-parameter-root-tower). -/
abbrev ParameterRootDeckGroup (p : ℕ) (J : Type u) :=
  Multiplicative (J → (q : {q : ℕ // q.Prime ∧ q ≠ p}) →
    @PadicInt q.val ⟨q.property.1⟩)

/-- The diagonal integral vector, used to normalize all finite residue characters.
Source: tame-boundary expansion, compatible Chinese-remainder identification
(blueprint: def-sfb-full-parameter-root-tower). -/
def parameterRootDeckInteger (p : ℕ) {J : Type u} (a : J → ℤ) :
    ParameterRootDeckGroup p J :=
  Multiplicative.ofAdd (fun i _ ↦ (a i : _))

/-- Compatible primitive roots and the standard finite residue characters of the tame group.
Continuity and the integral-vector normalization uniquely specify the characters.
Source: tame-boundary expansion, root rotations and Chinese remainders
(blueprint: def-sfb-full-parameter-root-tower). -/
structure ParameterRootCharacters (p : ℕ) (J : Type u) (R : Type u) [CommRing R] where
  roots : TameRootOrder p → R
  primitive : ∀ n, IsPrimitiveRoot (roots n) n.val
  compatible : ∀ n m, n.val ∣ m.val → roots m ^ (m.val / n.val) = roots n
  residue : ∀ n : TameRootOrder p,
    ParameterRootDeckGroup p J →* Multiplicative (J → ZMod n.val)
  continuous_residue : ∀ n, Continuous (residue n)
  integer_residue : ∀ n (a : J → ℤ) i,
    (residue n (parameterRootDeckInteger p a)).toAdd i = (a i : ZMod n.val)

/-- The open chart base removing the components outside I.
Source: tame-boundary expansion, definition of S_I
(blueprint: def-sfb-full-parameter-root-tower). -/
def parameterStratumOpen {Y : Scheme.{u}} {A : Type u} [Finite A]
    (C : A → Y.IdealSheafData) (I : Finset A) : Y.Opens :=
  letI := Fintype.ofFinite A
  sncStratumOpen (fun j ↦ C ((Fintype.equivFin A).symm j))
    (I.map (Fintype.equivFin A).toEmbedding)

/-- The reduced stratum as the open part of the reduced intersection.
Source: tame-boundary expansion, S_I
(blueprint: def-sfb-full-parameter-root-tower). -/
abbrev ParameterStratum {Y : Scheme.{u}} {A : Type u} [Finite A]
    (C : A → Y.IdealSheafData) (I : Finset A) :=
  letI := Fintype.ofFinite A
  (sncStratumIdeal (fun j ↦ C ((Fintype.equivFin A).symm j))
    (I.map (Fintype.equivFin A).toEmbedding)).subscheme

/-- Inclusion of the reduced stratum in Y.
Source: tame-boundary expansion, S_I
(blueprint: def-sfb-full-parameter-root-tower). -/
def parameterStratumInclusion {Y : Scheme.{u}} {A : Type u} [Finite A]
    (C : A → Y.IdealSheafData) (I : Finset A) : ParameterStratum C I ⟶ Y :=
  letI := Fintype.ofFinite A
  (sncStratumIdeal (fun j ↦ C ((Fintype.equivFin A).symm j))
    (I.map (Fintype.equivFin A).toEmbedding)).subschemeι ≫ (parameterStratumOpen C I).ι

/-- Parameters cut out the specified component ideals scheme-theoretically.
Source: tame-boundary expansion, equations t_i
(blueprint: def-sfb-full-parameter-root-tower). -/
def IsBoundaryParameterFamily {Y U : Scheme.{u}} {J : Type u} [Fintype J]
    (C : J → Y.IdealSheafData) (f : U ⟶ Y) (t : J → Γ(U, ⊤)) : Prop :=
  ∀ i, (C i).comap f = Scheme.IdealSheafData.ofIdealTop (Ideal.span {t i})

end AlgebraicGeometry.ProEtale
