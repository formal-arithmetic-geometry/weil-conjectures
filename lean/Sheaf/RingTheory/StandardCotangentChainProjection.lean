/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The standard cotangent chain projection

Source: Stacks Project, Cotangent Complex, Tags 08UP
(remark-explicit-comparison-map) and 08QL (section-functoriality)
(blueprint: lem-trf-standard-cotangent-chain-projection).

The conormal module is Mathlib's actual augmentation kernel modulo its square.
The two-term target is specified by coordinate isomorphisms and its differential,
not by a choice of an unspecified object. The projection is characterized on tensors.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Algebra.CotangentResolution.StandardProjection

/-- Polynomial coordinates of the recorded standard resolution. Source: Stacks,
Tags 08PM and 08UP (blueprint: lem-trf-standard-cotangent-chain-projection). -/
def coordinates
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) (n : ℕ) :
    (C.standard f).algebra.obj (op ⦋n⦌) ≅ standardTerm f n :=
  eqToIso ((C.standard_spec f).1 n)

/-- The coordinate identification of a term of the alternating complex with its
actual tensor module. Source: Stacks, Tag 08PN
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
def degreeIso {f : Arrow CommRingCat.{u}} {P : Augmentation f}
    (D : DifferentialModel P) (n : ℕ) :
    (differentialComplex D).X (-(n : ℤ)) ≅ differentialTerm P n :=
  (((AlgebraicTopology.alternatingFaceMapComplex _).obj D.module).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl) ≪≫ D.termIso n

/-- Mathlib's canonical polynomial extension `A[B] → B`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
def extension (f : Arrow CommRingCat.{u}) :
    letI := f.hom.hom.toAlgebra
    Algebra.Extension.{u} f.left f.right :=
  letI := f.hom.hom.toAlgebra
  (Algebra.Generators.self f.left f.right).toExtension

/-- The standard augmentation conormal module, with Mathlib's descended `B`-action.
Source: Stacks, Tag 08UP (blueprint: lem-trf-standard-cotangent-chain-projection). -/
def conormal (f : Arrow CommRingCat.{u}) : ModuleCat.{u} f.right :=
  letI := f.hom.hom.toAlgebra
  ModuleCat.of f.right (extension f).Cotangent

/-- The class of an element of the actual evaluation kernel in `I/I²`.
Source: Stacks, Tag 08UP (blueprint: lem-trf-standard-cotangent-chain-projection). -/
def kernelClass (f : Arrow CommRingCat.{u})
    (h : RingHom.ker (standardAugmentation f 0).hom) : conormal f :=
  letI := f.hom.hom.toAlgebra
  Algebra.Extension.Cotangent.mk (P := extension f) h

/-- The face difference in literal polynomial coordinates. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
def faceDifference
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (x : (C.standard f).algebra.obj (op ⦋1⦌)) : standardTerm f 0 :=
  (coordinates C f 0).hom
    ((C.standard f).algebra.δ (0 : Fin 2) x -
      (C.standard f).algebra.δ (1 : Fin 2) x)

/-- A two-term conormal complex and the prescribed face-difference chain projection.
Its coordinate differential is `[h] ↦ dh ⊗ 1`; the projection has identity degree
zero, face-difference degree minus one, and zero remaining components.
Source: Stacks, Tag 08UP (blueprint: lem-trf-standard-cotangent-chain-projection). -/
structure Projection
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) where
  target : CochainComplex (ModuleCat.{u} f.right) ℤ
  negIso : target.X (-1) ≅ conormal f
  zeroIso : target.X 0 ≅ differentialTerm (C.standard f) 0
  otherTerms : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (target.X i)
  differential_formula : ∀ h : RingHom.ker (standardAugmentation f 0).hom,
    zeroIso.hom (target.d (-1) 0 (negIso.inv (kernelClass f h))) =
      differentialGenerator (C.standard f) 0 1 ((coordinates C f 0).inv h.val)
  face_mem_kernel : ∀ x : (C.standard f).algebra.obj (op ⦋1⦌),
    standardAugmentation f 0 (faceDifference C f x) = 0
  map : differentialComplex (C.differentials (C.standard f)) ⟶ target
  zero_component :
    map.f 0 ≫ zeroIso.hom = (degreeIso (C.differentials (C.standard f)) 0).hom
  neg_component : ∀ (b : f.right) (x : (C.standard f).algebra.obj (op ⦋1⦌)),
    negIso.hom (map.f (-1)
      (complexGenerator (C.differentials (C.standard f)) 1 b x)) =
      b • kernelClass f ⟨faceDifference C f x, face_mem_kernel x⟩
  other_components : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → map.f i = 0

/-- The degree-minus-one map `ρ`, in the actual tensor and conormal coordinates.
Source: Stacks, Tag 08UP (blueprint: lem-trf-standard-cotangent-chain-projection). -/
def rho
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    {C : Coherence.{u}} {f : Arrow CommRingCat.{u}} (P : Projection C f) :
    differentialTerm (C.standard f) 1 ⟶ conormal f :=
  (degreeIso (C.differentials (C.standard f)) 1).inv ≫ P.map.f (-1) ≫ P.negIso.hom

/-- The conormal differential in the stated coordinates. Source: Stacks, Tag 08UP
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
def delta
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    {C : Coherence.{u}} {f : Arrow CommRingCat.{u}} (P : Projection C f) :
    conormal f ⟶ differentialTerm (C.standard f) 0 :=
  P.negIso.inv ≫ P.target.d (-1) 0 ≫ P.zeroIso.hom

/-- The alternating boundary `M_(n+1) → M_n` in tensor coordinates.
Source: Stacks, Tags 08PN and 08UP
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
def boundary
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) (n : ℕ) :
    differentialTerm (C.standard f) (n + 1) ⟶ differentialTerm (C.standard f) n :=
  (degreeIso (C.differentials (C.standard f)) (n + 1)).inv ≫
    (differentialComplex (C.differentials (C.standard f))).d (-((n + 1 : ℕ) : ℤ))
      (-(n : ℤ)) ≫ (degreeIso (C.differentials (C.standard f)) n).hom

/-- The specified semilinear map of two-term targets. Its action on conormal classes
and differential tensors is fixed, with no arbitrary target map.
Source: Stacks, Tags 08QL and 08UP
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
structure TargetMap
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    {C : Coherence.{u}} {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Projection C f) (Q : Projection C g) where
  kernel_mem : ∀ h : RingHom.ker (standardAugmentation f 0).hom,
    standardAugmentation g 0 (standardSquareMap q 0 h.val) = 0
  map : P.target ⟶ (restrictComplex q.right).obj Q.target
  conormal_formula : ∀ h : RingHom.ker (standardAugmentation f 0).hom,
    Q.negIso.hom (map.f (-1) (P.negIso.inv (kernelClass f h))) =
      kernelClass g ⟨standardSquareMap q 0 h.val, kernel_mem h⟩
  tensor_formula : ∀ (b : f.right) (x : (C.standard f).algebra.obj (op ⦋0⦌)),
    Q.zeroIso.hom
      (map.f 0 (P.zeroIso.inv (differentialGenerator (C.standard f) 0 b x))) =
      differentialGenerator (C.standard g) 0 (q.right b)
        ((C.standardMap q).map.app (op ⦋0⦌) x)

/-- The simultaneous standard projections, their two chain identities, and strict
naturality for every ring square. Source: Stacks, Tags 08UP and 08QL
(blueprint: lem-trf-standard-cotangent-chain-projection). -/
structure System
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) where
  projection : ∀ f : Arrow CommRingCat.{u}, Projection C f
  rho_formula : ∀ (f : Arrow CommRingCat.{u}) (b : f.right)
    (x : (C.standard f).algebra.obj (op ⦋1⦌)),
    rho (projection f) (differentialGenerator (C.standard f) 1 b x) =
      b • kernelClass f
        ⟨faceDifference C f x, (projection f).face_mem_kernel x⟩
  delta_rho : ∀ f : Arrow CommRingCat.{u},
    rho (projection f) ≫ delta (projection f) = boundary C f 0
  rho_partial : ∀ f : Arrow CommRingCat.{u}, boundary C f 1 ≫ rho (projection f) = 0
  targetMap : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    TargetMap q (projection f) (projection g)
  naturality : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    (projection f).map ≫ (targetMap q).map =
      (C.differentialMap (C.standardMap q)).map ≫
        (restrictComplex q.right).map (projection g).map

/-- The face-difference rule is well-defined and gives a strictly natural chain
projection to the two-term standard conormal complex.
Source: Stacks, Tag 08UP (remark-explicit-comparison-map) and Tag 08QL
(section-functoriality) (blueprint: lem-trf-standard-cotangent-chain-projection).

Proof:
1. Use lem-trf-cotangent-resolution-coherence for the standard resolution. Evaluation
   sends X_b to b and is surjective. The prescribed faces give d₀(Y_p)=p,
   d₁(Y_p)=X_εp and the three degree-two faces f, Y_d₀f, Y_d₁f. Polynomial
   uniqueness from def-weil-pbc-mv-polynomial-ring determines these maps.
2. Mathlib's conormal quotient has the B-action b[h]=[rh] for a lift ε(r)=b:
   different lifts differ in I and hence change rh by I². Leibniz from
   def-weil-pbc-kahler-differentials shows that h ↦ dh ⊗ 1 kills I² and is
   B-linear. This constructs the two-term target with the displayed differential.
3. Put Δ(f)=[d₀f-d₁f]. Additivity and vanishing on A follow from the faces.
   Expand d₀(fg)-d₁(fg)=d₀(f)(d₀g-d₁g)+d₁(g)(d₀f-d₁f). Modulo I² both
   coefficient actions are through the common augmentation, proving Leibniz.
4. The universal derivation of def-weil-pbc-kahler-differentials induces a map
   on differentials. The tensor universal property of
   lem-weil-pbc-module-base-change-universal-property extends it to the B-linear
   ρ(b ⊗ df)=bΔ(f). The tensor order here is the symmetric order of the source.
5. On all differential generators δρ equals the alternating first boundary.
   These generators span by the differential presentation and tensor bilinearity.
6. The dZ_f generate the degree-two term, by polynomial expansion and Leibniz.
   Applying ρ to its boundary gives the class of
   (d₀f-d₁f)-(d₀f-X_εd₀f)+(d₁f-X_εd₁f)=0 since εd₀f=εd₁f.
   These two identities give the chain map with the stated components.
7. The standard maps commute with augmentations and faces, hence carry I and
   I² into I' and I'². They induce [h] ↦ [t₀h] and b ⊗ dx ↦ β(b) ⊗ d(t_n x).
   On generators these commute with δ and ρ as equalities. Thus the entire
   chain-map square commutes strictly after restricting target scalars. -/
theorem exists_system
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) : Nonempty (System C) := by
  sorry

end Algebra.CotangentResolution.StandardProjection
