/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FullParameterRootTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The full parameter-root torsor and its fixed boundary

Source: main-20261015 ctf-stability direct-images proof (3), tame-boundary expansion,
root rotations, CRT, affine limits and the root-to-zero map
(blueprint: lem-sfb-full-root-rotation-torsor).

The conclusion packages canonical maps with their generator formulas. No map is chosen
from an unproved existence assertion. The profinite comparison uses the recorded test
object functor, including its scheme structure, rather than a set of geometric points.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Positive tame orders give nonzero residue moduli.
Source: tame-boundary expansion, positive prime-to-p orders
(blueprint: lem-sfb-full-root-rotation-torsor). -/
instance fullRootOrderNeZero {p : ℕ} (n : TameRootOrder p) : NeZero n.val :=
  ⟨Nat.ne_of_gt n.property.1⟩

/-- The finite root algebra, with precisely the equations in the statement.
Source: tame-boundary expansion, finite root covers
(blueprint: lem-sfb-full-root-rotation-torsor). -/
def ParameterRootStage {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) (n : ℕ) :=
  MvPolynomial I H ⧸ Ideal.span
    (Set.range (fun i : I ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))

/-- The inherited ring structure on the finite root quotient.
Source: tame-boundary expansion, finite root covers
(blueprint: lem-sfb-full-root-rotation-torsor). -/
instance parameterRootStageCommRing {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) (n : ℕ) : CommRing (ParameterRootStage t n) :=
  inferInstanceAs (CommRing
    (MvPolynomial I H ⧸ Ideal.span
      (Set.range (fun i : I ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))))

/-- The inherited coefficient algebra structure on the finite root algebra.
Source: tame-boundary expansion, finite root covers
(blueprint: lem-sfb-full-root-rotation-torsor). -/
instance parameterRootStageAlgebra {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) (n : ℕ) : Algebra H (ParameterRootStage t n) :=
  inferInstanceAs (Algebra H
    (MvPolynomial I H ⧸ Ideal.span
      (Set.range (fun i : I ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))))

/-- The specified quotient generator of a finite root algebra.
Source: tame-boundary expansion, root coordinates
(blueprint: lem-sfb-full-root-rotation-torsor). -/
def parameterRootStageRoot {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) (n : ℕ) (i : I) :
    ParameterRootStage t n :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Finite residue labels, with multiplicative notation for coordinatewise addition.
Source: tame-boundary expansion, the groups G_n
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev ParameterRootLabels (I : Type u) (n : ℕ) := Multiplicative (I → ZMod n)

/-- The inverse limit of the finite label groups, with its product subspace topology.
The group law is coordinatewise, as specified in `FullRootRotationData.residue_mul`.
Source: tame-boundary expansion, ordinary residue transitions
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev ParameterRootResidueLimit (p : ℕ) (I : Type u) :=
  {a : (n : TameRootOrder p) → ParameterRootLabels I n.val //
    ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val) (i : I),
      ZMod.castHom h (ZMod n.val) ((a m).toAdd i) = (a n).toAdd i}

/-- The punctured base ring. The empty product is one.
Source: tame-boundary expansion, U circle
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev ParameterRootBase {I H : Type u} [Fintype I] [CommRing H] (t : I → H) :=
  Localization.Away (∏ i, t i)

/-- The finite punctured root ring; zero rings are permitted.
Source: tame-boundary expansion, T_n circle
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev ParameterRootStageAway {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) (n : ℕ) :=
  Localization.Away (algebraMap H (ParameterRootStage t n) (∏ i, t i))

/-- The punctured full root ring, using the recorded compatible-root presentation.
Source: tame-boundary expansion, T circle
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev FullParameterRootAway (p : ℕ) {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) :=
  Localization.Away (algebraMap H (FullParameterRootAlgebra p t) (∏ i, t i))

/-- The parameter boundary quotient, including the zero quotient and the empty family.
Source: tame-boundary expansion, H/J
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev ParameterRootBoundary {I H : Type u} [CommRing H] (t : I → H) :=
  H ⧸ Ideal.span (Set.range t)

/-- The recorded scheme-valued profinite test object over an affine scheme.
Source: tame-boundary expansion, X[P]
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev rootTest (R : Type u) [CommRing R] (P : Profinite.{u}) : Scheme.{u} :=
  ((profiniteToProEtOf (Spec (.of R))).obj P).left

/-- The structural projection X[P] to X.
Source: tame-boundary expansion, first torsor projection
(blueprint: lem-sfb-full-root-rotation-torsor). -/
abbrev rootTestProjection (R : Type u) [CommRing R] (P : Profinite.{u}) :
    rootTest R P ⟶ Spec (.of R) :=
  ((profiniteToProEtOf (Spec (.of R))).obj P).hom

/-- The constant-label slice X to X[P], constructed by evaluation on locally constant
functions and the pullback universal property.
Source: tame-boundary expansion, (x,g)
(blueprint: lem-sfb-full-root-rotation-torsor). -/
def rootTestSlice (R : Type u) [CommRing R] (P : Profinite.{u}) (g : P) :
    Spec (.of R) ⟶ rootTest R P :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom ((Int.castRingHom R).comp (LocallyConstant.evalRingHom g))))
    (𝟙 _) (specULiftZIsTerminal.hom_ext _ _)

/-- The map X'[P'] to X[P] induced by a scheme map and a continuous label map.
Source: tame-boundary expansion, transition and base-change compatibility
(blueprint: lem-sfb-full-root-rotation-torsor). -/
def rootTestMap {R S : Type u} [CommRing R] [CommRing S]
    (f : Spec (.of S) ⟶ Spec (.of R)) {P Q : Profinite.{u}} (a : Q ⟶ P) :
    rootTest S Q ⟶ rootTest R P :=
  pullback.map _ _ _ _ (profiniteToScheme.map a) f (𝟙 _)
    (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _)

/-- The complete canonical rotation, torsor and fixed-boundary conclusions, expressed
as data with their defining equations, so no arbitrary comparison or action is assumed.
The residue homeomorphism preserves multiplication coordinatewise and takes integral
vectors to their ordinary residues. The finite and infinite comparisons are scheme
isomorphisms, with both projections specified on every constant-label slice.
Source: main-20261015 direct-images proof (3), tame-boundary expansion
(blueprint: lem-sfb-full-root-rotation-torsor). -/
structure FullRootRotationData (p : ℕ) {I H : Type u} [Fintype I] [CommRing H]
    (t : I → H) (ζ : TameRootOrder p → H) where
  residue : ParameterRootDeckGroup p I ≃ₜ ParameterRootResidueLimit p I
  residue_mul : ∀ g h n, (residue (g * h)).val n =
    (residue g).val n * (residue h).val n
  residue_integer : ∀ (a : I → ℤ) (n : TameRootOrder p) i,
    ((residue (parameterRootDeckInteger p a)).val n).toAdd i = (a i : ZMod n.val)
  transition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    ParameterRootStage t n.val →ₐ[H] ParameterRootStage t m.val
  transition_root : ∀ n m h i,
    transition n m h (parameterRootStageRoot t n.val i) =
      parameterRootStageRoot t m.val i ^ (m.val / n.val)
  inclusion : ∀ n : TameRootOrder p,
    ParameterRootStage t n.val →ₐ[H] FullParameterRootAlgebra p t
  inclusion_root : ∀ n i,
    inclusion n (parameterRootStageRoot t n.val i) = fullParameterRoot p t n i
  inclusion_transition : ∀ n m h, (inclusion m).comp (transition n m h) = inclusion n
  rotation : ∀ n : TameRootOrder p, ParameterRootLabels I n.val →
    (ParameterRootStage t n.val →ₐ[H] ParameterRootStage t n.val)
  rotation_root : ∀ n a i, rotation n a (parameterRootStageRoot t n.val i) =
    algebraMap H _ (ζ n ^ (a.toAdd i).val) * parameterRootStageRoot t n.val i
  rotation_one : ∀ n, rotation n 1 = AlgHom.id H _
  rotation_mul : ∀ n a b, rotation n (a * b) = (rotation n a).comp (rotation n b)
  rotation_transition : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val) a,
    (transition n m h).comp
        (rotation n (Multiplicative.ofAdd (fun i ↦ ZMod.castHom h _ (a.toAdd i)))) =
      (rotation m a).comp (transition n m h)
  fullRotation : ParameterRootDeckGroup p I →
    (FullParameterRootAlgebra p t →ₐ[H] FullParameterRootAlgebra p t)
  fullRotation_root : ∀ g n i, fullRotation g (fullParameterRoot p t n i) =
    algebraMap H _ (ζ n ^ (((residue g).val n).toAdd i).val) * fullParameterRoot p t n i
  fullRotation_one : fullRotation 1 = AlgHom.id H _
  fullRotation_mul : ∀ g h, fullRotation (g * h) = (fullRotation g).comp (fullRotation h)
  fullRotation_inclusion : ∀ g n,
    (fullRotation g).comp (inclusion n) = (inclusion n).comp (rotation n ((residue g).val n))
  base : ∀ n : TameRootOrder p,
    ParameterRootBase t →+* ParameterRootStageAway t n.val
  base_constants : ∀ n h, base n (algebraMap H _ h) =
    algebraMap (ParameterRootStage t n.val) _ (algebraMap H _ h)
  fullBase : ParameterRootBase t →+* FullParameterRootAway p t
  fullBase_constants : ∀ h, fullBase (algebraMap H _ h) =
    algebraMap (FullParameterRootAlgebra p t) _ (algebraMap H _ h)
  awayTransition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    ParameterRootStageAway t n.val →+* ParameterRootStageAway t m.val
  awayTransition_localization : ∀ n m h x,
    awayTransition n m h (algebraMap (ParameterRootStage t n.val) _ x) =
      algebraMap (ParameterRootStage t m.val) _ (transition n m h x)
  awayInclusion : ∀ n : TameRootOrder p,
    ParameterRootStageAway t n.val →+* FullParameterRootAway p t
  awayInclusion_localization : ∀ n x,
    awayInclusion n (algebraMap (ParameterRootStage t n.val) _ x) =
      algebraMap (FullParameterRootAlgebra p t) _ (inclusion n x)
  awayRotation : ∀ n : TameRootOrder p, ParameterRootLabels I n.val →
    (ParameterRootStageAway t n.val →+* ParameterRootStageAway t n.val)
  awayRotation_localization : ∀ n a x,
    awayRotation n a (algebraMap (ParameterRootStage t n.val) _ x) =
      algebraMap (ParameterRootStage t n.val) _ (rotation n a x)
  fullAwayRotation : ParameterRootDeckGroup p I →
    (FullParameterRootAway p t →+* FullParameterRootAway p t)
  fullAwayRotation_localization : ∀ g x,
    fullAwayRotation g (algebraMap (FullParameterRootAlgebra p t) _ x) =
      algebraMap (FullParameterRootAlgebra p t) _ (fullRotation g x)
  comparison : ∀ n : TameRootOrder p,
    rootTest (ParameterRootStageAway t n.val) (Profinite.of (ParameterRootLabels I n.val)) ≅
      pullback (Spec.map (CommRingCat.ofHom (base n))) (Spec.map (CommRingCat.ofHom (base n)))
  comparison_fst : ∀ n, (comparison n).hom ≫ pullback.fst _ _ = rootTestProjection _ _
  comparison_slice : ∀ n a, rootTestSlice _ _ a ≫ (comparison n).hom ≫
    pullback.snd _ _ = Spec.map (CommRingCat.ofHom (awayRotation n a))
  comparison_transition : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
    rootTestMap (Spec.map (CommRingCat.ofHom (awayTransition n m h)))
        (CompHausLike.ofHom _ ⟨fun a ↦ Multiplicative.ofAdd
          (fun i ↦ ZMod.castHom h _ (a.toAdd i)), continuous_of_discreteTopology⟩) ≫
        (comparison n).hom ≫ pullback.snd _ _ =
      (comparison m).hom ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (awayTransition n m h))
  fullComparison : rootTest (FullParameterRootAway p t)
      (Profinite.of (ParameterRootDeckGroup p I)) ≅
    pullback (Spec.map (CommRingCat.ofHom fullBase)) (Spec.map (CommRingCat.ofHom fullBase))
  fullComparison_fst : fullComparison.hom ≫ pullback.fst _ _ = rootTestProjection _ _
  fullComparison_slice : ∀ g, rootTestSlice _ _ g ≫ fullComparison.hom ≫
    pullback.snd _ _ = Spec.map (CommRingCat.ofHom (fullAwayRotation g))
  fullComparison_finite : ∀ n,
    rootTestMap (Spec.map (CommRingCat.ofHom (awayInclusion n)))
        (CompHausLike.ofHom _ ⟨fun g ↦ (residue g).val n,
          (continuous_apply n).comp (continuous_subtype_val.comp residue.continuous)⟩) ≫
        (comparison n).hom ≫ pullback.snd _ _ =
      fullComparison.hom ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (awayInclusion n))
  boundary : FullParameterRootAlgebra p t →+* ParameterRootBoundary t
  boundary_constants : ∀ h, boundary (algebraMap H _ h) = Ideal.Quotient.mk _ h
  boundary_root : ∀ n i, boundary (fullParameterRoot p t n i) = 0
  boundary_fixed : ∀ g, boundary.comp (fullRotation g).toRingHom = boundary
  empty_full : IsEmpty I → Function.Bijective (algebraMap H (FullParameterRootAlgebra p t))
  empty_group : IsEmpty I → Subsingleton (ParameterRootDeckGroup p I)
  empty_boundary : IsEmpty I → Function.Bijective boundary

/-- Naturality under a ring map preserving the parameters and compatible roots.
Every ring map below is specified on constants and roots, and every localized map is
specified on its source ring. Thus these are the actual canonical maps. Comparison
naturality specifies the second projection; the first is the structural projection.
Source: main-20261015 direct-images proof (3), tame-boundary expansion, base-change clause
(blueprint: lem-sfb-full-root-rotation-torsor). -/
structure FullRootRotationBaseChange {p : ℕ} {I H K : Type u} [Fintype I]
    [CommRing H] [CommRing K] {t : I → H} {s : I → K}
    {ζ : TameRootOrder p → H} {η : TameRootOrder p → K}
    (D : FullRootRotationData p t ζ) (E : FullRootRotationData p s η) (φ : H →+* K) where
  residue_eq : ∀ g, D.residue g = E.residue g
  stageMap : ∀ n : TameRootOrder p, ParameterRootStage t n.val →+* ParameterRootStage s n.val
  stageMap_constants : ∀ n h, stageMap n (algebraMap H _ h) = algebraMap K _ (φ h)
  stageMap_root : ∀ n i,
    stageMap n (parameterRootStageRoot t n.val i) = parameterRootStageRoot s n.val i
  fullMap : FullParameterRootAlgebra p t →+* FullParameterRootAlgebra p s
  fullMap_constants : ∀ h, fullMap (algebraMap H _ h) = algebraMap K _ (φ h)
  fullMap_root : ∀ n i, fullMap (fullParameterRoot p t n i) = fullParameterRoot p s n i
  transition_natural : ∀ n m h,
    (stageMap m).comp (D.transition n m h).toRingHom =
      (E.transition n m h).toRingHom.comp (stageMap n)
  inclusion_natural : ∀ n,
    fullMap.comp (D.inclusion n).toRingHom = (E.inclusion n).toRingHom.comp (stageMap n)
  rotation_natural : ∀ n a,
    (stageMap n).comp (D.rotation n a).toRingHom =
      (E.rotation n a).toRingHom.comp (stageMap n)
  fullRotation_natural : ∀ g,
    fullMap.comp (D.fullRotation g).toRingHom = (E.fullRotation g).toRingHom.comp fullMap
  baseMap : ParameterRootBase t →+* ParameterRootBase s
  baseMap_constants : ∀ h, baseMap (algebraMap H _ h) = algebraMap K _ (φ h)
  awayStageMap : ∀ n : TameRootOrder p,
    ParameterRootStageAway t n.val →+* ParameterRootStageAway s n.val
  awayStageMap_localization : ∀ n x,
    awayStageMap n (algebraMap (ParameterRootStage t n.val) _ x) =
      algebraMap (ParameterRootStage s n.val) _ (stageMap n x)
  awayFullMap : FullParameterRootAway p t →+* FullParameterRootAway p s
  awayFullMap_localization : ∀ x,
    awayFullMap (algebraMap (FullParameterRootAlgebra p t) _ x) =
      algebraMap (FullParameterRootAlgebra p s) _ (fullMap x)
  base_natural : ∀ n, (awayStageMap n).comp (D.base n) = (E.base n).comp baseMap
  fullBase_natural : awayFullMap.comp D.fullBase = E.fullBase.comp baseMap
  comparison_natural : ∀ n,
    rootTestMap (Spec.map (CommRingCat.ofHom (awayStageMap n))) (𝟙 _) ≫
        (D.comparison n).hom ≫ pullback.snd _ _ =
      (E.comparison n).hom ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (awayStageMap n))
  fullComparison_natural :
    rootTestMap (Spec.map (CommRingCat.ofHom awayFullMap)) (𝟙 _) ≫
        D.fullComparison.hom ≫ pullback.snd _ _ =
      E.fullComparison.hom ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom awayFullMap)
  boundaryMap : ParameterRootBoundary t →+* ParameterRootBoundary s
  boundaryMap_constants : ∀ h, boundaryMap (Ideal.Quotient.mk _ h) =
    Ideal.Quotient.mk _ (φ h)
  boundary_natural : boundaryMap.comp D.boundary = E.boundary.comp fullMap

/-- Compatible rotations give the finite and full profinite torsor comparisons and the
fixed root-to-zero boundary map, naturally in the ring, parameters and compatible roots.
The conclusion is data with canonical defining equations, not a choice of a cover or an
assumption that a torsor comparison already exists.

Source: main-20261015 ctf-stability direct-images proof (3), tame-boundary expansion
(blueprint: lem-sfb-full-root-rotation-torsor).

Proof:
1. Define each rotation on quotient generators by multiplying the i-th root by the
   indicated power of ζ_n. The n-th power relation, inverse label and addition of labels
   give the action laws. Compatibility of ζ gives the power-transition equations.
2. Reconstruct compatible residues from the q-adic coordinates by CRT
   [lem-pc-crt-ideal-quotient-product]. Conversely use PadicInt.lift and its uniqueness
   [lem-exc-padic-residue-universal-property]. Their residue formulas and separation show
   the maps are inverse. Residue fibres are open and agreement modulo q^b bounds the
   q-adic norm, proving continuity in both directions. Integral vectors have their usual
   residues, including the singleton modulus one.
3. Localization commutes with the directed root-algebra colimit by its universal
   property. The affine spectrum limit theorem [lem-weil-pbc-spec-colimit-limit] then
   identifies the localized full presentation with the limit of punctured finite stages.
4. Reindex the finite parameter family by Fin (card I). Apply
   [lem-sfb-compatible-kummer-tower-cech] to obtain the specified finite CRT comparisons,
   their power-transition compatibility and the full profinite comparison on the recorded
   scheme-valued test objects. Their projections on each label slice are exactly x and gx.
5. Send constants to H/(t_i) and every positive-order root to zero. All root and transition
   relations vanish, so the compatible-root quotient gives the boundary map. Rotations
   fix it because a scalar times zero is zero.
6. For φ preserving parameters and roots, send each root generator to its namesake.
   Relations, rotations and power maps agree on generators. Pass to localizations and
   use the comparison base-change clause of the Cech node. On boundary quotients the two
   composites agree on constants and send every root to zero. Residue reconstruction
   is independent of H. These are all the fields of FullRootRotationBaseChange.
7. With no parameters all presentations are H, f=1 and J=0. The structural and boundary
   ring maps are bijective and the deck group is a singleton, giving the identity
   comparisons and boundary inclusion under these canonical identifications. Empty
   punctures give zero localization rings and are allowed throughout.
-/
theorem fullRootRotationTorsor (p : ℕ) (hp : p.Prime)
    {I H : Type u} [Fintype I] [CommRing H] [Nontrivial H] [CharP H p]
    (t : I → H) (ζ : TameRootOrder p → H)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) n.val)
    (hcompat : ∀ (n m : TameRootOrder p), n.val ∣ m.val → ζ m ^ (m.val / n.val) = ζ n)
    (hunit : ∀ (n : TameRootOrder p) (a b : ZMod n.val), a ≠ b →
      IsUnit (ζ n ^ a.val - ζ n ^ b.val)) :
    ∃ D : FullRootRotationData p t ζ,
      ∀ (K : Type u) [CommRing K] [Nontrivial K] [CharP K p]
        (s : I → K) (η : TameRootOrder p → K)
        (_hη : ∀ n, IsPrimitiveRoot (η n) n.val)
        (_hcompat : ∀ (n m : TameRootOrder p), n.val ∣ m.val → η m ^ (m.val / n.val) = η n)
        (_hunit : ∀ (n : TameRootOrder p) (a b : ZMod n.val), a ≠ b →
          IsUnit (η n ^ a.val - η n ^ b.val))
        (φ : H →+* K) (_ht : ∀ i, φ (t i) = s i) (_hroots : ∀ n, φ (ζ n) = η n)
        (E : FullRootRotationData p s η), Nonempty (FullRootRotationBaseChange D E φ) := by
  sorry

end AlgebraicGeometry.ProEtale
