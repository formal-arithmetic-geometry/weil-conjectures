module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Compatible injectives and the homogeneous injective total target

Source: blueprint, six-functors direct-images proof, paragraph (3), resolution
normalization helper; Stacks Tags 03EV and 015Z
(blueprint: lem-sfb-homogeneous-injective-total-target).

All models below are specifications with the actual free modules and internal Hom.
No construction is selected from the existence theorem. Nonnegative complexes are
extended by zero when read as ordinary integer-indexed cochain complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (HomogeneousFunctions homogeneousEvaluate)
open Profinite.CondensedAction.InternalBar (onSections pureTensor)

namespace CategoryTheory.CondensedBar

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The section-ring sheaf of the given condensed ring, with its ring-valued encoding.
Source: the internal-to-section equivalence and Stacks 03EV
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
abbrev homogeneousSectionRings :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat RingCat)).obj
    (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) A.X)

/-- The sheafified direct sum indexed by maps to P: extension by zero of the unit
on the slice. Its presheaf at V is the sum of A(V) over V → P, including the empty sum.
Source: Stacks 03EV, clause (2)
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
abbrev homogeneousFreeSheaf (P : Profinite.{u}) :=
  (PresheafOfModules.sheafification.{u + 1} (𝟙 (homogeneousSectionRings A).obj)).obj
    ((SheafOfModules.extensionByZeroPresheaf.{u + 1} (homogeneousSectionRings A) P).obj
      (SheafOfModules.unit ((homogeneousSectionRings A).over P)))

/-- The canonical generator for a represented profinite parameter, obtained from the
existing free-forgetful adjunction's unit, on each test object.
Source: the generalized-generator normalization of free induction
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
def homogeneousParameterGenerator (P S : Profinite.{u}) (x : C(S, P)) :
    sections A (freeParameter A P) S :=
  (((Profinite.CondensedAction.InternalBar.freeAdjunction A.toMon).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P)).hom.app (op S))
      (ULift.up (CompHausLike.ofHom _ x))

/-- Translation induction, with its underlying tensor functor and both adjunction
formulas fixed on generalized pure tensors over every profinite test object.
Source: resolution normalization helper, free-induction paragraph
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
structure HomogeneousFreeInduction where
  functor : Modules A ⥤ Equivariant A G
  underlying : functor ⋙ forgetAction ≅ tensorLeft (freeParameter A (Profinite.of G))
  adjunction : functor ⊣ forgetAction
  translation : ∀ (M : Modules A) (S : Profinite.{u}) (k g : C(S, G))
    (m : sections A M S),
    onSections A.toMon (underlying.hom.app M) S
      ((functor.obj M).act S k
        (onSections A.toMon (underlying.inv.app M) S
          (pureTensor A.toMon _ M S (homogeneousParameterGenerator A _ S g) m))) =
      pureTensor A.toMon _ M S (homogeneousParameterGenerator A _ S (k * g)) m
  untranspose : ∀ (M : Modules A) (J : Equivariant A G) (h : M ⟶ J.module)
    (S : Profinite.{u}) (g : C(S, G)) (m : sections A M S),
    onSections A.toMon ((adjunction.homEquiv M J).symm h).val S
      (onSections A.toMon (underlying.inv.app M) S
        (pureTensor A.toMon _ M S (homogeneousParameterGenerator A _ S g) m)) =
      J.act S g (onSections A.toMon h S m)
  transpose : ∀ (M : Modules A) (J : Equivariant A G) (b : functor.obj M ⟶ J)
    (S : Profinite.{u}) (m : sections A M S),
    onSections A.toMon (adjunction.homEquiv M J b) S m =
      onSections A.toMon b.val S (onSections A.toMon (underlying.inv.app M) S
        (pureTensor A.toMon _ M S (homogeneousParameterGenerator A _ S 1) m))
  exact : PreservesFiniteLimits functor ∧ PreservesFiniteColimits functor

/-- Evaluation through the fixed underlying internal-Hom identification. The result
is an actual section on T, for arbitrary T → S, not a function only on ordinary points.
Source: the homogeneous double complex, displayed action and differential formulas
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
def homogeneousTargetValue {J : Equivariant A G} {p : ℕ}
    (H : HomogeneousFunctions A.toMon G J p) (S : Profinite.{u})
    (c : sections A H.object.module S) (T : Profinite.{u}) (f : T ⟶ S)
    (x : Fin (p + 1) → C(T, G)) : sections A J.module T :=
  homogeneousEvaluate A.toMon G J p S
    ((H.internalHom.hom.val.app (op S)).hom c) T f x

variable {A G}

/-- The homogeneous double complex and its injective finite-diagonal total, with
horizontal deletion, vertical postcomposition and the constant augmentation fixed
on every profinite slice. The bicomplex type includes commuting square-zero maps.
Source: resolution normalization helper, homogeneous total construction
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
structure HomogeneousInjectiveTotal [ActionAbelian A G]
    (I : CochainComplex (Equivariant A G) ℕ) where
  double : HomologicalComplex₂ (Equivariant A G) (.up ℕ) (.up ℕ)
  functions : ∀ p q : ℕ, HomogeneousFunctions A.toMon G (I.X q) p
  term : ∀ p q : ℕ, (double.X p).X q ≅ (functions p q).object
  horizontal : ∀ (p q : ℕ) (S : Profinite.{u})
    (c : sections A ((double.X p).X q).module S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (p + 2) → C(T, G)),
    homogeneousTargetValue A G (functions (p + 1) q) S
      (onSections A.toMon (((double.d p (p + 1)).f q ≫ (term (p + 1) q).hom).val) S c)
      T f x =
    ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
      homogeneousTargetValue A G (functions p q) S
        (onSections A.toMon (term p q).hom.val S c) T f (fun j ↦ x (i.succAbove j))
  vertical : ∀ (p q : ℕ) (S : Profinite.{u})
    (c : sections A ((double.X p).X q).module S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (p + 1) → C(T, G)),
    homogeneousTargetValue A G (functions p (q + 1)) S
      (onSections A.toMon (((double.X p).d q (q + 1) ≫ (term p (q + 1)).hom).val) S c)
      T f x =
    onSections A.toMon (I.d q (q + 1)).val T
      (homogeneousTargetValue A G (functions p q) S
        (onSections A.toMon (term p q).hom.val S c) T f x)
  injective : ∀ p q : ℕ, Injective ((double.X p).X q)
  [hasTotal : double.HasTotal (.up ℕ)]
  totalInjective : ∀ n : ℕ, Injective ((double.total (.up ℕ)).X n)
  negative : ∀ n : ℤ, n < 0 →
    IsZero (((double.total (.up ℕ)).extend ComplexShape.embeddingUpNat).X n)
  constants : ∀ q : ℕ, I.X q ⟶ (double.X 0).X q
  constantValue : ∀ (q : ℕ) (S : Profinite.{u}) (m : sections A (I.X q).module S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin 1 → C(T, G)),
    homogeneousTargetValue A G (functions 0 q) S
      (onSections A.toMon ((constants q ≫ (term 0 q).hom).val) S m) T f x =
    (I.X q).module.X.obj.map f.op m
  delta : I ⟶ double.total (.up ℕ)
  delta_components : ∀ q : ℕ,
    delta.f q = constants q ≫ double.ιTotal (.up ℕ) 0 q q (by simp)

variable (A G)

/-- Full assertion of compatible injectives and the homogeneous total target.
Abelianness is supplied as conclusion data for the fixed additive action category;
no extra hypothesis is imposed on the ring or group. Each resolution is arbitrary.
Source: all paragraphs of the resolution normalization helper
(blueprint: lem-sfb-homogeneous-injective-total-target). -/
structure HomogeneousInjectiveTargetData where
  [abelian : ActionAbelian A G]
  freePresentation : ∀ P : Profinite.{u},
    Nonempty ((sectionsFunctor A).obj (freeParameter A P) ≅ homogeneousFreeSheaf A P)
  flat : ∀ P : Profinite.{u},
    PreservesFiniteLimits (tensorLeft (freeParameter A P)) ∧
      PreservesFiniteColimits (tensorLeft (freeParameter A P))
  induction : HomogeneousFreeInduction A G
  forgetExact : PreservesFiniteLimits (forgetAction (A := A) (G := G)) ∧
    PreservesFiniteColimits (forgetAction (A := A) (G := G))
  forgetInjective : (forgetAction (A := A) (G := G)).PreservesInjectiveObjects
  resolutions : ∀ N : Equivariant A G, Nonempty (InjectiveResolution N)
  underlyingInjective : ∀ (N : Equivariant A G) (I : InjectiveResolution N) (q : ℕ),
    Injective (I.cocomplex.X q).module
  underlyingQuasiIso : ∀ (N : Equivariant A G) (I : InjectiveResolution N),
    QuasiIso (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℕ)).map I.ι)
  kInjective : ∀ (N : Equivariant A G) (I : InjectiveResolution N),
    I.cochainComplex.IsKInjective
  totals : ∀ (N : Equivariant A G) (I : InjectiveResolution N),
    Nonempty (HomogeneousInjectiveTotal I.cocomplex)

/-- Compatible equivariant injective resolutions and normalized homogeneous injective
finite-diagonal total targets exist for every commutative condensed ring and profinite group.

Source: six-functors direct-images proof, paragraph (3), resolution normalization
helper; Stacks 03EV (flat extension by zero) and 015Z (adjoint injective preservation)
(blueprint: lem-sfb-homogeneous-injective-total-target).

Proof:
1. Apply lem-sfb-condensed-free-linearization-tensor to the represented parameter P.
Its section module is the sheafification of the sum over V → P of A(V), hence the
extension by zero of the unit from the slice. Apply lem-pc-sites-modules-j-shriek-flat,
then lem-pe-internal-section-tensor-comparison to obtain exactness of internal tensor.
2. On A[G] tensor M let k translate the free generator [g] to [kg]. The free and
tensor universal properties extend this over every slice. Transpose h by [g] tensor m
mapping to g.h(m), and transpose back by evaluation at [1]; the action laws show
these maps are inverse and natural. This gives the specified induction adjunction.
3. By lem-sfb-condensed-action-injective-infrastructure, forgetting is exact and detects
exactness. Its composite with induction is the exact tensor functor of step 1, so
induction is exact. Apply lem-sp-right-adjoint-preserves-injectives to this adjunction.
4. The same infrastructure and lem-sp-grothendieck-enough-injectives supply enough
injectives. Starting with N, embed successive cokernels in injectives and use the
quotient followed by the next embedding as differential. This gives a nonnegative
injective resolution. For any such resolution, exact forgetting preserves its
quasi-isomorphism and step 3 preserves its injective terms. The theorem
lem-weil-pbc-bounded-below-injectives-kinjective makes its zero extension K-injective.
5. Apply lem-sfb-internal-homogeneous-functions-injective to every I^q and p, using
underlying injectivity from step 4, to obtain the displayed homogeneous terms.
6. Precomposition by deleting coordinate i gives the horizontal faces. Their alternating
sum squares to zero: the two deletion orders for i < j have opposite signs.
Postcomposition with d_I squares to zero and commutes with all faces; both operations
are equivariant on every profinite slice.
7. Use def-sp-double-complex-total. On bidegree (p,q) its differential is
horizontal plus (-1)^p vertical; the mixed terms cancel. There are n+1 summands
in degree n, each injective by step 5. Extend a map along a monomorphism componentwise
and combine the finitely many extensions to prove total injectivity. Below zero the
extension is zero, hence also injective.
8. Constants m ↦ (h ↦ m) give equivariant maps I^q → T^(0,q). Their horizontal
differential is zero, and their vertical differential is the constant of d_I(m).
The sign at p=0 is +1, so the bar-zero inclusions give the cochain map delta.
All operations use restriction, group multiplication and inversion, and internal
linear maps, so all action and adjunction identities hold after every profinite base change.
-/
theorem homogeneous_injective_total_target : Nonempty (HomogeneousInjectiveTargetData A G) := by
  sorry

end CategoryTheory.CondensedBar
