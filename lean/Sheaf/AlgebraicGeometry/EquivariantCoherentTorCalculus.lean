module

public import Sheaf.AlgebraicGeometry.EquivariantTorCalculusData
public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Equivariant coherent Tor calculus

Source: Stacks 08BP, 00LY, 00LS, 00M7, 00M8, 01BY and 03LF, with the
node's eleven-step action-groupoid descent argument.
(blueprint: lem-sfb-equivariant-coherent-tor-calculus)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SchemeTor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


open Scheme.Modules
open CategoryTheory.CartesianMonoidalCategory
attribute [local instance] pullbackAdditive modulesMonoidal modulesMonoidalPreadditive

variable (F : Type u) [Field F]

set_option maxHeartbeats 100000 in
-- The comparison record binds several dependent sheaf and derived-category interfaces.
/-- The actual derived symmetry on Tor, with the degree-zero signed tensor convention.
Source: Stacks 08BP and 06YH (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
def symmetry {X : Scheme.{u}} (P M : X.Modules) (q : ℕ) : obj q P M ≅ obj q M P := by
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).1.some
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).2.1.some
  letI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  letI := schemeModule_hasFunctorialFlatResolution X
  letI : BraidedCategory
      (DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
    DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
  unfold obj tensor
  exact (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (-(q : ℤ))).mapIso
      (β_ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj P)
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))

/-- A module map is equivariant precisely when its linearization square commutes.
Source: Stacks 03LF (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
def EquivariantArrow {S : Scheme.{u}} {G X : Over S} [GrpObj G] [ModObj G X]
    {D : EquivariantCoherent.ActionGroupoidModel G X}
    (P M : EquivariantCoherent.Coherent D)
    (f : EquivariantCoherent.underlying P ⟶ EquivariantCoherent.underlying M) : Prop :=
  (tensorPullback (EquivariantCoherent.target G X)).map f ≫
      (EquivariantCoherent.linearization M).hom =
    (EquivariantCoherent.linearization P).hom ≫
      (tensorPullback (EquivariantCoherent.source G X)).map f

/-- Equivariance for a bilinear operation on coherent linearized modules.
Source: Stacks 03LF and 01CD (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
def EquivariantBilinear {S : Scheme.{u}} {G X : Over S} [GrpObj G] [ModObj G X]
    {D : EquivariantCoherent.ActionGroupoidModel G X}
    (P M N : EquivariantCoherent.Coherent D)
    (f : ordinaryTensor (EquivariantCoherent.underlying P)
      (EquivariantCoherent.underlying M) ⟶ EquivariantCoherent.underlying N) : Prop :=
  (tensorPullback (EquivariantCoherent.target G X)).map f ≫
      (EquivariantCoherent.linearization N).hom =
    (EquivariantCoherent.tensorComparison (EquivariantCoherent.target G X)
      (EquivariantCoherent.underlying P) (EquivariantCoherent.underlying M)).hom ≫
    EquivariantCoherent.moduleTensorMap (EquivariantCoherent.linearization P).hom
      (EquivariantCoherent.linearization M).hom ≫
    (EquivariantCoherent.tensorComparison (EquivariantCoherent.source G X)
      (EquivariantCoherent.underlying P) (EquivariantCoherent.underlying M)).inv ≫
    (tensorPullback (EquivariantCoherent.source G X)).map f

/-- The existing algebra-object structure is equivariant, including its unit.
Source: Stacks 03LF and 00M7 (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
def EquivariantAlgebra {S : Scheme.{u}} {G X : Over S} [GrpObj G] [ModObj G X]
    {D : EquivariantCoherent.ActionGroupoidModel G X}
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)] : Prop :=
  EquivariantBilinear P P P MonObj.mul ∧
    (tensorPullback (EquivariantCoherent.target G X)).map MonObj.one ≫
        (EquivariantCoherent.linearization P).hom =
      tensorPullbackObjUnitToUnit (EquivariantCoherent.target G X) ≫
      (letI := (tensorPullbackObjUnitToUnit_isIso (EquivariantCoherent.source G X)).1;
        inv (tensorPullbackObjUnitToUnit (EquivariantCoherent.source G X))) ≫
      (tensorPullback (EquivariantCoherent.source G X)).map MonObj.one

/-- Multiplication on the coefficient factor of a tensor complex.
Source: Stacks 00M7 (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
def coefficientTerm {X : Scheme.{u}} (P E : X.Modules) [MonObj P] :
    ordinaryTensor P (ordinaryTensor E P) ⟶ ordinaryTensor E P :=
  (α_ P E P).inv ≫ ((β_ P E).hom ▷ P) ≫ (α_ E P P).hom ≫ (E ◁ MonObj.mul)

set_option maxHeartbeats 100000 in
-- The comparison record binds several dependent sheaf and derived-category interfaces.
/-- Multiplication acts on Tor as coefficient multiplication on resolution homology;
its arrows and all boundaries in the second variable are linear, and an ideal acting
as zero on P acts as zero on Tor. The field `killed` applies to every invariant coherent
ideal and quotient presentation, without choosing a quotient model.
Source: Stacks 00M7 and 08BP (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
structure AlgebraCalculus (B : FlatCalculus F) (A : ActionCalculus F B) where
  /-- The actual module-object structure over the existing algebra object. -/
  action : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)]
    (_hP : EquivariantAlgebra P) (M : EquivariantCoherent.Coherent D) (q : ℕ),
    ModObj (EquivariantCoherent.underlying P) (obj q
      (EquivariantCoherent.underlying P) (EquivariantCoherent.underlying M))
  /-- The multiplication action is equivariant. -/
  equivariant : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)]
    (hP : EquivariantAlgebra P) (M : EquivariantCoherent.Coherent D) (q : ℕ),
    letI := action G X D P hP M q
    EquivariantBilinear P (A.tor G X D q P M) (A.tor G X D q P M)
      ((EquivariantCoherent.underlying P ◁ (A.realization G X D q P M).hom) ≫
        (action G X D P hP M q).smul ≫ (A.realization G X D q P M).inv)
  /-- The action is pinned on cycle representatives in every K-flat resolution of M. -/
  normalization : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)]
    (hP : EquivariantAlgebra P) (M : EquivariantCoherent.Coherent D) (q : ℕ)
    (E : CochainComplex
      (SheafOfModules.{u} (moduleRings X.val.left.toRingedSpace)) ℤ)
    (a : E ⟶ (HomologicalComplex.single
      (SheafOfModules.{u} (moduleRings X.val.left.toRingedSpace)) (.up ℤ) 0).obj
        (EquivariantCoherent.underlying M)) [QuasiIso a] (hk : kFlat E),
    letI := action G X D P hP M q
    let C := tensorComplex E (EquivariantCoherent.underlying P)
    let e := symmetry (EquivariantCoherent.underlying P)
      (EquivariantCoherent.underlying M) q ≪≫ resolutionHomologyIso (X := X.val.left) _ _ q E a hk
    ∀ (U : X.val.left.Opens) (p : Γ(EquivariantCoherent.underlying P, U))
      (z w : Γ(C.cycles (-(q : ℤ)), U)),
      (C.iCycles (-(q : ℤ))).val.app (op U) w =
        (coefficientTerm (EquivariantCoherent.underlying P) (E.X (-(q : ℤ)))).app U
          (tmulSection p ((C.iCycles (-(q : ℤ))).val.app (op U) z)) →
      (action G X D P hP M q).smul.app U (tmulSection p
        (e.inv.app U ((C.homologyπ (-(q : ℤ))).val.app (op U) z))) =
          e.inv.app U ((C.homologyπ (-(q : ℤ))).val.app (op U) w)
  /-- Naturality of the module action in the second input. -/
  maps_linear : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)]
    (hP : EquivariantAlgebra P) (M N : EquivariantCoherent.Coherent D)
    (f : M ⟶ N) (q : ℕ),
    let aM := action G X D P hP M q
    let aN := action G X D P hP N q
    aM.smul ≫ map q (𝟙 _) (EquivariantCoherent.underlyingMap f) =
      (EquivariantCoherent.underlying P ◁
        map q (𝟙 _) (EquivariantCoherent.underlyingMap f)) ≫ aN.smul
  /-- Every second-variable connecting morphism is P-linear. -/
  boundary_linear : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)]
    (hP : EquivariantAlgebra P) (L M N : EquivariantCoherent.Coherent D)
    (s : L ⟶ M) (t : M ⟶ N)
    (h : EquivariantCoherent.underlyingMap s ≫ EquivariantCoherent.underlyingMap t = 0)
    (hs : (ShortComplex.mk (EquivariantCoherent.underlyingMap s)
      (EquivariantCoherent.underlyingMap t) h).ShortExact) (q : ℕ),
    let aN := action G X D P hP N (q + 1)
    let aL := action G X D P hP L q
    let d := boundaryRight (EquivariantCoherent.underlying P) _ hs q
    aN.smul ≫ d = (EquivariantCoherent.underlying P ◁ d) ≫ aL.smul
  /-- An ideal killed in the coefficient algebra is killed on every Tor sheaf.
  In particular apply this to the quotient O_X/J and its invariant ideal. -/
  killed : ∀ (G : Space F) [GrpObj G.val] [IsAffine G.val.left]
    (X : Space F) [ModObj G.val X.val]
    (D : EquivariantCoherent.ActionGroupoidModel G.val X.val)
    (P : EquivariantCoherent.Coherent D) [MonObj (EquivariantCoherent.underlying P)]
    (_hP : EquivariantAlgebra P) (M : EquivariantCoherent.Coherent D)
    (q : ℕ) (U : X.val.left.Opens) (j : Γ(X.val.left, U)),
    (∀ p : Γ(EquivariantCoherent.underlying P, U), j • p = 0) →
      ∀ t : Γ(obj q (EquivariantCoherent.underlying P)
        (EquivariantCoherent.underlying M), U), j • t = 0

/-- Equivariant coherent Tor and its exact-sequence calculus, for all finite-type
F-schemes and affine finite-type F-group schemes. All comparison data below is in
the conclusion; Tor is the actual derived tensor homology defined above.

Proof: finite-type schemes over a field are Noetherian. On affine opens resolve a
finite module by a bounded-above complex of finite free modules (unbounded to the
left is allowed). Sheafify, tensor, and identify derived homology with ordinary Tor.
Kernels, images and cokernels of coherent modules are coherent. Tensoring a short
exact sequence by the free resolution gives the full homology long exact sequence;
the signed derived tensor shift gives precisely the boundaries above. Flat pullback
preserves the resolution, and reassociation on pure tensors gives the normalized
base-change comparison. Resolution lifts are unique up to homotopy, so these maps
are natural, agree on overlaps, compose, and commute with connecting maps. Action,
projection and nerve face maps are flat: projections are field base changes, and
(g,x) ↦ (g,gx) identifies action with projection; the same inverse-coordinate argument
handles multiplication. Apply beta to the input linearizations. Composition proves
the cocycle, and restriction of the cocycle to (e,e,x), followed by cancellation of an
invertible idempotent, proves the unit without assuming the unit section flat.
Naturality gives equivariant maps, boundaries, kernels, images, and beta for equivariant
flat maps. Resolving the second input makes coefficient multiplication a unital
associative equivariant action; naturality of boundaries makes the sequence P-linear,
and an ideal killed on P kills the complex and its homology. Finally finite locally
free tensor is locally a finite direct sum, hence exact. Reassociation on the same
resolution gives the normalized equivariant tensor comparison, while the degree-zero
flat resolution of V gives degree zero tensor and vanishing in positive degrees.
Source: Stacks 08BP, 06YH, 00LY, 00LS, 00M7, 00M8, 01BY and 03LF; the eleven
proof steps of the node (blueprint: lem-sfb-equivariant-coherent-tor-calculus). -/
theorem equivariant_coherent_tor_calculus :
    ∃ (B : FlatCalculus F) (A : ActionCalculus F B),
      Nonempty (ExactCalculus F B A) ∧ ResolutionCalculus F ∧
      EquivariantPullbacks F ∧ EquivariantFlatCalculus F B A ∧
      AffineBaseChangeCalculus F B ∧
      Nonempty (LocallyFreeCalculus F B A) ∧ Nonempty (AlgebraCalculus F B A) := by
  sorry

end AlgebraicGeometry.SchemeTor
