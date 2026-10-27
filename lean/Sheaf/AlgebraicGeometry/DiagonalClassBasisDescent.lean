/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingPairOpenRigidity
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Descent of normalized diagonal classes on an arbitrary open basis

Source: Stacks Project, duality.tex, Tag 0E2W; cohomology.tex, Tags 0D66 and 0D68;
sites-cohomology.tex, Tags 08JA and 08JB.
(blueprint: lem-trf-diagonal-class-basis-descent).
The scalar identification is specified by its inverse s ↦ multiplication by s followed
by the given class. Linearity is written as additivity and its explicit scalar equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- Exact restriction to an open subscheme, with its derived-category endpoints explicit.
Source: Stacks 0E2W (blueprint: lem-trf-diagonal-class-basis-descent). -/
def diagonalBasisRestriction (X : Scheme.{u}) (U : X.Opens) :
    schemeDerivedCategory X ⥤ schemeDerivedCategory U.toScheme :=
  (relativeDualizingOpenRestriction U.ι).mapDerivedCategory

/-- The group of diagonal classes with the specified coefficient object.
Source: Stacks 0E2W (blueprint: lem-trf-diagonal-class-basis-descent). -/
abbrev DiagonalClassHom {X S : Scheme.{u}} (f : X ⟶ S) (K : schemeDerivedCategory X) :=
  DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
    (derivedPullback (pullback.fst f f)).obj K

/-- Multiplication by a global section on the diagonal object in degree zero.
Source: Stacks 0E2W, scalar description (blueprint: lem-trf-diagonal-class-basis-descent).
This is the ordinary multiplication map on O_X, pushed along the diagonal and localized. -/
def diagonalClassSectionAction {X S : Scheme.{u}} (f : X ⟶ S)
    (s : Γ(X, ⊤)) :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) :=
  DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
    ((SheafOfModules.pushforward (pullback.diagonal f).toRingCatSheafHom).map
      (Scheme.Modules.smulHom (Scheme.Modules.unit X) s)))

/-- The already defined, section-normalized restriction of a diagonal class to U ×_S U.
Source: Stacks 0E2W, 0E2X (blueprint: lem-trf-diagonal-class-basis-descent). -/
def diagonalBasisClass {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (K : schemeDerivedCategory X)
    (ξ : DiagonalClassHom f K) :
    DiagonalClassHom (U.ι ≫ f) ((diagonalBasisRestriction X U).obj K) :=
  relativeDualizingOpenClass f (U.ι ≫ f) U.ι (𝟙 S) (by simp) K ξ

/-- Preservation of the restricted diagonal class by a local morphism.
Source: Stacks 0E2W (blueprint: lem-trf-diagonal-class-basis-descent). -/
def IsDiagonalBasisNormalized {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (K L : schemeDerivedCategory X) (ξ : DiagonalClassHom f K) (η : DiagonalClassHom f L)
    (a : (diagonalBasisRestriction X U).obj K ⟶ (diagonalBasisRestriction X U).obj L) :
    Prop :=
  diagonalBasisClass f U K ξ ≫
      (derivedPullback (pullback.fst (U.ι ≫ f) (U.ι ≫ f))).map a =
    diagonalBasisClass f U L η

/-- Iterated open restriction compared with direct restriction, using the pinned
pullback composition and exact-open-restriction comparisons.
Source: Stacks 0D68, 0E2W (blueprint: lem-trf-diagonal-class-basis-descent). -/
def diagonalBasisRestrictionIso {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    (diagonalBasisRestriction X U) ⋙
        derivedPullback (X.homOfLE h) ≅
      (diagonalBasisRestriction X V) :=
  Functor.isoWhiskerRight (relativeDualizingOpenPullbackIso U.ι).symm _ ≪≫
    relativeMVComp (X.homOfLE h) U.ι ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.homOfLE_ι X h)) ≪≫
    relativeDualizingOpenPullbackIso V.ι

/-- Restriction of a local comparison along an inclusion of basis opens.
Source: Stacks 0D68, 0E2W (blueprint: lem-trf-diagonal-class-basis-descent). -/
def diagonalBasisHomRestriction {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    {K L : schemeDerivedCategory X}
    (a : (diagonalBasisRestriction X U).obj K ⟶
      (diagonalBasisRestriction X U).obj L) :
    (diagonalBasisRestriction X V).obj K ⟶
      (diagonalBasisRestriction X V).obj L :=
  (diagonalBasisRestrictionIso h).inv.app K ≫
    (derivedPullback (X.homOfLE h)).map a ≫ (diagonalBasisRestrictionIso h).hom.app L

/-- Normalized local isomorphisms descend uniquely, and the diagonal Hom group is
canonically the module of global functions, compatibly with every basis restriction.
Source: Stacks 0E2W, 0D66(2), 0D68, 08JA and 08JB
(blueprint: lem-trf-diagonal-class-basis-descent).

Proof, following the six steps of the node:
1. Restrict a normalized local isomorphism from U to V. The canonical diagonal and
pullback comparisons preserve its normalization, so uniqueness on V gives compatibility.
2. Local isomorphisms identify all negative cross Hom groups with negative self Hom
of K. Apply lem-trf-derived-basis-local-hom-glue to the maps and their inverses.
Its injectivity for both self Hom groups makes the two composites identities and gives
unique gluing of the isomorphisms, with no finite-cover assumption.
3. Transpose multiplication followed by eta with def-pc-canonical-derived-tensor-hom-
bijection. Invertibility of this transpose identifies maps O_Y[0] → D with maps D → M.
The fully faithful single functor (lem-weil-pbc-derived-single-fully-faithful) identifies
the former with sections on X. Tensor-Hom naturality and the left unitor of
def-pc-scheme-derived-tensor-structure identify the resulting map with s ↦ m_s;eta.
Its inverse sends eta to 1. Additivity and m_s m_t = m_st prove scalar linearity.
4. The ordinary diagonal algebra restricts with its unit and products. Apply
lem-weil-pbc-ringed-internal-hom-exact-restriction and
lem-weil-pbc-ringed-slice-evaluation-transpose to identify the restricted transpose
with multiplication by eta_U. The same inverse formula gives Phi_U, and the sectionwise
restriction of m_s proves compatibility of Phi and Phi_U.
5. For the glued a, put h = xi;Lp1*(a). Its restriction is eta_U, so Phi(h) restricts
to 1 on the basis. Sheaf separatedness on X gives Phi(h)=1, hence h=eta. No claim that
U ×_S U covers Y is needed.
6. Any other globally normalized isomorphism restricts to the uniquely normalized
local ones. Unique Hom gluing identifies it with a. The empty scheme and empty basis
are covered by the same empty-cover sheaf and Hom-gluing assertions. -/
theorem diagonalClass_basis_descent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (K L : schemeDerivedCategory X)
    (ξ : DiagonalClassHom f K)
    (η : DiagonalClassHom f L)
    (hη : IsIso (relativeDualizingClassMap f L η))
    (B : Set X.Opens)
    (hB : ∀ O : X.Opens, sSup {U : X.Opens | U ∈ B ∧ U ≤ O} = O)
    (hnegative : ∀ U ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton ((diagonalBasisRestriction X U).obj K ⟶
        ((diagonalBasisRestriction X U).obj K)⟦i⟧))
    (hlocal : ∀ U ∈ B,
      ∃! a : (diagonalBasisRestriction X U).obj K ≅
          (diagonalBasisRestriction X U).obj L,
        IsDiagonalBasisNormalized f U K L ξ η a.hom) :
    (∀ (a : ∀ U : {U : X.Opens // U ∈ B},
        (diagonalBasisRestriction X U.val).obj K ≅
          (diagonalBasisRestriction X U.val).obj L),
      (∀ U : {U : X.Opens // U ∈ B},
        IsDiagonalBasisNormalized f U.val K L ξ η (a U).hom) →
      (∀ (U V : {U : X.Opens // U ∈ B}) (h : V.val ≤ U.val),
        diagonalBasisHomRestriction h (a U).hom = (a V).hom) ∧
      (∃! α : K ≅ L, ∀ U : {U : X.Opens // U ∈ B},
        (diagonalBasisRestriction X U.val).map α.hom =
          (a U).hom)) ∧
    (∃ Φ : (DiagonalClassHom f L) ≃+ Γ(X, ⊤),
      (∀ s : Γ(X, ⊤), Φ.symm s = diagonalClassSectionAction f s ≫ η) ∧
      Φ η = 1 ∧
      (∀ (s : Γ(X, ⊤)) (h : DiagonalClassHom f L),
        Φ (diagonalClassSectionAction f s ≫ h) = s * Φ h) ∧
      ∀ U ∈ B,
        ∃ ΦU : (DiagonalClassHom (U.ι ≫ f) ((diagonalBasisRestriction X U).obj L)) ≃+
            Γ(U.toScheme, ⊤),
          (∀ s : Γ(U.toScheme, ⊤),
            ΦU.symm s = diagonalClassSectionAction (U.ι ≫ f) s ≫
              diagonalBasisClass f U L η) ∧
          ∀ h : DiagonalClassHom f L,
            ΦU (diagonalBasisClass f U L h) = U.ι.appTop (Φ h)) ∧
    (∃! α : K ≅ L, ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η) ∧
    (∀ (α : K ≅ L),
      (∀ U ∈ B,
        IsDiagonalBasisNormalized f U K L ξ η
          ((diagonalBasisRestriction X U).map α.hom)) →
        ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η) := by
  sorry

end AlgebraicGeometry
