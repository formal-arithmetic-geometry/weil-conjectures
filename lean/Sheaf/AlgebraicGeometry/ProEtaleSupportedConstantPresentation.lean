/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Cokernel presentation of the supported constant pro-etale module

Source: Milne, Lectures on Etale Cohomology, Section 9, proof of Theorem 9.4, p. 67;
Stacks Project, Tag 09AH is the quasi-compact-open model only. The finite-coefficient
argument below does not require a quasi-compact open complement
(blueprint: lem-pur-proetale-supported-constant-presentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Constant sections restrict to the same constants on the open localization.
This is the sheafification extension of the scalar-preserving presheaf map.
Source: Milne, Section 9; Stacks, Tag 09AE
(blueprint: lem-pur-proetale-supported-constant-presentation). -/
noncomputable def proEtaleFixedOpenConstantMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    proEtaleFixedConstantModule U A ⟶
      (ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          (proEtaleFixedConstantModule X A) :=
  ((sheafificationAdjunction (ProEt.topology U)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).homEquiv _ _).symm
      (Functor.whiskerLeft (MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale j)).op
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))

/-- The open adjunction counit at the constant module. The realization unit identifies
its open coefficient with the same constant module, and the uniquely normalized rank-one
comparisons identify both coefficients with their constant ring sheaves.
Source: Milne, Section 9; Stacks, Tags 09AE and 00YV
(blueprint: lem-pur-proetale-supported-constant-presentation). -/
noncomputable def proEtaleOpenConstantCounit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).obj (proEtaleConstantModule U A) ⟶
      proEtaleConstantModule X A :=
  (sfIntrinsicExtensionByZero j A).map (proEtaleConstantModuleUnit U A).inv ≫
    (sfIntrinsicModuleEquivalence X A).functor.map
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
          ((sfIntrinsicModuleEquivalence U A).unitIso.inv.app
            (proEtaleFixedConstantModule U A))) ≫
    (sfIntrinsicModuleEquivalence X A).functor.map
      (((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _).symm
          (proEtaleFixedOpenConstantMap j A)) ≫
    (proEtaleConstantModuleUnit X A).hom

/-- Constant restriction to the closed subscheme, realized in the ordinary module category.
The fixed-scalar arrow extends a ↦ a on the base-changed object. The direct-image
comparison is normalized on scalar-unit sections, and the rank-one comparisons also
preserve constants. Thus its component sends each constant a to that same constant on
W ×[X] Z. Source: Milne, Section 9; Stacks, Tags 09A5 and 03D1
(blueprint: lem-pur-proetale-supported-constant-presentation). -/
noncomputable def proEtaleClosedConstantRestriction {Z X : Scheme.{u}} (i : Z ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleConstantModule X A ⟶
      (proEtaleConstantModuleDirectImage i A).obj (proEtaleConstantModule Z A) :=
  (proEtaleConstantModuleUnit X A).inv ≫
    (sfIntrinsicModuleEquivalence X A).functor.map
      (proEtaleConstantDirectImageMap i
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))) ≫
    (sfIntrinsicDirectImageComparison i A).inv.app (proEtaleFixedConstantModule Z A) ≫
    (proEtaleConstantModuleDirectImage i A).map (proEtaleConstantModuleUnit Z A).hom

/-- The constant restriction is the cokernel of the open constant counit, with no
quasi-compactness assumption on the open complement and no finiteness condition on X.
Source: Milne, Section 9, proof of Theorem 9.4, p. 67; finite pro-etale adaptation of
Stacks, Tag 09AH (blueprint: lem-pur-proetale-supported-constant-presentation).

Proof (the node's five steps):
1. By lem-pur-proetale-finite-constant-sections, constant sheaf sections are continuous
   functions to finite discrete A. The restriction rho is restriction of functions,
   by uniqueness of sheafification. On the extension presheaf P, the map to A_X is the
   identity over U and zero otherwise. Its composite with rho is zero since V_Z is
   empty over U. Module sheafification therefore gives rho epsilon = 0.
2. For affine V, its closed subspace V_Z is quasi-compact, by closed-immersion base
   change and affine quasi-compactness. The finitely many clopen fibres of a section
   V_Z → A admit ambient open neighbourhoods. Finitely many affine neighbourhoods
   inside them cover V_Z. Cover the remaining closed quasi-compact subset of V by
   finitely many affine opens contained in V_U. On each chosen open a constant lifts
   the section, or zero lifts it over V_U. These form a finite Zariski, hence pro-etale,
   cover. General objects are first covered by affines. Thus rho is locally surjective.
3. A section g of ker rho vanishes on V_Z. Its clopen nonzero locus D lies over U;
   its clopen zero locus E complements D. On D lift g through P → j_!A_U and on E
   take zero. Glue to q(g). Pullback preserves these loci, so q is natural. Refining
   the two-piece covers for two sections proves addition and scalar linearity.
4. Let h : j_!A_U → ker rho be the factorization from step 1. On (D,E), epsilon q
   is the kernel inclusion, hence hq = 1. Precompose qh with P → j_!A_U: over U it
   is that unit, and off U the presheaf has value zero. Uniqueness in module
   sheafification gives qh = 1. Thus epsilon identifies its source with ker rho.
5. Local surjectivity makes rho epic by sheaf gluing. Its kernel is the image of
   epsilon, so j_!A_U → A_X → i_*A_Z → 0 is exact. In the abelian category an epic
   arrow with that kernel is a cokernel. The displayed IsColimit is exactly this
   cokernel universal property; the proof uses no geometric-stalk conservativity. -/
theorem proEtale_supported_constant_presentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : proEtaleOpenConstantCounit i.openComplement.ι A ≫
        proEtaleClosedConstantRestriction i A = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (proEtaleClosedConstantRestriction i A) h)) := by
  sorry

end AlgebraicGeometry.Scheme
