/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Lifting a supported quotient section to an affine nonvanishing locus

Source: Stacks Project, Modules on Schemes, Tag 0B5P,
`lemma-quasi-compact-h1-zero-invertible`, first paragraph of the proof
(blueprint: lem-trf-supported-section-h1-affine-lift).

The inclusion `j` is fixed by its composite with the ideal inclusion. The tensor
quotient map and multiplication map are fixed by equalities, so no arbitrary
injection replaces multiplication. Nonzero germ of `q` is equivalent to nonzero
image under the canonical stalk quotient identification, since that identification
is an isomorphism. Stalk ideals are written using localization from the affine `U`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A quotient section with nonzero germ lifts, and its image in the line bundle has
an affine principal nonvanishing locus inside the given affine trivializing open.

Source: Stacks Project, Modules on Schemes, Tag 0B5P,
`lemma-quasi-compact-h1-zero-invertible`, first paragraph of the proof
(blueprint: lem-trf-supported-section-h1-affine-lift).

Proof:
1. Module sheaves form an abelian category with enough injectives
   (lem-sc-ringed-space-module-sheaves-enough-injectives). Global sections is additive
   and left exact (lem-sc-global-sections-left-exact). Apply the right-derived delta
   functor (lem-weil-pbc-right-derived-universal-delta-functor, pqf-def-cohomology) to
   the short exact tensor sequence. Its degree-zero identification gives the actual
   section map of the cokernel projection followed by tensoring with `M`.
2. The connecting homomorphism lands in the zero first cohomology group. Exactness
   gives `t` mapping to `q`. Put `s = ι(t)`. At `x`, the canonical quotient identifies
   the germ of `q` with the residue of `s` modulo the maximal ideal times `M_x`.
   Thus the nonzero germ hypothesis puts `x` in the nonvanishing locus.
3. At a point outside `U`, every germ of `I` has zero image in the residue field,
   by the defining vanishing ideal and def-weil-pbc-module-stalk,
   def-weil-residue-field. Hence `I_z` lies in the maximal ideal.
4. By lem-pc-ringed-space-module-stalk-tensor, `t_z` is a finite sum of pure tensors.
   Canonical multiplication sends it into the maximal ideal times `M_z`, by step 3.
   Consequently `s` has zero residue outside `U`.
5. The generator `a` gives the unique `f` with `s` restricted to `U` equal to `f a`.
   At points of `U`, its residue is nonzero exactly when the germ of `f` is a unit.
   Together with steps 2 and 4 this identifies the whole nonvanishing locus with `U_f`.
6. The affine basic-open calculation of
   lem-weil-pbc-affine-open-section-vanishing-prime identifies `U_f` with the basic
   open of `f` in the affine `U`. This open is affine. -/
theorem exists_supported_section_h1_affine_lift
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (M : X.Modules) [M.IsInvertible]
    (a : Γ(M, U)) (ha : Function.Bijective (fun f : Γ(X, U) ↦ f • a))
    (I J : X.IdealSheafData)
    (hI : I = Scheme.IdealSheafData.vanishingIdeal
      ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩)
    (j : J.toModules ⟶ I.toModules) (hj : j ≫ I.toModulesι = J.toModulesι)
    (hJx : (J.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hx).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hIx : (I.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hx).hom = ⊤)
    (hseq : ∃ hz : (j ▷ M) ≫ (cokernel.π j ▷ M) = 0,
      (ShortComplex.mk (j ▷ M) (cokernel.π j ▷ M) hz).ShortExact)
    (π : I.toModules ⊗ M ⟶ cokernel j ⊗ M) (hπ : π = cokernel.π j ▷ M)
    (ι : I.toModules ⊗ M ⟶ M) (hι : ι = (I.toModulesι ▷ M) ≫ (λ_ M).hom)
    [Mono ι] (q : Γ(cokernel j ⊗ M, ⊤))
    (hq : TopCat.Presheaf.germ (cokernel j ⊗ M).val.presheaf ⊤ x trivial q ≠ 0)
    (hH1 : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (J.toModules ⊗ M))) :
    ∃ (t : Γ(I.toModules ⊗ M, ⊤)) (s : Γ(M, ⊤)) (f : Γ(X, U)) (V : X.Opens),
      π.app ⊤ t = q ∧ s = ι.app ⊤ t ∧
      x ∈ nonvanishingLocus M s ∧
      (∀ z : X, z ∉ U → z ∉ nonvanishingLocus M s) ∧
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = f • a ∧
      (V : Set X) = nonvanishingLocus M s ∧ V = X.basicOpen f ∧
      (V : Set X) = {y | ∃ hy : y ∈ U, IsUnit (X.presheaf.germ U y hy f)} ∧
      x ∈ V ∧ V ≤ U ∧ IsAffineOpen V := by
  sorry

end AlgebraicGeometry.Scheme.Modules
