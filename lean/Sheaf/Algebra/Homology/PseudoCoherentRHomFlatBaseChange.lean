/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.MixedGlobalExtension
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.NormalizedRingHomExtension
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.PerfectRingHomScalarExtension
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

-- The high-priority successor-universe sheafification instance gets stuck on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! # Flat scalar extension of pseudo-coherent derived Hom

Source: Stacks Project, more-algebra.tex, Tag 0A6A(3), Equation 0E1X and Tag 0E1W
(blueprint: lem-trf-pseudocoherent-rhom-flat-base-change).

Modules are encoded on the existing one-object site with bottom topology.
Pseudo-coherence uses `DerivedCategory.IsPseudoCoherent` after evaluating a complex
representative at the unique object. The scalar models and internal-Hom adjunction
are the existing normalized constructions; their existence is
`scalarInternalHomAdjunction_exists`. The displayed component equation specifies the
map on all derived objects, and the natural transformation supplies naturality for
all derived morphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w m

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

/-- Flat scalar extension commutes with derived Hom from a pseudo-coherent object
into a cohomologically bounded-below object, naturally in both derived objects.
The component is precisely the scalar adjoint of Hom applied to the scalar unit,
followed by the inverse of the normalized internal-Hom adjunction (Stacks 0E1W).
The existential natural transformation is therefore uniquely specified, rather than
an arbitrary comparison. The module localization universe `m` is independent of `w`.

Source: Stacks Project, more-algebra.tex, Tag 0A6A(3), Equation 0E1X and Tag 0E1W
(blueprint: lem-trf-pseudocoherent-rhom-flat-base-change).

Proof:
1. By def-pc-ring-pseudo-coherent-complex choose a bounded-above finite-free model P
   for E. By def-sbc-standard-tstructure-derived-category choose a representative N
   of L with N^q = 0 for q < a. Evaluation on the one-object bottom-topology site
   identifies these with ordinary module complexes.
2. Flat tensor is exact (lem-weil-pbc-flat-tensor-exact). Apply it to the sequences
   defining cycles and boundaries to identify H^i(F C) with S tensor H^i(C), for
   every complex C. Hence F preserves all quasi-isomorphisms, without boundedness.
3. Resolve C by a K-flat complex (lem-pc-kflat-resolution). The derived computation
   of lem-pur-derived-change-of-rings and Step 2 identify LF(Q C) with Q(F C).
   The normalized scalar adjunction identifies its unit with x mapped to 1 tensor x;
   this is the extension/restriction adjunction of lem-sc-mixed-global-extension-adjunction.
4. The product-total Hom complex Hom(P,N) computes RHom(E,L), naturally in the
   representatives, by lem-pod-projective-hom-evaluation-model. The same applies
   over S to FP,FN, since finite free terms remain finite free and bounded above.
   The differential is the one of def-pur-hom-complex.
5. Lem-pc-normalized-ring-hom-extension supplies the shared chain comparison
   chi(s tensor f)_p(t tensor x) = st tensor f_p(x). Its projections agree with
   the extension-data part of def-pc-perfect-rhom-base-change-map; no perfect-source
   derived comparison is applied to E.
6. In degree n truncate P stupidly below c = a-n (def-kun-truncations). All removed
   Hom factors have zero target. Thus the degree-n comparison is the comparison
   for the bounded finite-free truncation, invertible by
   lem-pc-perfect-ring-hom-scalar-extension. This works separately in every degree;
   the inverses commute with the differentials, so chi is a complex isomorphism.
7. The internal-Hom adjunction restricts an S-linear family by x mapped to 1 tensor x.
   Hom applied to the unit sends f to (x mapped to 1 tensor f(x)); its scalar adjoint
   sends s tensor f to (t tensor x mapped to st tensor f(x)). Hence Q(chi) is exactly
   the component specified below. Functoriality of Hom, the unit and adjunction gives
   naturality for arbitrary derived morphisms, and Step 6 gives its invertibility.
No Noetherian or perfectness hypothesis is used. -/
theorem exists_pseudoCoherentRHomFlatBaseChange
    [∀ O : Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{u + 1})) CommRingCat.{u},
      HasDerivedCategory.{w} (scalarModules ⊥ O)]
    (M : ScalarHomModels.{u, u, u, w} (⊥ : GrothendieckTopology (Discrete PUnit.{u + 1})))
    (μ : ∀ {O T : Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{u + 1})) CommRingCat.{u}}
      (a : O ⟶ T), ScalarHomTensorComparison.{u, u, u, w} M a)
    (α : ScalarInternalHomAdjunction.{u, u, u, w} M μ)
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{m} (ModuleCat.{u} R)]
    (φ : R →+* S) (hφ : φ.Flat) :
    ∃ χ : derivedInternalHomOfUniverses.{u, u, u, w} ⊥
          (CochainComplex.onePointRingSheaf R) ⋙ (M.scalar (ringSiteMap.{u} φ)).derived ⟶
        (((M.scalar (ringSiteMap.{u} φ)).derived.op).prod
          (M.scalar (ringSiteMap.{u} φ)).derived) ⋙
            derivedInternalHomOfUniverses.{u, u, u, w} ⊥
              (CochainComplex.onePointRingSheaf S),
      (∀ E L : DerivedCategory (RingSiteModules R),
        χ.app (op E, L) = ((M.scalar (ringSiteMap.{u} φ)).adjunction.homEquiv _ _).symm
          ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
              (CochainComplex.onePointRingSheaf R)).map
            (Prod.mkHom (𝟙 (op E)) ((M.scalar (ringSiteMap.{u} φ)).adjunction.unit.app L)) ≫
              (α.iso (ringSiteMap.{u} φ)).inv.app
                (op E, (M.scalar (ringSiteMap.{u} φ)).derived.obj L))) ∧
      (∀ E L : DerivedCategory (RingSiteModules R),
        (∃ P : CochainComplex (RingSiteModules R) ℤ,
          Nonempty (DerivedCategory.Q.obj P ≅ E) ∧
            DerivedCategory.IsPseudoCoherent (A := R)
              ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj
                (((SheafOfModules.evaluation (R := (sheafCompose ⊥
                  (forget₂ CommRingCat.{u} RingCat.{u})).obj
                    (CochainComplex.onePointRingSheaf R)) (op ⟨PUnit.unit⟩)).mapHomologicalComplex
                      (.up ℤ)).obj P))) →
        (∃ a : ℤ, ∀ i : ℤ, i < a →
          IsZero ((DerivedCategory.homologyFunctor (RingSiteModules R) i).obj L)) →
        IsIso (χ.app (op E, L))) := by
  sorry

end CategoryTheory
