module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Paper.RingComplexGodementConstruction
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction
import Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension
import Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Transfer of a dualizing complex along a finite ring map

Source: Stacks Project, dualizing.tex, Tags 0AX0 (lemma-dualizing-finite) and
0A7B (definition-dualizing), and more-algebra.tex, Tag 0A5S
(definition-injective-dimension) (blueprint: lem-trf-finite-map-dualizing-transfer).

The ordinary module categories use the shared one-object ringed sites. The
transferred complex has the actual precomposition B-action, constructed from
ordinary coinduction, not an arbitrary lift of its underlying A-object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- RHom_A(B,L) as a B-complex, with (b • h)(x) = h(x*b).
Choose the localization's representative of L, apply the existing functorial
K-injective replacement on the one-object A-site, evaluate at its unique object,
apply ordinary coinduction degreewise, and use the existing constant-module
embedding on the B-site. Evaluation and the constant embedding are inverse exact
equivalences on this site. Thus evaluation preserves K-injectivity, and this
is precisely the K-injective Hom model of RHom_A(B,L) with its prescribed action.
The replacement and all coinduction and embedding data are existing constructions.
Source: Stacks Project, Tags 0AX0 and 0A70
(blueprint: lem-trf-finite-map-dualizing-transfer). -/
def finiteMapDualizingComplex {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{u} (RingSiteModules A)]
    [HasDerivedCategory.{u} (RingSiteModules B)]
    (L : DerivedCategory (RingSiteModules A)) : DerivedCategory (RingSiteModules B) :=
  letI := AlgebraicGeometry.ringComplexConstant_additive (CommRingCat.of B)
  letI := (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  Q.obj (((AlgebraicGeometry.ringComplexConstant (CommRingCat.of B)).mapHomologicalComplex
    (.up ℤ)).obj (((ModuleCat.coextendScalars f).mapHomologicalComplex (.up ℤ)).obj
      (((SheafOfModules.evaluation.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf A)) (op ⟨PUnit.unit⟩)).mapHomologicalComplex
            (.up ℤ)).obj ((CochainComplex.kInjectiveResolutionFunctor.{u} (RingSiteModules A)).obj
              (Q.objPreimage L)))))

/-- Finite-map transfer preserves the three defining properties of a dualizing complex.
The scalar-action arrows are the transposes of the left unitors under the existing
representative-normalized tensor--Hom adjunction. Its tensor unit is the ring in
cohomological degree zero, so these are precisely the homothety maps in Tag 0A7B.
Source: Stacks Project, Tag 0AX0, expanded using Tags 0A7B and 0A5S
(blueprint: lem-trf-finite-map-dualizing-transfer).

Proof:
1. Restriction of scalars preserves monomorphisms and has right adjoint Hom_A(B,-).
The adjunction sends f to n ↦ f(n)(1), with inverse g ↦ (n ↦ (b ↦ g(b*n))).
Hence coinduction preserves injectives by lem-exc-rg-right-adjoint-preserves-injectives.
2. Choose the bounded injective representative I of L. It is K-injective by
lem-weil-pbc-bounded-below-injectives-kinjective. The canonical comparisons of
lem-trf-derived-coinduction-adjunction identify finiteMapDualizingComplex f L
with Hom_A(B,I). This has injective B-terms by step 1 and vanishes outside
I's finite term interval, proving the bounded injective conclusion.
3. Apply lem-trf-coherent-rhom-finite-injective-dimension to K=B[0] and L.
The finite-map hypothesis gives finite A-cohomology of B[0]. Thus RHom_A(B,L)
has finite A-cohomology. Every finite A-generating family also B-generates,
since its B-span contains its A-span. This proves finite B-cohomology.
4. Set T=RHom_A(L,L). The assumed scalar-action isomorphism identifies T with
A[0], of Tor amplitude [0,0]. Every truncation of B[0] is zero or B[0], hence
is pseudo-coherent by lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion.
Apply lem-trf-derived-evaluation-finite-injective with K=B[0] and both targets L.
It makes B[0] = A[0] tensor B[0] to T tensor B[0] to RHom_A(RHom_A(B,L),L)
an isomorphism. Since scalar 1 acts as id_L, its transpose is evaluation;
thus this is the actual canonical biduality arrow b ↦ (h ↦ h(b)).
5. The internal adjunction of lem-trf-algebraic-shriek-derived-hom-adjunction
identifies restriction of RHom_B(Omega,Omega) with RHom_A(U(Omega),L).
Evaluation at 1 sends scalar b acting on Omega to h ↦ (b*h)(1)=h(b).
Hence restriction of the B-scalar-action arrow is exactly the isomorphism
of step 4. Restriction reflects isomorphisms by
lem-trf-derived-coinduction-adjunction, proving the last conclusion. -/
theorem finite_map_dualizing_transfer
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B)
    (hfinite : Module.Finite A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    [HasDerivedCategory.{u} (RingSiteModules A)]
    [HasDerivedCategory.{u} (RingSiteModules B)]
    (L : DerivedCategory (RingSiteModules A))
    (hL : ∀ i : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) i).obj L).val.obj (op ⟨PUnit.unit⟩)))
    (hI : ∃ I : CochainComplex (RingSiteModules A) ℤ,
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q)) ∧
      (∀ q : ℤ, Injective (I.X q)) ∧ Nonempty (Q.obj I ≅ L))
    (hscalar : IsIso ((SignedRingedHom.adjunction ⊥
      (CochainComplex.onePointRingSheaf A) L).homEquiv _ _ (λ_ L).hom)) :
    (∀ i : ℤ, Module.Finite B
      (((homologyFunctor (RingSiteModules B) i).obj
        (finiteMapDualizingComplex f L)).val.obj (op ⟨PUnit.unit⟩))) ∧
    (∃ J : CochainComplex (RingSiteModules B) ℤ,
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (J.X q)) ∧
      (∀ q : ℤ, Injective (J.X q)) ∧
      Nonempty (Q.obj J ≅ finiteMapDualizingComplex f L)) ∧
    IsIso ((SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf B)
      (finiteMapDualizingComplex f L)).homEquiv _ _
        (λ_ (finiteMapDualizingComplex f L)).hom) := by
  sorry

end DerivedCategory
