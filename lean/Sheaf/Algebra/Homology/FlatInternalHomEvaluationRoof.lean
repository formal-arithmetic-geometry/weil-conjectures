/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData

/-! # Flat scalar extension and the evaluation-normalized internal-Hom roof

Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 0A95; sites-modules.tex,
Tag 03CZ; the evaluation-roof refinement of the final paragraph of blueprint
main-20261015, lem-sfb-dc-hom-preserves.proof.md
(blueprint: lem-sfb-hom-flat-evaluation-roof).

The strict numerator and denominator are the recorded ones. The only representative
identifications introduced here are specified on actual sheafified tensor generators.
All derived comparisons are defined by transposing scalar-extended evaluation.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules WeilConjectures
open WeilConjectures.SfbHomFilteredColimit
open scoped ChangeOfRings

attribute [local irreducible] coefficientTotalTensor homComplexFunctor
  SheafOfModules.monoidalCategory scalarPairComplexComparison

namespace CategoryTheory.SfbFlatHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- The already recorded strict tensor functor with the restricted regular S-module.
This abbreviation uses restriction of scalars and the actual single-zero total tensor.
Source: Stacks 03CZ, 06YN (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable abbrev scalarTensor {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :=
  Prod.sectR ((scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))
    (CochainComplex (scalarModules J R) ℤ) ⋙ tensor.{c, v, r} J R

variable (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison M a)
  (α : ScalarInternalHomAdjunction M μ)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The canonical map c is the transpose of scalar-extended evaluation, with the
inverse strong tensor comparison in front of it. It is defined for all derived inputs.
Source: Stacks 08J9, 07A4 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def comparison (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L) :=
  (M.closed S).transpose _ _ _
    ((μ a).iso.inv.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L), K) ≫
      (M.scalar a).derived.map ((M.closed R).evaluation K L))

/-- The precise map Theta U(c), using the recorded normalized scalar adjunction.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def restrictedComparison (K L : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj L)) :=
  (scalarDerivedRestriction a).map (comparison M μ a K L) ≫
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L)

/-- The exact-extension representative map, using the universal derived counit and
termwise restriction comparison. Its invertibility under exactness is asserted below.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def representative
    (ν : scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ))
    (B : CochainComplex (scalarModules J R) ℤ) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj B)) ⟶
      DerivedCategory.Q.obj ((scalarTensor.{c, v, r} a).obj B) :=
  (scalarDerivedRestriction a).map
      (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B) ≫
    (scalarRestrictionComparison a).hom.app
      ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj B) ≫
    DerivedCategory.Q.map (ν.inv.app B)

/-- The source identification U E^L H_R(QP,QC) to Q(S tensor Hom(P,I(C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def sourceMap
    (ν : scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ))
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      (coefficientHomResolutionIso.{r, c, v, w} J R P L).hom) ≫
    representative M a ν ((homFixed.{c, v, r} J R P).obj L)

/-- The target identification H_R(QP,U E^L QC) to Q(Hom(P,I(S tensor C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def targetMap
    (ν : scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ))
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (representative M a ν L)) ≫
    (coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj L)).hom

/-- The strict denominator v_S = Hom(P,I(S tensor eta_C)), without changing models.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable abbrev denominator
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  roofDenominator.{c, v, r} J R P L
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- The strict numerator a_S is the component of the unique normalized comparison.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable abbrev numerator
    (P L : CochainComplex (scalarModules J R) ℤ) :=
  (WeilConjectures.SfbHomFilteredColimit.comparison.{c, v, r} J R P L).app
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- Inverting precisely the localized denominator; the argument supplies only its proof
of being a quasi-isomorphism, with no choice of any map or object.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def denominatorInverse
    (P L : CochainComplex (scalarModules J R) ℤ) (hv : QuasiIso (denominator.{c, v, r} a P L)) :=
  letI := hv
  inv (DerivedCategory.Q.map (denominator.{c, v, r} a P L))

/-- The full flat evaluation-roof assertion, simultaneously for every coefficient map.
The natural isomorphism nu is fixed by its actual pure-tensor formula. The remaining
fields are propositions about the recorded models and explicitly defined maps.
Coefficient composition includes identity maps and, by the two paths in a commutative
square, arbitrary compatible coefficient maps.
Source: Stacks 08J9, 0A95, 03CZ and the node's evaluation-roof refinement
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
structure EvaluationRoof where
  /-- The canonical tensor/restricted-extension identification, before localization. -/
  tensorIso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    scalarTensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ)
  /-- On actual sheafified generators, nu sends s tensor x to s tensor x. -/
  tensorIso_normalized : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (B : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (B.X n).val.obj V),
    (((tensorIso a).hom.app B).f n).val.app V
        (tensorGenerator.{c, v, r} J R _ B n V s x) =
      ((eqToHom ((M.scalar a).extension_obj (B.X n)).symm).val.app V)
        ((toSheafify J (changeOfRingsPresheaf a (B.X n)).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))
  /-- Exact ordinary extension computes derived extension on every complex. -/
  exact_computes : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ B : CochainComplex (scalarModules J R) ℤ,
      IsIso (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B)
  /-- No boundedness or continuity is needed for the strict denominator. -/
  denominator_quasiIso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ (P L : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      QuasiIso (denominator.{c, v, r} a P L)
  /-- The equation [v_S] Theta U(c) = [a_S], with both representative transports. -/
  equation : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ (P L : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
          targetMap M a (tensorIso a) P L ≫ DerivedCategory.Q.map (denominator.{c, v, r} a P L) =
        sourceMap M a (tensorIso a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L)
  /-- Equivalently Theta U(c) is the numerator followed by the inverse denominator. -/
  roof : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ (P L : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      ∀ hv : QuasiIso (denominator.{c, v, r} a P L),
        restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
            targetMap M a (tensorIso a) P L =
          sourceMap M a (tensorIso a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫
            denominatorInverse.{c, v, r, w} a P L hv
  /-- Naturality in both derived inputs, including maps represented by inverse quasi-isos. -/
  naturality : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (K K' L L' : DerivedCategory (scalarModules J R)) (f : K' ⟶ K) (g : L ⟶ L'),
    (scalarDerivedRestriction a).map ((M.scalar a).derived.map
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g))) ≫
        restrictedComparison M μ α a K' L' =
      restrictedComparison M μ α a K L ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom f.op ((scalarDerivedRestriction a).map ((M.scalar a).derived.map g)))
  /-- Coefficient compatibility, with the unit-normalized scalar composition transports. -/
  coefficients : ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
    (K L : DerivedCategory (scalarModules J R)),
    comparison M μ (a ≫ b) K L =
      (scalarHomExtensionComp M a b).inv.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
        (M.scalar b).derived.map (comparison M μ a K L) ≫
          comparison M μ b ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L) ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J T).map
              (Prod.mkHom ((scalarHomExtensionComp M a b).inv.app K).op
                ((scalarHomExtensionComp M a b).hom.app L))

/-- Flat scalar comparison is precisely the evaluation-normalized strict resolution roof.
All presentations are those of the dependency nodes, and no finite basis, colimit
continuity, or bound on either complex is assumed.

Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 0A95; sites-modules.tex,
Tag 03CZ; blueprint main-20261015, lem-sfb-dc-hom-preserves.proof.md, final paragraph,
as refined by the six proof steps of the DAG node
(blueprint: lem-sfb-hom-flat-evaluation-roof).

Proof:
1. Exact extension commutes with cohomology and preserves quasi-isomorphisms.
   Resolve an arbitrary complex by a flat-term K-flat complex. The universal derived
   counit and preservation of this resolution make its exact-extension representative
   comparison invertible. Apply this to E eta_C. Naturality and two-out-of-three show
   I_R(E eta_C) is a quasi-isomorphism between K-injectives. Hom invariance proves v_S
   is a quasi-isomorphism (Tags 010N, 06YY, 0A95).
2. Set J_C = I_R(C) and B = Hom(P,J_C). The one-K-flat chain-transpose lemma computes
   evaluation by B tensor P to J_C followed by the inverse localized eta_C. It also
   applies to the arbitrary complex S tensor B; this complex need not be K-flat.
3. The scalar chain identification gives h((s tensor f) tensor p) = s tensor f(p).
   The strict numerator has uncurry eta_(S tensor J_C) composed with h, by its fixed
   pure-tensor and Hom-product-projection normalization. Its derived transpose is [h].
4. Resolve B by a flat-term K-flat T. On T,P the normalized scalar tensor comparison
   is the actual chain tensor identification. Tensoring with P and applying exact E
   preserve the resolution quasi-isomorphisms. Descent therefore gives the same h
   on S tensor B, without asserting that arbitrary tensor computes derived tensor.
5. The normalized scalar adjunction makes the transpose of Theta U(c) equal to
   [E eta_C] inverse composed with [h]. Postcomposition by [v_S] cancels this inverse.
   The transpose becomes [h], equal to the numerator's transpose by step 3.
   Injectivity of the closed transpose gives the equation; inversion of [v_S] gives
   the equivalent roof formula.
6. Evaluation commutes with precomposition in P and postcomposition in C. Naturality
   of the fixed resolution unit, scalar tensor square and scalar adjunction gives
   these equations on representatives and their inverse quasi-isomorphisms, hence
   on all derived morphisms. The same calculation with successive scalar units and
   the unit-normalized scalar composition isomorphisms gives coefficient compatibility.
   Both paths of a compatible coefficient square have the same evaluation transpose.
   Identity coefficients are included. No finite freeness, continuity or bound occurs. -/
theorem evaluationRoof : Nonempty (EvaluationRoof M μ α) := by
  sorry

end CategoryTheory.SfbFlatHom
