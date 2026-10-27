/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.FiniteNormalRelativeCurveModel
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants
import Sheaf.RingTheory.PolynomialDistinctLinearCRT
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import Sheaf.AlgebraicGeometry.FiniteCurveGenusMonotonicity
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField

/-! # Equivariant rationalization of a generic finite étale marking

Source: de Jong, Families of curves and alterations (1997), §§3.2 and 3.6,
printed pp.605,608 (blueprint: lem-sfb-equivariant-marking-rationalization).

The extension group is specified by an injective pair of homomorphisms whose image is
exactly the displayed fibre product. Thus the presentation includes nonfaithful actions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace EquivariantMarkingRationalization

/-- The reduced closed inclusion of a geometric fibre component.
Source: de Jong §3.6, p.608; Stacks Tag 0CDV.
(blueprint: lem-sfb-equivariant-marking-rationalization) -/
noncomputable def fibreComponentι {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
    (Z : irreducibleComponents (pullback (C := Scheme.{u}) f s)) :
    (pullback (C := Scheme.{u}) f s).reducedNormalizationComponent Z ⟶ pullback (C := Scheme.{u}) f
      s :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι

/-- The canonical field structure map on the normalization of a geometric fibre component.
Source: de Jong §3.6, p.608; Stacks Tag 0CDV.
(blueprint: lem-sfb-equivariant-marking-rationalization) -/
noncomputable def normalizedFibreComponentToSpec {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
    (Z : irreducibleComponents (pullback (C := Scheme.{u}) f s)) :
    ((pullback (C := Scheme.{u}) f s).reducedNormalizationComponent Z).normalization ⟶ Spec (.of Ω)
      :=
  ((pullback (C := Scheme.{u}) f s).reducedNormalizationComponent Z).fromNormalization ≫
    fibreComponentι f s Z ≫ pullback.snd f s

end EquivariantMarkingRationalization

open EquivariantMarkingRationalization

/-- A finite Galois constant extension makes the finite étale generic marking rational,
with its precise extension group, tensor action, normal models, kernel fixed fields,
and componentwise genus comparison. `B` is characterized as the original fixed subfield.
The injective pair `(β, σE)` has exactly the pairs in the stated fibre product as its image;
the kernel clause identifies it with all K-automorphisms of E. `L` presents F tensor_K E
by the specified pure-tensor formula. Every generic map is tied to its normalization map.

Source: de Jong §§3.2 and 3.6, pp.605,608.
(blueprint: lem-sfb-equivariant-marking-rationalization)

Proof (the node's seven steps):
1. The étale-fibre description (02GL) decomposes M into finitely many spectra of finite
   separable fields. Choose primitive elements and their separable minimal polynomials
   (finite-separable-extension-primitive-element). For empty M the list is empty.
2. Apply equivariant-galois-polynomial-envelope to these polynomials and the given action
   on K. It gives E finite Galois over B, all residue-field embeddings, and the exact
   fibre-product group, surjectivity, kernel identification and E^N = K.
3. Apply finite-normal-relative-curve-model in its constant-extension case. Geometric
   integrality makes F tensor_K E a field finite separable over F. The model theorem gives
   every normality, finite-type, projectivity, finite-surjectivity and pure-fibre clause,
   and identifies the generic fibre with the original curve after scalar extension.
4. On pure tensors the action is balanced because the two actions agree on K. Identity,
   composition and inverse follow on generators. The model theorem's functoriality lifts
   it to the normalizations. Tensor-field-extension-galois-invariants gives L^N = F.
5. Each residue field tensored with E is E[T]/(p), with p split and separable. Apply
   polynomial-quotient-distinct-linear-crt to obtain distinct rational points. Equivariance
   of the generic maps preserves the inverse marking. Empty coproducts stay empty.
6. Base change the finite map to the full fibre product. A reduced source component maps
   finitely onto its reduced image. Integral-injective-dimension-equal (00OK) and the
   dimension of nonempty opens show its image has dimension one; purity makes the image
   a target component. The component map is finite surjective and nonconstant.
7. Projective-base-change and projective-proper make these components proper curves.
   Normalization-properties makes their normalizations smooth proper curves over Ω.
   Normalization-dominant-lift supplies the induced nonconstant map. Algebraic closedness
   in the function field, generic-point-geometric-irreducibility and perfect-field
   geometric reducedness give geometric integrality. Finite-curve-genus-monotonicity,
   also for inseparable maps, proves the genus inequality and every inherited lower bound.
-/
theorem exists_equivariant_marking_rationalization
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hSnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    (hXnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback (C := Scheme.{u}) f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    [Algebra S.functionField X.functionField]
    (hKF : Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)) ≫
      S.fromSpecFunctionField = X.fromSpecFunctionField ≫ f)
    (M : Scheme.{u}) (i : M ⟶ pullback (C := Scheme.{u}) f S.fromSpecFunctionField)
    [IsClosedImmersion i] [IsReduced M]
    [IsFinite (i ≫ pullback.snd f S.fromSpecFunctionField)]
    [Etale (i ≫ pullback.snd f S.fromSpecFunctionField)]
    (G : Type v) [Group G] [Finite G]
    (σk : G →* (k ≃+* k)) (σX : G →* Aut X) (σS : G →* Aut S)
    (hk : ∀ g : G, (σS g).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (σk g⁻¹).toRingHom))
    (hequiv : ∀ g : G, (σX g).hom ≫ f = f ≫ (σS g).hom)
    (hMstable : ∀ g : G, (σX g).hom ''
      Set.range (i ≫ pullback.fst f S.fromSpecFunctionField) =
        Set.range (i ≫ pullback.fst f S.fromSpecFunctionField)) :
    ∃ B : Subfield S.functionField,
      (∀ a : S.functionField, a ∈ B ↔
        ∀ g : G, (Scheme.functionFieldAut (σS g)).hom a = a) ∧
      ∃ (E : Type u) (_ : Field E) (_ : Algebra S.functionField E)
        (_ : Algebra B E) (_ : IsScalarTower B S.functionField E),
        FiniteDimensional S.functionField E ∧
        FiniteDimensional B E ∧ IsGalois B E ∧
        (∀ m : M, ∃ j : M.residueField m →+* E,
          j.comp (Spec.homEquiv (M.fromSpecResidueField m ≫ i ≫
            pullback.snd f S.fromSpecFunctionField)).hom = algebraMap S.functionField E) ∧
        ∃ (G' : Type (max u v)) (_ : Group G') (_ : Finite G')
          (β : G' →* G) (σE : G' →* (E ≃+* E)),
          Function.Surjective β ∧
          Function.Injective (fun h : G' ↦ (β h, σE h)) ∧
          (∀ (g : G) (τ : E ≃+* E),
            ((∀ b : B, τ (algebraMap B E b) = algebraMap B E b) ∧
              ∀ a : S.functionField, τ (algebraMap S.functionField E a) =
                algebraMap S.functionField E
                  ((Scheme.functionFieldAut (σS g⁻¹)).hom a)) ↔
              ∃ h : G', β h = g ∧ σE h = τ) ∧
          (∀ τ : E ≃+* E,
            (∀ a : S.functionField, τ (algebraMap S.functionField E a) =
              algebraMap S.functionField E a) ↔ ∃ h : β.ker, σE h.val = τ) ∧
          (∀ z : E, z ∈ Set.range (algebraMap S.functionField E) ↔
            ∀ h : β.ker, σE h.val z = z) ∧
          IsField (TensorProduct S.functionField X.functionField E) ∧
          ∃ (L : Type u) (_ : Field L) (_ : Algebra X.functionField L)
            (_ : Algebra S.functionField L) (_ : Algebra E L)
            (_ : IsScalarTower S.functionField X.functionField L)
            (_ : IsScalarTower S.functionField E L)
            (eL : TensorProduct S.functionField X.functionField E ≃+* L),
            (∀ (a : X.functionField) (c : E),
              eL (TensorProduct.tmul S.functionField a c) =
                algebraMap X.functionField L a * algebraMap E L c) ∧
            FiniteDimensional X.functionField L ∧ Algebra.IsSeparable X.functionField L ∧
            (∀ s : S.normalizationIn E, IsDomain ((S.normalizationIn E).presheaf.stalk s) ∧
              IsIntegrallyClosed ((S.normalizationIn E).presheaf.stalk s)) ∧
            IsIntegral (S.normalizationIn E) ∧
            IsHProjective (S.fromNormalizationIn E ≫ p) ∧
            LocallyOfFiniteType (S.fromNormalizationIn E ≫ p) ∧
            QuasiCompact (S.fromNormalizationIn E ≫ p) ∧
            (∀ x : X.normalizationIn L, IsDomain ((X.normalizationIn L).presheaf.stalk x) ∧
              IsIntegrallyClosed ((X.normalizationIn L).presheaf.stalk x)) ∧
            IsIntegral (X.normalizationIn L) ∧
            LocallyOfFiniteType (X.fromNormalizationIn L ≫ f ≫ p) ∧
            QuasiCompact (X.fromNormalizationIn L ≫ f ≫ p) ∧
            IsFinite (S.fromNormalizationIn E) ∧ Surjective (S.fromNormalizationIn E) ∧
            ∃ (q : X.normalizationIn L ⟶ S.normalizationIn E)
              (r : X.normalizationIn L ⟶ pullback (C := Scheme.{u}) f (S.fromNormalizationIn E)),
              q ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f ∧
              (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ q =
                Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
                  (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
              r ≫ pullback.fst f (S.fromNormalizationIn E) = X.fromNormalizationIn L ∧
              r ≫ pullback.snd f (S.fromNormalizationIn E) = q ∧
              IsFinite r ∧ Surjective r ∧ IsHProjective q ∧
              (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
                (s : Spec (.of Ω) ⟶ S.normalizationIn E), (pullback (C := Scheme.{u}) q
                  s).IsPureDimension 1) ∧
              Smooth (pullback.snd q (S.fromSpecOfAlgebraFunctionField E).toNormalization) ∧
              GeometricallyIntegral
                (pullback.snd q (S.fromSpecOfAlgebraFunctionField E).toNormalization) ∧
              ∃ eC : pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField
                E).toNormalization ≅
                  pullback (C := Scheme.{u}) (pullback.snd f S.fromSpecFunctionField)
                    (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))),
                eC.hom ≫ pullback.snd (pullback.snd f S.fromSpecFunctionField)
                    (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))) =
                  pullback.snd q (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
                eC.hom ≫ pullback.fst (pullback.snd f S.fromSpecFunctionField)
                    (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))) ≫
                      pullback.fst f S.fromSpecFunctionField =
                  pullback.fst q (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫
                    X.fromNormalizationIn L ∧
                ∃ (σL : G' →* (L ≃+* L))
                  (τS : G' →* Aut (S.normalizationIn E))
                  (τX : G' →* Aut (X.normalizationIn L)),
                  (∀ (h : G') (z : X.functionField) (c : E),
                    σL h (eL (TensorProduct.tmul S.functionField z c)) =
                      eL (TensorProduct.tmul S.functionField
                        ((Scheme.functionFieldAut (σX (β h)⁻¹)).hom z) (σE h c))) ∧
                  (∀ h : G', (τS h).hom ≫ S.fromNormalizationIn E =
                    S.fromNormalizationIn E ≫ (σS (β h)).hom) ∧
                  (∀ h : G', (τX h).hom ≫ X.fromNormalizationIn L =
                    X.fromNormalizationIn L ≫ (σX (β h)).hom) ∧
                  (∀ h : G', (τX h).hom ≫ q = q ≫ (τS h).hom) ∧
                  (∀ h : G', Spec.map (CommRingCat.ofHom (σE h⁻¹).toRingHom) ≫
                      (S.fromSpecOfAlgebraFunctionField E).toNormalization =
                    (S.fromSpecOfAlgebraFunctionField E).toNormalization ≫ (τS h).hom) ∧
                  (∀ h : G', Spec.map (CommRingCat.ofHom (σL h⁻¹).toRingHom) ≫
                      (X.fromSpecOfAlgebraFunctionField L).toNormalization =
                    (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ (τX h).hom) ∧
                  (∀ z : L, z ∈ Set.range (algebraMap X.functionField L) ↔
                    ∀ h : β.ker, σL h.val z = z) ∧
                  (∃ (n : ℕ) (a : Fin n →
                      (Spec (.of E) ⟶
                        pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField
                          E).toNormalization)),
                    (∀ j : Fin n, a j ≫
                      pullback.snd q (S.fromSpecOfAlgebraFunctionField E).toNormalization = 𝟙 _) ∧
                    (Pairwise fun j l : Fin n ↦ Disjoint (Set.range (a j)) (Set.range (a l))) ∧
                    (∀ z : pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField
                      E).toNormalization,
                      eC.hom z ∈ Set.range
                        (pullback.snd i (pullback.fst (pullback.snd f S.fromSpecFunctionField)
                          (Spec.map (CommRingCat.ofHom (algebraMap S.functionField E))))) ↔
                        ∃ j : Fin n, z ∈ Set.range (a j)) ∧
                    (∀ h : G', (τX h).hom ''
                        (⋃ j : Fin n, Set.range (a j ≫
                          pullback.fst q (S.fromSpecOfAlgebraFunctionField E).toNormalization)) =
                      ⋃ j : Fin n, Set.range (a j ≫
                        pullback.fst q (S.fromSpecOfAlgebraFunctionField E).toNormalization))) ∧
                  (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
                      (s : Spec (.of Ω) ⟶ S.normalizationIn E),
                    ∃ hF : pullback (C := Scheme.{u}) q s ⟶ pullback (C := Scheme.{u}) f (s ≫
                      S.fromNormalizationIn E),
                      hF ≫ pullback.fst f (s ≫ S.fromNormalizationIn E) =
                        pullback.fst q s ≫ X.fromNormalizationIn L ∧
                      hF ≫ pullback.snd f (s ≫ S.fromNormalizationIn E) = pullback.snd q s ∧
                      ∀ Z' : irreducibleComponents (pullback (C := Scheme.{u}) q s),
                        ∃ (Z : irreducibleComponents (pullback (C := Scheme.{u}) f (s ≫
                          S.fromNormalizationIn E)))
                          (h : (pullback (C := Scheme.{u}) q s).reducedNormalizationComponent Z' ⟶
                            (pullback (C := Scheme.{u}) f (s ≫ S.fromNormalizationIn
                              E)).reducedNormalizationComponent Z)
                          (hν : ((pullback (C := Scheme.{u}) q s).reducedNormalizationComponent
                            Z').normalization ⟶
                            ((pullback (C := Scheme.{u}) f (s ≫ S.fromNormalizationIn
                              E)).reducedNormalizationComponent
                              Z).normalization),
                          IsFinite h ∧ Surjective h ∧
                          Smooth (normalizedFibreComponentToSpec q s Z') ∧
                          IsProper (normalizedFibreComponentToSpec q s Z') ∧
                          Smooth (normalizedFibreComponentToSpec f (s ≫ S.fromNormalizationIn E) Z)
                            ∧
                          IsProper (normalizedFibreComponentToSpec f (s ≫ S.fromNormalizationIn E)
                            Z) ∧
                          hν ≫ normalizedFibreComponentToSpec f (s ≫ S.fromNormalizationIn E) Z =
                            normalizedFibreComponentToSpec q s Z' ∧
                          h ≫ fibreComponentι f (s ≫ S.fromNormalizationIn E) Z =
                            fibreComponentι q s Z' ≫ hF ∧
                          hν ≫ ((pullback (C := Scheme.{u}) f (s ≫ S.fromNormalizationIn
                            E)).reducedNormalizationComponent
                              Z).fromNormalization =
                            ((pullback (C := Scheme.{u}) q s).reducedNormalizationComponent
                              Z').fromNormalization ≫ h ∧
                          (¬ ∃ z : Spec (.of Ω) ⟶
                              ((pullback (C := Scheme.{u}) f (s ≫ S.fromNormalizationIn
                                E)).reducedNormalizationComponent
                                Z).normalization,
                            z ≫ normalizedFibreComponentToSpec f (s ≫ S.fromNormalizationIn E) Z =
                                𝟙 _ ∧
                              normalizedFibreComponentToSpec q s Z' ≫ z = hν) ∧
                          @Scheme.arithmeticGenus Ω _
                              ((pullback (C := Scheme.{u}) f (s ≫ S.fromNormalizationIn
                                E)).reducedNormalizationComponent
                                Z).normalization
                              ⟨normalizedFibreComponentToSpec f (s ≫ S.fromNormalizationIn E) Z⟩ ≤
                            @Scheme.arithmeticGenus Ω _
                              ((pullback (C := Scheme.{u}) q s).reducedNormalizationComponent
                                Z').normalization
                              ⟨normalizedFibreComponentToSpec q s Z'⟩) ∧
                  ∀ b : ℕ,
                    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
                        (Z : irreducibleComponents (pullback (C := Scheme.{u}) f s)),
                      b ≤ @Scheme.arithmeticGenus Ω _
                        ((pullback (C := Scheme.{u}) f s).reducedNormalizationComponent
                          Z).normalization
                        ⟨normalizedFibreComponentToSpec f s Z⟩) →
                    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
                        (s : Spec (.of Ω) ⟶ S.normalizationIn E)
                        (Z : irreducibleComponents (pullback (C := Scheme.{u}) q s)),
                      b ≤ @Scheme.arithmeticGenus Ω _
                        ((pullback (C := Scheme.{u}) q s).reducedNormalizationComponent
                          Z).normalization
                        ⟨normalizedFibreComponentToSpec q s Z⟩ := by
  sorry

end AlgebraicGeometry
