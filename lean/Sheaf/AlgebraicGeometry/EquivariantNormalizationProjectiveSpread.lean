/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import Sheaf.AlgebraicGeometry.SemilinearEquivariantChowModification
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover

/-! # Equivariant projective spreading of a generic normalization

Source: Stacks Project, coherent.tex, Tag 0200 (lemma-chow-Noetherian), algebra.tex,
Tags 0307 and 00GN; de Jong (1997), Sections 2.9--2.10, printed pp. 604--605.
(blueprint: lem-sfb-equivariant-normalization-projective-spread).

The generic normalization and its two structural maps are actual constructions.
The theorem retains the specified generic maps and the scheme structure of the marking.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace NormalizationProjectiveSpread

/-- The normalization of the reduced generic base change to the specified field `K₀`.
Source: de Jong (1997), Sections 2.9--2.10; Stacks Tags 0307 and 0CDV
(blueprint: lem-sfb-equivariant-normalization-projective-spread). -/
noncomputable def genericNormalization {Y C : Scheme.{u}} [IsIntegral Y]
    (g : C ⟶ Y) (K₀ : Type u) [Field K₀] [Algebra Y.functionField K₀] : Scheme.{u} :=
  (pullback g (Y.fromSpecOfAlgebraFunctionField K₀)).reducedNormalization

/-- The structural map from the generic normalization to the original curve family.
Source: Stacks Tags 0307 and 0CDV; de Jong (1997), Section 2.9
(blueprint: lem-sfb-equivariant-normalization-projective-spread). -/
noncomputable def toCurve {Y C : Scheme.{u}} [IsIntegral Y]
    (g : C ⟶ Y) (K₀ : Type u) [Field K₀] [Algebra Y.functionField K₀] :
    genericNormalization g K₀ ⟶ C :=
  Scheme.fromReducedNormalization _ ≫ pullback.fst g (Y.fromSpecOfAlgebraFunctionField K₀)

/-- The structural map from the generic normalization to its specified ground field.
Source: Stacks Tags 0307 and 0CDV; de Jong (1997), Section 2.9
(blueprint: lem-sfb-equivariant-normalization-projective-spread). -/
noncomputable def toField {Y C : Scheme.{u}} [IsIntegral Y]
    (g : C ⟶ Y) (K₀ : Type u) [Field K₀] [Algebra Y.functionField K₀] :
    genericNormalization g K₀ ⟶ Spec (.of K₀) :=
  Scheme.fromReducedNormalization _ ≫ pullback.snd g (Y.fromSpecOfAlgebraFunctionField K₀)

end NormalizationProjectiveSpread

open NormalizationProjectiveSpread

/-- Spread the smooth marked generic normalization to an equivariant projective model.
The isomorphism `eF` specifies `F₀ = k(C) ⊗[k(Y)] K₀` on pure tensors, including both
field embeddings. `hK` specifies the inclusion of function fields induced by `g`.
The spectrum equations for the field actions specify their restrictions to the original
schemes; together with `hσF₀` they specify the tensor action. The two equations for `σN`
specify the induced action on the normalization. Field actions are left actions; their
inverses induce left actions on spectra. No action is required to be faithful or to fix `k`.

The morphism `f₀` is characterized by its square and its specified generic map. Its
Cartesian square with `j₀` identifies its generic fibre with the constructed normalization
over both `C` and `K₀`. The corresponding square with `jT`, and `jT ≫ q = j₀`, say that
the actual generic fibre of `q` is this isomorphism. The last Cartesian square identifies
the generic marking as a closed subscheme, and the affine kernel equality specifies its
schematic closure, including when the marking is empty.

Source: Stacks Project, Tag 0200 (lemma-chow-Noetherian), Tags 0307 and 00GN;
de Jong (1997), Sections 2.9--2.10, printed pp. 604--605.
(blueprint: lem-sfb-equivariant-normalization-projective-spread).

Proof (the node's eleven steps):
1. The tensors of a finite K-basis of K₀ span F₀ over F and 1 extends to a basis,
   so F embeds in F₀ and F₀/F is finite. Apply
   lem-sfb-finite-normalization-model-functoriality to Y,K₀ and C,F₀. Integral closures
   give the specified normal integral finite models and semilinear actions; the tensor
   action is h(x tensor a) = h(x) tensor h(a), compatible with the tensor relations.
2. Apply lem-fin-finite-over-projective over the affine Noetherian field spectrum to S₀.
   Projectivity gives properness and separatedness (lem-pc-projective-proper).
   Proper and finite composition give properness of C and C₀, by
   lem-weil-pbc-proper-fp-permanence and lem-weil-pbc-finite-morphism-permanence.
3. On Spec B over Spec A the integral closure of A in K₀ maps into that of B in F₀:
   keep the same monic equation. Integral-closure-commutes-localization glues these maps
   to f₀. The inclusions specify its square, generic map and equivariance. The
   proper-to-separated lemma gives properness of f₀.
4. Invert A minus zero. The resulting finite-dimensional domain from its integral
   closure is K₀ (lem-weil-pbc-finite-dimensional-domain-is-field). Thus the generic
   coordinate ring of C₀ is the integral closure of B_K in F₀. Tensoring the inclusion
   B_K into F remains injective by extending a vector-space basis; B_K tensor K₀ is
   a domain with fraction field F₀.
5. B_K tensor K₀ is finite, hence integral, over B_K
   (lem-weil-pbc-finite-algebra-is-integral). Transitivity of integrality
   (lem-weil-pbc-integral-transitive) identifies their integral closures in F₀.
   Localization compatibility glues these equalities into the canonical generic
   identification with N, fixing B and K₀ and respecting all actions. Reduction changes
   nothing since the base-change affine rings are domains.
6. By lem-pc-dim-base-change the generic base change is one-dimensional. Apply
   lem-sc-normalization-exists over K₀: N is a proper integral normal curve with
   function field F₀; properness is preserved by base change. Smoothness and geometric
   integrality are the hypotheses here.
7. Apply lem-sfb-semilinear-equivariant-chow-modification to C₀ to obtain integral T,
   its semilinear action, and proper birational equivariant q, with T/k and q
   H-projective. The closed graph lemma lem-sfb-finite-constant-projective-graph with
   the identity constant extension and separated target S₀ makes T to S₀ H-projective.
8. The generic fibre of T is integral by
   lem-weil-pbc-generic-fibre-localization-domain-irreducible and has function field F₀
   by lem-sc-integral-function-field-affine-fraction. Its proper dominant map to N
   induces the identity of F₀. The dimension/trdeg lemma
   lem-sc-closed-irreducible-dimension-trdeg makes both curves one-dimensional.
   Apply lem-trf-proper-birational-normal-curve-iso. The induced isomorphism retains
   the structural maps to C and K₀ and equivariance.
9. Finite type over k gives Noetherianity (lem-weil-pbc-finite-type-over-noetherian).
   Fields are excellent (lem-exc-fields-excellent), finite-type coordinate rings are
   excellent (lem-exc-finite-type-localization-excellent), and
   lem-trf-excellent-scheme-affine-cover gives excellence on every affine open.
10. The finite marking is quasi-compact, and T is separated, so the composite D to T
    is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence. Its scheme image is
    defined by the affine restriction kernels (lem-weil-pbc-scheme-image-qc-kernel).
    The actions preserve these kernels and descend to the closure L with their group law.
11. On a generic affine chart, contract the marking ideal J in S inverse R to I in R.
    If r/s is in J then r/1 is in J, hence r is in I; conversely I maps into J.
    Thus S inverse I = J, identifying L's generic fibre with D with its full scheme
    structure and both structural maps. If D is empty then J is the unit ideal,
    I is the unit ideal and L is empty. -/
theorem exists_equivariant_normalization_projective_spread
    (k : Type u) [Field k] (Y C : Scheme.{u}) [IsIntegral Y] [IsIntegral C]
    (pY : Y ⟶ Spec (.of k)) [IsHProjective pY]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    (g : C ⟶ Y) [IsProper g] [IsDominant g]
    [LocallyOfFiniteType (g ≫ pY)] [QuasiCompact (g ≫ pY)]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    [GeometricallyIntegral (pullback.snd g Y.fromSpecFunctionField)]
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) g Y.fromSpecFunctionField) = 1)
    [Algebra Y.functionField C.functionField]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap Y.functionField C.functionField)) ≫
      Y.fromSpecFunctionField = C.fromSpecFunctionField ≫ g)
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σY : H →* Aut Y) (σC : H →* Aut C)
    (hY : ∀ h : H, (σY h).hom ≫ pY =
      pY ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hC : ∀ h : H, (σC h).hom ≫ g ≫ pY =
      (g ≫ pY) ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hg : ∀ h : H, (σC h).hom ≫ g = g ≫ (σY h).hom)
    (K₀ : Type u) [Field K₀] [Algebra Y.functionField K₀]
    [Module.Finite Y.functionField K₀] [IsPurelyInseparable Y.functionField K₀]
    (σK₀ : H →* (K₀ ≃+* K₀))
    (hK₀ : ∀ h : H, Spec.map (CommRingCat.ofHom (σK₀ h⁻¹).toRingHom) ≫
      Y.fromSpecOfAlgebraFunctionField K₀ =
        Y.fromSpecOfAlgebraFunctionField K₀ ≫ (σY h).hom)
    (F₀ : Type u) [Field F₀] [Algebra C.functionField F₀] [Algebra K₀ F₀]
    (eF : TensorProduct Y.functionField C.functionField K₀ ≃+* F₀)
    (heF : ∀ (x : C.functionField) (a : K₀),
      eF (TensorProduct.tmul Y.functionField x a) =
        algebraMap C.functionField F₀ x * algebraMap K₀ F₀ a)
    (σF₀ : H →* (F₀ ≃+* F₀))
    (hF₀ : ∀ h : H, Spec.map (CommRingCat.ofHom (σF₀ h⁻¹).toRingHom) ≫
      C.fromSpecOfAlgebraFunctionField F₀ =
        C.fromSpecOfAlgebraFunctionField F₀ ≫ (σC h).hom)
    (hσF₀ : ∀ (h : H) (a : K₀),
      σF₀ h (algebraMap K₀ F₀ a) = algebraMap K₀ F₀ (σK₀ h a))
    [Smooth (toField g K₀)] [GeometricallyIntegral (toField g K₀)]
    (σN : H →* Aut (genericNormalization g K₀))
    (hNC : ∀ h : H, (σN h).hom ≫ toCurve g K₀ = toCurve g K₀ ≫ (σC h).hom)
    (hNK : ∀ h : H, (σN h).hom ≫ toField g K₀ =
      toField g K₀ ≫ Spec.map (CommRingCat.ofHom (σK₀ h⁻¹).toRingHom))
    (D : Scheme.{u}) (d : D ⟶ genericNormalization g K₀) [IsClosedImmersion d]
    [IsFinite (d ≫ toField g K₀)] [Etale (d ≫ toField g K₀)]
    (σD : H →* Aut D)
    (hD : ∀ h : H, (σD h).hom ≫ d = d ≫ (σN h).hom) :
    (∀ s : Y.normalizationIn K₀,
      IsDomain ((Y.normalizationIn K₀).presheaf.stalk s) ∧
        IsIntegrallyClosed ((Y.normalizationIn K₀).presheaf.stalk s)) ∧
    IsIntegral (Y.normalizationIn K₀) ∧ IsNoetherian (Y.normalizationIn K₀) ∧
    (∀ U : (Y.normalizationIn K₀).affineOpens, IsExcellent Γ(Y.normalizationIn K₀, U)) ∧
    LocallyOfFiniteType (Y.fromNormalizationIn K₀ ≫ pY) ∧
    QuasiCompact (Y.fromNormalizationIn K₀ ≫ pY) ∧
    IsFinite (Y.fromNormalizationIn K₀) ∧ IsDominant (Y.fromNormalizationIn K₀) ∧
    IsHProjective (Y.fromNormalizationIn K₀ ≫ pY) ∧
    (∃ e : Spec (.of K₀) ≅ Spec (Y.normalizationIn K₀).functionField,
      e.hom ≫ (Y.normalizationIn K₀).fromSpecFunctionField =
        (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization) ∧
    (∀ c : C.normalizationIn F₀,
      IsDomain ((C.normalizationIn F₀).presheaf.stalk c) ∧
        IsIntegrallyClosed ((C.normalizationIn F₀).presheaf.stalk c)) ∧
    IsIntegral (C.normalizationIn F₀) ∧ IsNoetherian (C.normalizationIn F₀) ∧
    (∀ U : (C.normalizationIn F₀).affineOpens, IsExcellent Γ(C.normalizationIn F₀, U)) ∧
    LocallyOfFiniteType (C.fromNormalizationIn F₀ ≫ g ≫ pY) ∧
    QuasiCompact (C.fromNormalizationIn F₀ ≫ g ≫ pY) ∧
    IsFinite (C.fromNormalizationIn F₀) ∧ IsDominant (C.fromNormalizationIn F₀) ∧
    (∃ e : Spec (.of F₀) ≅ Spec (C.normalizationIn F₀).functionField,
      e.hom ≫ (C.normalizationIn F₀).fromSpecFunctionField =
        (C.fromSpecOfAlgebraFunctionField F₀).toNormalization) ∧
    ∃ (f₀ : C.normalizationIn F₀ ⟶ Y.normalizationIn K₀)
      (σS₀ : H →* Aut (Y.normalizationIn K₀))
      (σC₀ : H →* Aut (C.normalizationIn F₀)),
      IsProper f₀ ∧
      f₀ ≫ Y.fromNormalizationIn K₀ = C.fromNormalizationIn F₀ ≫ g ∧
      (C.fromSpecOfAlgebraFunctionField F₀).toNormalization ≫ f₀ =
        Spec.map (CommRingCat.ofHom (algebraMap K₀ F₀)) ≫
          (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization ∧
      (∀ h : H, (σS₀ h).hom ≫ Y.fromNormalizationIn K₀ =
        Y.fromNormalizationIn K₀ ≫ (σY h).hom) ∧
      (∀ h : H, (σC₀ h).hom ≫ C.fromNormalizationIn F₀ =
        C.fromNormalizationIn F₀ ≫ (σC h).hom) ∧
      (∀ h : H, Spec.map (CommRingCat.ofHom (σK₀ h⁻¹).toRingHom) ≫
        (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization =
          (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization ≫ (σS₀ h).hom) ∧
      (∀ h : H, Spec.map (CommRingCat.ofHom (σF₀ h⁻¹).toRingHom) ≫
        (C.fromSpecOfAlgebraFunctionField F₀).toNormalization =
          (C.fromSpecOfAlgebraFunctionField F₀).toNormalization ≫ (σC₀ h).hom) ∧
      (∀ h : H, (σC₀ h).hom ≫ f₀ = f₀ ≫ (σS₀ h).hom) ∧
      ∃ j₀ : genericNormalization g K₀ ⟶ C.normalizationIn F₀,
        IsPullback j₀ (toField g K₀) f₀
          (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization ∧
        j₀ ≫ C.fromNormalizationIn F₀ = toCurve g K₀ ∧
        (∀ h : H, (σN h).hom ≫ j₀ = j₀ ≫ (σC₀ h).hom) ∧
        ∃ (T : Scheme.{u}) (_ : IsIntegral T) (q : T ⟶ C.normalizationIn F₀)
          (σT : H →* Aut T) (jT : genericNormalization g K₀ ⟶ T),
          IsNoetherian T ∧ (∀ U : T.affineOpens, IsExcellent Γ(T, U)) ∧
          LocallyOfFiniteType (q ≫ C.fromNormalizationIn F₀ ≫ g ≫ pY) ∧
          QuasiCompact (q ≫ C.fromNormalizationIn F₀ ≫ g ≫ pY) ∧
          IsProper q ∧
          (∃ U : (C.normalizationIn F₀).Opens,
            Dense (U : Set (C.normalizationIn F₀)) ∧ IsIso (q ∣_ U) ∧
              Dense ((q ⁻¹ᵁ U) : Set T)) ∧
          IsHProjective (q ≫ C.fromNormalizationIn F₀ ≫ g ≫ pY) ∧
          IsHProjective q ∧ IsHProjective (q ≫ f₀) ∧
          (∀ h : H, (σT h).hom ≫ q = q ≫ (σC₀ h).hom) ∧
          IsPullback jT (toField g K₀) (q ≫ f₀)
            (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization ∧
          jT ≫ q = j₀ ∧
          (∀ h : H, (σN h).hom ≫ jT = jT ≫ (σT h).hom) ∧
          ∃ (L : Scheme.{u}) (iL : L ⟶ T) (dL : D ⟶ L) (σL : H →* Aut L),
            IsClosedImmersion iL ∧
            (∀ U : T.affineOpens,
              RingHom.ker (iL.app U).hom = RingHom.ker ((d ≫ jT).app U).hom) ∧
            (∀ h : H, (σL h).hom ≫ iL = iL ≫ (σT h).hom) ∧
            (∀ h : H, (σD h).hom ≫ dL = dL ≫ (σL h).hom) ∧
            dL ≫ iL = d ≫ jT ∧
            IsPullback dL (d ≫ toField g K₀) (iL ≫ q ≫ f₀)
              (Y.fromSpecOfAlgebraFunctionField K₀).toNormalization := by
  sorry

end AlgebraicGeometry
