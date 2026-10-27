/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.ReducedNormalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Invariant normalization of a marked generic curve

Source: Stacks Project, Varieties, Tags 0BXT, 04KT and 0C3N; de Jong,
Families of curves and alterations (1997), §2.7 and Lemma 2.8, pp.603–604.
(blueprint: lem-sfb-invariant-marked-generic-normalization).

The result is packaged as data whose maps are pinned to the existing componentwise
normalization. Actions on a field are encoded by actions on its affine spectrum;
contravariance identifies these with actions on the field (using inverse group elements).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

namespace InvariantMarkedGenericNormalization

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]

/-- The actual scalar tensor product of the generic field, using the scalar map induced
by `Spec k(X) → X → Spec K`. Source: Stacks 0BXT and the generic calculation in 01RW
(blueprint: lem-sfb-invariant-marked-generic-normalization). -/
noncomputable def genericTensor (f : X ⟶ Spec (.of K))
    (K₀ : Type u) [Field K₀] [Algebra K K₀] : CommRingCat.{u} := by
  letI : Algebra K X.functionField :=
    (Spec.preimage (X.fromSpecFunctionField ≫ f)).hom.toAlgebra
  exact .of (X.functionField ⊗[K] K₀)

/-- The first canonical tensor embedding. Source: Stacks 01RW, generic base change
(blueprint: lem-sfb-invariant-marked-generic-normalization). -/
noncomputable def genericTensorLeft (f : X ⟶ Spec (.of K))
    (K₀ : Type u) [Field K₀] [Algebra K K₀] : X.functionField →+* genericTensor f K₀ := by
  letI : Algebra K X.functionField :=
    (Spec.preimage (X.fromSpecFunctionField ≫ f)).hom.toAlgebra
  exact (Algebra.TensorProduct.includeLeft :
    X.functionField →ₐ[K] X.functionField ⊗[K] K₀).toRingHom

/-- The second canonical tensor embedding. Source: Stacks 01RW, generic base change
(blueprint: lem-sfb-invariant-marked-generic-normalization). -/
noncomputable def genericTensorRight (f : X ⟶ Spec (.of K))
    (K₀ : Type u) [Field K₀] [Algebra K K₀] : K₀ →+* genericTensor f K₀ := by
  letI : Algebra K X.functionField :=
    (Spec.preimage (X.fromSpecFunctionField ≫ f)).hom.toAlgebra
  exact (Algebra.TensorProduct.includeRight :
    K₀ →ₐ[K] X.functionField ⊗[K] K₀).toRingHom

/-- All clauses of the invariant marked normalization, including the canonical generic
embeddings and arbitrary further scalar extension. The reduced closed immersion `i`
is determined by its displayed support; this includes the empty marking.
Source: Stacks 0BXT, 04KT, 0C3N; de Jong (1997), §2.7 and Lemma 2.8, pp.603–604
(blueprint: lem-sfb-invariant-marked-generic-normalization). -/
structure Data (f : X ⟶ Spec (.of K)) (Z : TopologicalSpace.Closeds X)
    (H : Type v) [Group H] (aK : H →* Aut (Spec (.of K))) (aX : H →* Aut X)
    (K₀ : Type u) [Field K₀] [Algebra K K₀] where
  finiteConstants : Module.Finite K K₀
  inseparableConstants : IsPurelyInseparable K K₀
  constantsAction : H →* Aut (Spec (.of K₀))
  constants_equivariant : ∀ h : H,
    (constantsAction h).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K K₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap K K₀)) ≫ (aK h).hom
  N : Scheme.{u}
  [integral : IsIntegral N]
  ν : N ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))
  normalizationIso : N ≅
    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))).reducedNormalization
  normalization_map : normalizationIso.hom ≫
    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))).fromReducedNormalization = ν
  smooth : Smooth (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
  proper : IsProper (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
  geometricallyIntegral :
    GeometricallyIntegral (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
  dimension : topologicalKrullDim N = 1
  D : Scheme.{u}
  i : D ⟶ N
  closedMarking : IsClosedImmersion i
  reducedMarking : IsReduced D
  marking_support : Set.range i =
    (ν ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))) ⁻¹' (Z : Set X)
  finiteMarking :
    IsFinite (i ≫ ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
  etaleMarking : Etale (i ≫ ν ≫
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
  curveAction : H →* Aut N
  original_equivariant : ∀ h : H,
    (curveAction h).hom ≫ ν ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))) =
    ν ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))) ≫ (aX h).hom
  field_equivariant : ∀ h : H,
    (curveAction h).hom ≫ ν ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))) =
    ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))) ≫
      (constantsAction h).hom
  marking_invariant : ∀ (h : H) (x : N),
    (curveAction h).hom x ∈ Set.range i ↔ x ∈ Set.range i
  tensorIsField : IsField (genericTensor f K₀)
  genericComparison : genericTensor f K₀ ≃+* N.functionField
  generic_original :
    Spec.map (CommRingCat.ofHom
      (genericComparison.toRingHom.comp (genericTensorLeft f K₀))) ≫ X.fromSpecFunctionField =
    N.fromSpecFunctionField ≫ ν ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))
  generic_constants :
    Spec.map (CommRingCat.ofHom
      (genericComparison.toRingHom.comp (genericTensorRight f K₀))) =
    N.fromSpecFunctionField ≫ ν ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))
  further_extension : ∀ (K' : Type u) [Field K'] [Algebra K₀ K']
      [Algebra K K'] [IsScalarTower K K₀ K'],
    ∃ e : pullback
        (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
        (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))) ≅
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K')))).reducedNormalization,
      (e.hom ≫
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K')))).fromReducedNormalization ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K'))) =
      pullback.fst
        (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
        (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))) ≫ ν ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K₀)))) ∧
      (e.hom ≫
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K')))).fromReducedNormalization ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K'))) =
      pullback.snd
        (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
        (Spec.map (CommRingCat.ofHom (algebraMap K₀ K')))) ∧
      ∃ j : pullback
          (i ≫ ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
          (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))) ⟶
          pullback
            (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
            (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))),
        (j ≫ pullback.fst
          (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
          (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))) =
        pullback.fst
          (i ≫ ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
          (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))) ≫ i) ∧
        (j ≫ pullback.snd
          (ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
          (Spec.map (CommRingCat.ofHom (algebraMap K₀ K'))) =
        pullback.snd
          (i ≫ ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
          (Spec.map (CommRingCat.ofHom (algebraMap K₀ K')))) ∧
        IsClosedImmersion j ∧
        IsReduced (pullback
          (i ≫ ν ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K₀))))
          (Spec.map (CommRingCat.ofHom (algebraMap K₀ K')))) ∧
        Set.range (j ≫ e.hom) =
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K')))).fromReducedNormalization ≫
            pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹' (Z : Set X)

end InvariantMarkedGenericNormalization

/-- Invariant inseparable normalization of a marked generic curve.
Source: Stacks Project, Varieties, Tags 0BXT, 04KT and 0C3N; de Jong (1997),
§2.7 and Lemma 2.8, pp.603–604
(blueprint: lem-sfb-invariant-marked-generic-normalization).

Proof in natural language (the agent-written assembly recorded by the DAG):

1. Apply the geometric-normalization preparation to $X$ and obtain a finite purely inseparable
$E/K$ whose normalized curve $N_E$ is geometrically normal. The scheme $X_E$ is already integral
by geometric integrality, so its reduction does nothing and the componentwise normalization is its
ordinary function-field normalization. Properness of $X_E$ follows by proper base change. The
finite normalization theorem gives that $N_E$ is proper, finite type and one-dimensional
(dimension of $X_E$ equals that of $X$ by the field-extension dimension theorem, applied on affine
opens). The geometrically normal dimension-one criterion makes $N_E$ smooth.
Uses: lem-weil-pbc-normalization-geonormal-insep, def-pc-geometrically-irreducible, lem-weil-pbc-
proper-fp-permanence, lem-sc-normalization-exists, lem-weil-pbc-dimension-preserved-field-
extension, lem-weil-pbc-geonormal-dim-one-smooth.

2. Put $D_E=(\nu_E^{-1}Z)_{\mathrm{red}}$. The finite birational map $\nu_E$ sends the generic
point to the generic point of $X_E$, which does not lie over the proper closed subset $Z$ of the
integral curve $X$. The purely inseparable projection $X_E      o X$ is a homeomorphism. Thus
$D_E$ is nowhere dense and closed. The dimension-zero and closed-subscheme finiteness lemmas imply
$D_E$ is finite over $E$. Apply geometric-reduction preparation to $D_E$ to obtain a finite purely
inseparable $L/E$ such that $(D_E\times_E L)_{\mathrm{red}}$ is geometrically reduced. The finite-
type dimension-zero theorem makes its points a finite set, so it has finitely many irreducible
components as required by geometric-reduction preparation. This also applies to $D_E=\varnothing$.
Uses: lem-sc-normalization-exists, lem-pc-nowhere-dense-dim-zero, lem-pc-zero-dimensional-closed-
subscheme-finite, lem-pur-finite-inseparable-geometric-reduction, lem-pc-homeo-pure-insep, lem-
weil-pbc-finite-type-dim-zero-artinian.

3. Choose a perfect purely inseparable overfield $P/K$. Embed the finite purely inseparable
extension $L/K$ into $P$: in characteristic $p$ each generator has $p^n$th power in $K$, whose
unique $p^n$th root exists in $P$; these uniquely specified roots respect all equations, so give
the embedding. Extend each $h\in H$ uniquely to $P$ by sending the root of $a\in K$ to the
corresponding root of $h(a)$. Roots are unique, so these maps preserve addition and
multiplication, have inverse indexed by $h^{-1}$, and satisfy the group law. Let $K_0$ be the
compositum inside $P$ of the finitely many fields $h(L)$. It contains $L$, is $H$-stable, and is
finite purely inseparable over $K$: take finite generators for each $h(L)$, and multiply their
finite degrees; a common $p$-power sends every generator, and hence every element of their
compositum, into $K$. In characteristic zero every extension just used is equality; take
$P=L=E=K_0=K$.
Uses: lem-weil-pbc-perfect-purely-inseparable-overfield.

4. For every extension $T/E$, apply the integral-closure scalar-extension lemma on each nonempty
affine open $\operatorname{Spec}A$ of $X_E$. Its inverse image in $N_E$ is $\operatorname{Spec}B$,
with $B$ the finite integral closure of $A$; geometric normality supplies the local normality
hypothesis after every extension. Thus $\operatorname{Spec}(B\otimes_E T)$ is the normalization
over $\operatorname{Spec}(A\otimes_E T)$. The canonical identifications commute on principal
opens, hence glue to an identification of the normalization of $X_T$ with $N_E\times_E T$. Its
affine charts are domains. The inverse images of any two nonempty affine opens intersect: choose a
nonempty principal open in their intersection in $X_E$; it remains nonempty after field extension,
and normalization is surjective. Hence this normalization is integral. This proves geometric
integrality of $N_E$ and identifies $N=N_E\times_E K_0$. Properness and dimension one follow from
proper base change and the field-extension dimension theorem; geometric normality is preserved
simply by quantifying over extensions $T/K_0$, so the dimension-one criterion gives smoothness of
$N$.
Uses: lem-sfb-integral-closure-geonormal-scalar-extension, def-sc-normalization, lem-sc-
normalization-exists, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-dimension-preserved-field-
extension, lem-weil-pbc-geonormal-dim-one-smooth.

5. The reduced inverse image $D$ of $Z$ on $N=N_E\times_E K_0$ is
$((D_E)_L)_{\mathrm{red}}\times_L K_0$. To check the reductions, on an affine chart let $I$ define
the inverse image before reduction and $J=\sqrt I$. The finite-normalization-model theorem gives
that $N_E$ is Noetherian; its closed subschemes are Noetherian, so applying the nilradical theorem
to the chart quotient shows that $J/I$ is nilpotent. This remains nilpotent after scalar
extension, so replacing $I$ by $J$ does not change the reduced inverse image. The same observation
over $L$, together with geometric reducedness of $((D_E)_L)_{\mathrm{red}}$, shows that its base
change to $K_0$ is already reduced. Finiteness survives base change, and the displayed scheme is
geometrically reduced by definition. The finite-geometrically-reduced criterion therefore makes
$D$ finite etale.
Uses: lem-sc-reduction-nilradical-nilpotent, lem-trf-finite-radicial-basechange, def-pc-
geometrically-irreducible, lem-sfb-finite-georeduced-etale, lem-sfb-finite-normalization-model-
functoriality.

6. The actions on $X$ and $K_0$ give a compatible semilinear action on $X_{K_0}$ by the fibre-
product universal property. Apply normalization functoriality with $V=X_{K_0}$ and $M=k(V)$
(degree one). It lifts each automorphism uniquely to $N$, and the identities and compositions are
preserved, hence give an $H$-action. The inverse image of the invariant closed set $Z$ is
invariant; its reduced structure is invariant as well since ring automorphisms preserve nilpotent
elements. Consequently this lifted action preserves $D$ and commutes with the two structural maps.
Uses: def-pc-fibre-product, lem-sfb-finite-normalization-model-functoriality.

7. For the generic-field assertion apply the flat-curve pullback function-field theorem with
ground field $K$, base $B=\operatorname{Spec}K$, total space $V=X$, and
$P=\operatorname{Spec}K_0$. The structure map of $X$ is flat because modules over a field are
flat; it is dominant and finite type, and its geometric fibres are reduced and its generic fibre
geometrically integral by hypothesis. The extension $k(P)/k(B)=K_0/K$ is finite. Thus
$k(X_{K_0})=F\otimes_K K_0$ is a field. Normalization is birational, so $k(N)$ equals this field;
both identifications use the structural maps, giving precisely the two stated embeddings.
Uses: lem-weil-pbc-module-over-field-flat, lem-sfb-flat-curve-pullback-function-field, lem-sc-
normalization-exists.

8. Let $K'/K_0$ be arbitrary. Apply step 4's affine argument to $T=K'$; it identifies the
normalization of $X_{K'}$ with $N_E\times_E K'=N\times_{K_0}K'$. Geometric integrality of $X$
means $X_{K'}$ is already reduced, even for inseparable or transcendental $K'/K_0$. Repeat the
nilpotent-ideal calculation of step 5 for the inverse image of $Z$. The scheme $D\times_{K_0}K'$
is already reduced by the geometric reducedness established there, so it is the reduced inverse
image, as required. Every identification agrees with the structural maps since on affine charts it
is the natural inclusion into the fraction field.
Uses: lem-sfb-integral-closure-geonormal-scalar-extension, def-pc-geometrically-irreducible, lem-
sc-reduction-nilradical-nilpotent.

The characteristic-zero clause uses surjectivity of the constants inclusion, the
node's specified meaning of equality of extensions; transport along its inverse
gives literally K₀ = K. The spectrum actions allow nonfaithful actions and arbitrary
actions on constants.
-/
theorem exists_invariant_marked_generic_normalization
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (Z : TopologicalSpace.Closeds X)
    (hZ : Z ≠ ⊤) (H : Type v) [Group H] [Finite H]
    (aK : H →* Aut (Spec (.of K))) (aX : H →* Aut X)
    (hcompat : ∀ h : H, (aX h).hom ≫ f = f ≫ (aK h).hom)
    (hmark : ∀ (h : H) (x : X), (aX h).hom x ∈ Z ↔ x ∈ Z) :
    ∃ (K₀ : Type u) (_ : Field K₀) (_ : Algebra K K₀),
      Nonempty (InvariantMarkedGenericNormalization.Data f Z H aK aX K₀) ∧
      (∀ [CharZero K], Function.Surjective (algebraMap K K₀)) := by
  sorry

end AlgebraicGeometry
