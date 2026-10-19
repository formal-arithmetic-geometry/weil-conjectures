/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.AlgebraicGeometry.NodalPointLocalCriterion
import Sheaf.TraceFormula.RelativeDimensionBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Jacobson.Ring
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange
import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.TraceFormula.SyntomicLocusBaseChange

/-! # The nodal open locus in a flat family

Source: Stacks Project, `curves.tex`, Tag 0DSC, lemma-locus-where-nodal
(blueprint: lem-trf-nodal-open-locus).

## Main definitions and statements

* `IsOrdinaryNode`: a closed point with completed local ring `Ω[[u,v]]/(uv)`.
* `IsSmoothOrOrdinaryNode`: the pointwise disjunction on a geometric fibre.
* `HasOnlySmoothOrNodalGeometricFibres`: this condition on every geometric fibre.
* `nodalOpenLocus`: existence, largestness, base change, and geometric-fibre description.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An ordinary node over `Ω` is a closed point with the specified completed local ring.
The coefficient field is algebraically closed whenever this predicate is used below.
Source: Stacks Project, `curves.tex`, definition-nodal and Tag 0DSC
(blueprint: lem-trf-nodal-open-locus). -/
def IsOrdinaryNode (Ω : Type u) [Field Ω] (X : Scheme.{u}) (x : X) : Prop :=
  x ∈ closedPoints X ∧ Nonempty
    (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+*
      (MvPowerSeries (Fin 2) Ω ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
          (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))

/-- A point of a geometric fibre is smooth or an ordinary node.
Source: Stacks Project, `curves.tex`, Tag 0DSC (blueprint: lem-trf-nodal-open-locus). -/
def IsSmoothOrOrdinaryNode {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation f] (x : X) : Prop :=
  x ∈ (f.smoothLocus : Set X) ∨ IsOrdinaryNode Ω X x

/-- Every geometric fibre of `f` consists of smooth points and ordinary nodes.
Geometric tests use the scheme universe, as for Mathlib's geometric morphism properties;
no test-field universe smaller than the scheme universe is introduced.
Source: Stacks Project, `curves.tex`, Tag 0DSC (blueprint: lem-trf-nodal-open-locus). -/
def HasOnlySmoothOrNodalGeometricFibres {X T : Scheme.{u}} (f : X ⟶ T)
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
    ∀ x : (pullback (C := Scheme.{u}) f g),
      IsSmoothOrOrdinaryNode (pullback.snd f g) x

/-- The largest nodal open of a flat, locally finitely presented family with pure
one-dimensional nonempty geometric fibres, compatible with arbitrary base change.

Source: Stacks Project, `curves.tex`, Tag 0DSC, lemma-locus-where-nodal
(blueprint: lem-trf-nodal-open-locus).

Proof plan, following the eight steps of the node:
1. The pure-dimension hypothesis also holds over every algebraically closed field mapping to $T$,
   not only the chosen algebraic closure of a residue field. For such $\Omega$ over $t$,
   [lem-weil-pbc-algebraic-extension-embeds-algebraically-closed] embeds $\overline{\kappa(t)}$
   into $\Omega$ over $\kappa(t)$. Associating fibre products identifies $Y_\Omega$ with
   $(Y_{\overline{\kappa(t)}})_\Omega$. The first fibre is locally of finite presentation, hence
   locally of finite type, by [lem-weil-pbc-qcqs-morphism-permanence](3). Apply
   [lem-trf-relative-dimension-base-change] to its structure morphism to the field: its sole
   nonempty fibre is pure of dimension $1$, so the base-changed scheme is pure of dimension $1$
   too. Empty fibres stay empty. Thus every geometric fibre of every base change of $p$ has the
   required dimension, since it is the fibre of $p$ at the composite geometric point.

2. Let $Z=\operatorname{Sing}(p)\hookrightarrow Y$ as defined in
   [def-trf-first-fitting-singular-subscheme]. Its formation commutes with arbitrary base change,
   without a nodality assumption: on affine charts [lem-weil-pbc-fibre-product-affine-spectra]
   gives $B'=A'\otimes_AB$, and [lem-weil-pbc-kahler-differentials-base-change] gives
   $\Omega_{B'/A'}\cong B'\otimes_B\Omega_{B/A}$. Apply
   [lem-trf-fitting-ideal-independence-base-change](2) to the finite $B$-module $\Omega_{B/A}$
   with $k=1$. It identifies its extended Fitting ideal with
   $\operatorname{Fit}_1(\Omega_{B'/A'})$. Quotienting by this extended ideal is exactly the base
   change of the defining closed subscheme; the identifications agree on localizations and glue.
   Hence $\operatorname{Sing}(p')=Z\times_TT'$ canonically for every base change.

3. Apply [lem-trf-dth-fitting-smooth-locus] with $d=1$ to $p$. Its hypotheses are the given
   flatness and local finite presentation and the given pure geometric-fibre dimension. It gives
   the open smooth locus $M=Y\setminus|Z|$. Apply it also to each geometric fibre morphism
   $Y_\Omega\to\operatorname{Spec}\Omega$: flatness and local finite presentation follow from
   [lem-weil-pbc-flat-morphism-base-change] and [lem-weil-pbc-qcqs-morphism-permanence](3), and
   all its geometric fibres have dimension $1$ by Step 1. Together with Step 2 this says
   $M_\Omega$ is exactly the smooth locus of $Y_\Omega$. In particular every point outside
   $Z_\Omega$ is smooth, including nonclosed points.

4. Let $V=V_p$ be the open of [lem-trf-syntomic-locus-base-change]. The morphism $h:Z\to T$ is
   locally of finite type: by [lem-weil-pbc-lft-affine-pairs] a finite-type affine chart $A\to B$
   for $p$ restricts to $A\to B/I$ for $Z$, and the images of the generators of $B$ generate its
   quotient. Let $W=W_h$ be its unramified open from [lem-trf-unramified-locus-base-change].
   Define $U=M\cup(V\cap W)$ as a subset of $Y$. It is open: $W\cap V$ is open in the closed
   subset $Z$, so $|Z|\setminus(W\cap V)$ is closed in $Y$, and its complement is exactly $U$. We
   retain the intersection with $V$; unramifiedness of the singular subscheme alone does not
   impose the complete-intersection condition.

5. Fix an algebraic closure $\Omega$ of $\kappa(t)$ and put $C=Y_\Omega$. Step 2 identifies
   $Z_\Omega$ with $\operatorname{Sing}(C/\Omega)$. By [lem-trf-syntomic-locus-base-change] and
   [lem-trf-lci-pointwise-criterion], every point of $V_\Omega$ has an affine open neighbourhood
   in $C$ which is a local complete intersection over $\Omega$: all fibre local rings there are
   complete intersections, and the pointwise criterion applies to that open. If $x\in V_\Omega\cap
   W_\Omega$, [lem-trf-unramified-locus-base-change] gives $\mathcal O_{Z_\Omega,x}=\kappa(x)$
   with $\kappa(x)/\Omega$ finite separable. The closed immersion preserves this residue field,
   and [lem-trf-finite-residue-point-closed-in-fibre] applied to $C\to\operatorname{Spec}\Omega$
   makes $x$ closed in $C$. Now [lem-trf-nodal-point-local-criterion] applies to this pure
   one-dimensional locally finite-type scheme: its three right-hand conditions have just been
   verified, so $x$ is an ordinary node. Points of $M_\Omega$ are smooth by Step 3.

6. Conversely, let $x$ be an ordinary node of $C$. Its closedness is part of the definition in the
   item. Apply [lem-trf-nodal-point-local-criterion]: $x$ has an affine
   local-complete-intersection neighbourhood, $\mathcal O_{Z_\Omega,x}=\kappa(x)$, and
   $\kappa(x)/\Omega$ is finite separable. The local-ring implication of
   [lem-trf-lci-pointwise-criterion] puts $x$ in the fibrewise complete-intersection locus, hence
   in $V_\Omega$ by [lem-trf-syntomic-locus-base-change]. The pointwise fibre-local-ring
   characterization in [lem-trf-unramified-locus-base-change] puts $x$ in $W_\Omega$. Every smooth
   point belongs to $M_\Omega$ by Step 3. Therefore $U_\Omega$ is exactly the union of the smooth
   points and the ordinary nodes of $C$, proving the precise geometric-fibre assertion. Local
   rings and their completions do not change on an open neighbourhood, so this also proves that
   the geometric fibres of $U$ have only the stated points.

7. For arbitrary $g:T'\to T$, the morphism $p'$ is flat and locally of finite presentation by
   [lem-weil-pbc-flat-morphism-base-change] and [lem-weil-pbc-qcqs-morphism-permanence](3). Step 1
   verifies its geometric-fibre dimension hypothesis. Its singular subscheme is the pullback of
   $Z$ by Step 2, hence its $M'$ is the inverse image of $M$ by the support formula of
   [lem-trf-dth-fitting-smooth-locus]. Its $V'$ is the inverse image of $V$ by
   [lem-trf-syntomic-locus-base-change]. Its $W'$ is the inverse image of $W$ by
   [lem-trf-unramified-locus-base-change], applied to $h:Z\to T$, whose base change is
   $Z\times_TT'\to T'$. Taking the inverse image of $M\cup(V\cap W)$ now gives exactly
   $M'\cup(V'\cap W')$. Thus the open constructed for $p'$ is $U\times_TT'$. Steps 5--6 apply to
   $p'$ as well.

8. Let $O\subseteq Y$ be any open with smooth or nodal geometric fibres, and fix $C=Y_\Omega$ as
   above. A smooth point of $O_\Omega$ is smooth in $C$, since its local map is unchanged. A node
   $x$ is closed in $O_\Omega$; on a finite-type affine neighbourhood its residue field is a
   finitely generated field extension of $\Omega$, so [lem-weil-pbc-zariski-lemma] makes it
   finite. Then [lem-trf-finite-residue-point-closed-in-fibre] makes $x$ closed in $C$. Its
   completed local ring is unchanged, so it is a node of $C$. Step 6 gives $O_\Omega\subseteq
   U_\Omega$. The projection $C\to Y_t$ is surjective: on each affine fibre chart it is the
   spectrum of the faithfully flat field-extension base-change map
   [lem-weil-pbc-field-extension-base-change-faithfully-flat], hence surjective by
   [lem-weil-pbc-faithfully-flat-surjective-spectrum], using
   [lem-weil-pbc-fibre-product-affine-spectra]. Thus $O\subseteq U$, proving largestness. The same
   surjectivity shows $Y_t\subseteq U$ if and only if $U_\Omega=C$; by Step 6 this is precisely
   that every singular point of $C$ is an ordinary node.
-/
theorem nodalOpenLocus
    (Y T : Scheme.{u}) (p : Y ⟶ T) [Flat p]
    [LocallyOfFinitePresentation p]
    (hgeom : ∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
      [IsAlgClosure (T.residueField t) Ω],
      Nonempty (pullback (C := Scheme.{u}) p
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t)) →
      (pullback p (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
        T.fromSpecResidueField t)).IsPureDimension 1) :
    ∃ U : Y.Opens,
      HasOnlySmoothOrNodalGeometricFibres (U.ι ≫ p) ∧
      (∀ V : Y.Opens,
        HasOnlySmoothOrNodalGeometricFibres (V.ι ≫ p) → V ≤ U) ∧
      (∀ (T' : Scheme.{u}) (g : T' ⟶ T),
        HasOnlySmoothOrNodalGeometricFibres
            ((pullback.fst p g ⁻¹ᵁ U).ι ≫ pullback.snd p g) ∧
        (∀ V : (pullback p g).Opens,
          HasOnlySmoothOrNodalGeometricFibres (V.ι ≫ pullback.snd p g) →
            V ≤ pullback.fst p g ⁻¹ᵁ U)) ∧
      (∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
        [IsAlgClosure (T.residueField t) Ω],
        ∀ x : (pullback (C := Scheme.{u}) p
          (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
            T.fromSpecResidueField t)),
          pullback.fst p
              (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                T.fromSpecResidueField t) x ∈ U ↔
            IsSmoothOrOrdinaryNode
              (pullback.snd p
                (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                  T.fromSpecResidueField t)) x) ∧
      (∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
        [IsAlgClosure (T.residueField t) Ω],
        ((∀ x : (pullback (C := Scheme.{u}) p (T.fromSpecResidueField t)),
            pullback.fst p (T.fromSpecResidueField t) x ∈ U) ↔
          (∀ x : (pullback (C := Scheme.{u}) p
              (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                T.fromSpecResidueField t)),
            x ∉ (pullback.snd p
                (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                  T.fromSpecResidueField t)).smoothLocus →
              IsOrdinaryNode Ω
                (pullback p
                  (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                    T.fromSpecResidueField t)) x))) := by
  sorry

end AlgebraicGeometry
