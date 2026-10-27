/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.AffineProjectiveCompactification
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents
import Sheaf.AlgebraicGeometry.NormalityPerfectClosureTest
import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import Sheaf.AlgebraicGeometry.DimensionExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.NoetherianSpace

/-!
# Normal projective compactification with constant boundary primes

Source: Stacks Project, Varieties, Tags 0GK4, 038N, 038O, 020I and 020J;
Morphisms, Tag 01WA; Algebra, Tag 00P3.
(blueprint: lem-sfb-algclosed-affine-normal-projective-boundary).

Closed subschemes are represented by their quasi-coherent ideals. Pulling back an ideal
with `comap` gives its scheme-theoretic inverse image, without taking a further reduction.
For an open immersion `j`, the inverse image of its image under the base-change projection
is the image of the base-changed open immersion. Thus the subtypes below are the actual
boundary spaces. The range equalities describe exactly their codimension-one components;
`Function.Injective` rules out repetitions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A smooth geometrically integral affine variety over an algebraically closed field has
an integral geometrically normal projective compactification with constant boundary primes.

Source: Stacks Project, Tags 0GK4, 038N, 038O, 020I, 020J, 01WA and 00P3.
(blueprint: lem-sfb-algclosed-affine-normal-projective-boundary)

Proof, following the eight steps of the node:
1. Apply [lem-kun-compactification-affine] to obtain a dense open immersion $X\hookrightarrow P$
   with $P$ projective. Replace $P$ by its reduction $P_0$, using [def-weil-pbc-scheme-reduction].
   This is a closed subscheme with the same underlying space. Its restriction to the open $X$ is
   $X$ itself, because $X$ is integral and therefore reduced: on an affine chart the nilradical
   restricts to zero on this open. Thus $X\hookrightarrow P_0$ is still a dense open immersion.
   The space $P_0$ is irreducible, since it contains the dense irreducible subspace $X$; being
   reduced and nonempty it is integral. Composing its closed immersion into $P$ with
   $P\hookrightarrow\mathbf P^n_k$ is a closed immersion (on local rings, compose the quotient
   maps), so $P_0$ is projective by [def-kun-projective]. The space $\mathbf P^n_k$ is covered by
   its $n+1$ standard affine charts, so it is quasi-compact, and its closed subset $P_0$ is
   quasi-compact; hence $P_0\to\operatorname{Spec}k$ is also projective in the quasi-compact
   convention of [def-pc-projective-morphism]. By [lem-pc-projective-proper] it is proper, hence
   finite type by [def-weil-proper-morphism].
2. Let $\nu:C=P_0^\nu\to P_0$ be normalization in its own function field [def-sc-normalization].
   The projective-normalization theorem [lem-weil-pbc-normalization-projective-components] gives a
   normal integral projective proper $C$: here $P_0$ has exactly one reduced irreducible
   component, so the componentwise normalization in that theorem has one summand and is exactly
   $P_0^\nu$. In particular $C$ is finite type. The base $\operatorname{Spec}k$ is normal, since
   its only local ring is the field $k$, an integrally closed domain. Applying
   [lem-sfb-smooth-normal-ascent] to $X\to\operatorname{Spec}k$ shows that $X$ is normal.
   Consequently [lem-sc-normalization-over-normal-locus] identifies $\nu^{-1}(X)\to X$ with an
   isomorphism. Its inverse followed by the open inclusion defines $j:X\hookrightarrow C$. It has
   nonempty image, and this image is dense because $C$ is integral. Projectivity supplies the
   required finite projective-space embedding.
3. The field $k$ is perfect: in positive characteristic $p$, a root in $k$ of $T^p-a$ is a $p$th
   root of each $a\in k$; characteristic zero already satisfies the definition of perfect. It is
   also separably closed, since every nonconstant polynomial has a root, so every irreducible
   polynomial has degree one. In [lem-weil-pbc-normality-perfect-closure-test] take $K=k$; the
   power condition holds with exponent index zero. Normality of $C$ therefore implies normality of
   every $C_F$, for arbitrary $F/k$. Taking $\Omega=k$ and $A=|C|$ in
   [lem-sbc-subset-geometric-irreducibility] proves that every $C_F$ is nonempty and irreducible.
   A scheme with domain local rings is reduced, so these schemes are integral. This proves
   geometric normality and geometric integrality with precisely the every-field-extension meanings
   in the statement.
4. By step 2, $C$ is proper, hence of finite type and in particular quasi-compact over $k$
   [def-weil-proper-morphism]; with its closed immersion into $\mathbf P^n_k$,
   $C\to\operatorname{Spec}k$ is projective in the convention of [def-pc-projective-morphism]. For
   every $F/k$, projectivity of $C_F\to\operatorname{Spec}F$ in that convention follows from
   [lem-pc-projective-base-change]. Thus [lem-pc-projective-proper] and [def-weil-proper-morphism]
   make $C_F$ proper and finite type. A field is Noetherian (its only ideals are zero and the
   whole field), so [lem-weil-pbc-finite-type-over-noetherian] shows that $C_F$ is Noetherian,
   including the finite affine-cover assertion in the statement. This also applies to $F=k$. By
   [lem-weil-pbc-open-immersion-base-change], $j_F$ is an open immersion. Write $Z=|C|\setminus
   j(X)$ and let $p:C_F\to C$ be projection. The complement of $j_F(X_F)$ is $p^{-1}Z$: the
   pullback of an open subscheme is its inverse-image open, as is seen directly by restricting the
   fibre-product universal property.
5. By [lem-sc-noetherian-closed-subset-finite-components], the closed subset $Z$ has finitely many
   distinct irreducible components $T_1,\ldots,T_s$; when $Z$ is empty use $s=0$. Give $T_a$ its
   reduced induced closed subscheme structure $D_a\hookrightarrow C$ by
   [lem-weil-pbc-reduced-induced-closed-subscheme]. Each $D_a$ is reduced, nonempty and
   irreducible, hence integral. It is finite type over $k$: on each affine chart of the
   finite-type scheme $C$ its ring is a quotient of the chart ring, still a finitely generated
   $k$-algebra, and a finite affine cover of $C$ restricts to a finite affine cover of $D_a$. This
   verifies the finite-type hypothesis required for each use of geometric reducedness and
   dimension below.
6. Fix any $F/k$. Apply [lem-sbc-subset-geometric-irreducibility] with $\Omega=k$, $X=D_a$, and
   its whole underlying set to show that $(D_a)_F$ is nonempty and irreducible. Since $k$ is
   perfect and $D_a$ is reduced of finite type, [lem-kun-geometric-reduced-perfect] says $(D_a)_F$
   is reduced. Thus every $D_a$ is geometrically integral. By
   [lem-weil-pbc-closed-immersion-base-change], $(D_a)_F\hookrightarrow C_F$ is a closed
   immersion; its image is $p^{-1}T_a$. Indeed, locally it is
   $\operatorname{Spec}((R/I)\otimes_kF)\to\operatorname{Spec}(R\otimes_kF)$, whose image is the
   zero set of the extended ideal $I$. The projection $(D_a)_F\to D_a$ is surjective by
   [lem-weil-pbc-surjective-base-change], applied to the surjective map
   $\operatorname{Spec}F\to\operatorname{Spec}k$. Finite type of $(D_a)_F$ follows from
   [lem-sfb-finite-type-composition-base-change].
7. The subsets $p^{-1}T_a$ cover $p^{-1}Z$, and are irreducible closed by step 6. They have no
   containment relations: a containment $p^{-1}T_a\subseteq p^{-1}T_b$ would imply $T_a\subseteq
   T_b$ by surjectivity of $(D_a)_F\to D_a$, hence $a=b$. An irreducible subset of a finite union
   of closed subsets lies in one of them (otherwise its intersections with these closed subsets
   give a finite proper closed covering, contradicting irreducibility). Therefore the $p^{-1}T_a$
   are exactly, without repetitions, all irreducible components of $p^{-1}Z$. Their reduced
   induced structures are $(D_a)_F$, by uniqueness in
   [lem-weil-pbc-reduced-induced-closed-subscheme], since these are already reduced closed
   subschemes with those supports.
8. By [lem-sc-scheme-sober], let $\eta_a$ be the unique generic point of $D_a$, viewed also as a
   point of $C$. Its local ring on $D_a$ is its function field [def-sc-function-field], so has
   dimension zero. The formula [lem-kun-dimension-formula] for $D_a$ and
   [lem-sc-dimension-locally-algebraic] give $\dim D_a=\operatorname{trdeg}_k\kappa(\eta_a)$. By
   [lem-weil-pbc-closed-immersion-residue-field-iso] this residue field is the same on $C$. Apply
   the same dimension formula and local constancy of dimension to the integral scheme $C$ to
   obtain $\dim C=\dim\mathcal O_{C,\eta_a}+\dim D_a$. The same argument over $F$ gives $\dim
   C_F=\dim\mathcal O_{C_F,\eta_{a,F}}+\dim(D_a)_F$. By [lem-kun-dimension-extension], $\dim
   C_F=\dim C$ and $\dim(D_a)_F=\dim D_a$. All these dimensions are finite for the present
   nonempty finite-type schemes, by [lem-kun-dimension-finite-type], so cancellation proves
   equality of the two displayed local-ring dimensions. In particular a component has codimension
   one exactly when its base-changed component does. Enumerate those $D_a$ with codimension one as
   $B_1,\ldots,B_r$. Steps 6--7 give geometric integrality and the asserted precise boundary list
   over every $F/k$. If none has codimension one, $r=0$ and the same argument gives the empty list
   after extension.
-/
theorem exists_algClosed_affine_normal_projective_boundary
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsAffine X]
    [Smooth f] [GeometricallyIntegral f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (C : Scheme.{u}) (p : C ⟶ Spec (.of k)) (j : X ⟶ C),
      LocallyOfFiniteType p ∧ QuasiCompact p ∧ IsHProjective p ∧
      j ≫ p = f ∧ IsOpenImmersion j ∧ DenseRange j ∧ GeometricallyIntegral p ∧
      (∀ (F : Type u) [Field F] [Algebra k F],
        IsIntegral (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F)))) ∧
        (∀ x : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}),
          IsDomain ((pullback p (Spec.map (CommRingCat.ofHom
            (algebraMap k F)))).presheaf.stalk x) ∧
          IsIntegrallyClosed ((pullback p (Spec.map (CommRingCat.ofHom
            (algebraMap k F)))).presheaf.stalk x)) ∧
        IsNoetherian (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F)))) ∧
        IsProper (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k F))))) ∧
      ∃ (r : ℕ) (B : Fin r → C.IdealSheafData),
        (∀ i : Fin r, IsReduced (B i).subscheme ∧
          GeometricallyIntegral ((B i).subschemeι ≫ p)) ∧
        Function.Injective (fun i : Fin r ↦ ((B i).support : Set C)) ∧
        Set.range (fun i : Fin r ↦ ((B i).support : Set C)) =
          {T : Set C | (∃ Z : Set {x : C // x ∉ Set.range j},
            Z ∈ irreducibleComponents {x : C // x ∉ Set.range j} ∧
            Subtype.val '' Z = T) ∧
            ∃ η : C, IsGenericPoint η T ∧ ringKrullDim (C.presheaf.stalk η) = 1} ∧
        ∀ (F : Type u) [Field F] [Algebra k F],
          (∀ i : Fin r, IsReduced
            ((B i).comap (pullback.fst p
              (Spec.map (CommRingCat.ofHom (algebraMap k F))))).subscheme) ∧
          Function.Injective (fun i : Fin r ↦
            (((B i).comap (pullback.fst p
              (Spec.map (CommRingCat.ofHom (algebraMap k F))))).support :
                Set (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}))) ∧
          Set.range (fun i : Fin r ↦
            (((B i).comap (pullback.fst p
              (Spec.map (CommRingCat.ofHom (algebraMap k F))))).support :
                Set (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}))) =
            {T : Set (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}) |
              (∃ Z : Set {x :
                  (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}) //
                  (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k F)))) x ∉
                    Set.range j},
                Z ∈ irreducibleComponents
                  {x : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}) //
                    (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k F)))) x ∉
                      Set.range j} ∧ Subtype.val '' Z = T) ∧
              ∃ η : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F))) : Scheme.{u}),
                IsGenericPoint η T ∧ ringKrullDim
                  ((pullback p (Spec.map (CommRingCat.ofHom
                    (algebraMap k F)))).presheaf.stalk η) = 1} := by
  sorry

end AlgebraicGeometry
