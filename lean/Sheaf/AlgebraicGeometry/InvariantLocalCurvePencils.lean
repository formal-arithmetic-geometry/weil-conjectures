/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.EtaleAtFieldExtension

/-! # Invariant local separating pencils

Source: de Jong, Families of curves and alterations, §§3.3--3.4, pp.605--606.
(blueprint: lem-sfb-invariant-local-curve-pencils)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The constant-field embedding into the fraction field of the scalar-extended function
field. This is the right tensor inclusion followed by the localization map, not a chosen map.
Source: de Jong §§3.3--3.4, pp.605--606.
(blueprint: lem-sfb-invariant-local-curve-pencils) -/
noncomputable def invariantPencilConstantMap
    (K F E : Type u) [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E] :
    E →+* FractionRing (F ⊗[K] E) :=
  (algebraMap (F ⊗[K] E) (FractionRing (F ⊗[K] E))).comp
    Algebra.TensorProduct.includeRight.toRingHom

/-- The three standard sections `[0:1]`, `[1:1]`, `[1:0]`, in that order.
Source: de Jong §3.4, p.606.
(blueprint: lem-sfb-invariant-local-curve-pencils) -/
noncomputable def invariantPencilSpecialPoint (S : Scheme.{u}) (j : Fin 3) :
    S ⟶ ProjectiveLine S :=
  if j = 2 then ProjectiveLine.infinity S else
    AffineSpace.homOfVector (𝟙 S) (fun _ ↦ if j = 0 then 0 else 1) ≫
      ProjectiveLine.affineChart S

/-- Local finite invariant pencils with the prescribed unramified generic fibres.
The function-field algebra is fixed by the generic stalk map; the compositum is its tensor
product's fraction field. Every comparison map below is fixed by its two projections.
Source: de Jong §§3.3--3.4, pp.605--606.
(blueprint: lem-sfb-invariant-local-curve-pencils)

Proof (the node's sixteen steps):

1. Apply [lem-sfb-finite-normal-relative-curve-model] with $E=K$ and $L=k(X)$. Its
scalar-extension clause applies to the given smooth geometrically integral generic curve. It
gives a finite surjection $\nu:N\to X$, where $N$ is the normalization in $k(X)$, $N\to S$ is
H-projective with pure one-dimensional geometric fibres, and $N_K=C$. Its functoriality extends
the $J$-action. Normality of $S$ identifies its normalization in $K$ with $S$: on affine normal
domains the integral closure in the fraction field is the same ring. Thus in positive base
dimension it suffices to construct the requested pencils on $N$, and no constant extension is
involved.
Uses: lem-sfb-finite-normal-relative-curve-model.

2. The projective-implies-proper theorem makes $N\to S$ proper. Also $S$ and $N$ are Noetherian
by [lem-weil-pbc-finite-type-over-noetherian], since they are of finite type over a field. The
image of $N$ in $S$ is closed and contains the generic point, hence is all of $S$. Thus every
fibre is nonempty. Replace $J$ by its image $G\subseteq\operatorname{Aut}_S(N)$; invariance
under $G$ will imply invariance under $J$. The action of $G$ on $C=N_K$ is faithful: if an
element is the identity there, its equalizer with the identity is closed because $N/S$ is
separated and contains the generic point of integral $N$. Its defining ideal is zero, since it
vanishes in $k(N)$ and affine coordinate rings of $N$ inject into that field. Hence the
equalizer is all of $N$. This reduction removes the kernel before taking any products; no scheme
quotient is constructed.
Uses: lem-kun-projective-implies-proper, lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-proper-closed-image, lem-sc-integral-function-field-affine-fraction.

3. Choose a projective embedding $i:N\hookrightarrow\mathbf P^D_S$ and put $L=i^*\mathcal O(1)$.
Form the invertible module $B=\bigotimes_{g\in G}g^*L$ and, for $a\in\Gamma(N_U,L^{\otimes n})$,
its norm section $\mathcal N_G(a)=\bigotimes_{g\in G}g^*a\in\Gamma(N_U,B^{\otimes n})$, where
$U\subseteq S$ is any open. These are genuine constructions with pullbacks and tensor products,
locally tensor products of free rank-one modules. For $h\in G$, the identification $h^*B\cong B$
permutes the factors by the bijection $g\mapsto gh$, and sends $h^*\mathcal N_G(a)$ to $\mathcal
N_G(a)$. In trivializations this is simply reordering a finite product. Therefore whenever two
norm sections generate, their projective-coordinate morphism is $G$-invariant. Pulling back to a
fibre commutes with this formula: both sides are the tensor product of the pulled-back sections.
Also $\mathcal N_G(a^m)=\mathcal N_G(a)^m$.
Uses: def-kun-projective, def-pc-module-pullback, def-pur-sheaf-tensor-product,
def-sc-invertible-module.

4. Assume $\dim S>0$, and fix a closed point $s\in S$. Choose an affine neighbourhood
$U=\operatorname{Spec}A$. The domain $A$ is infinite and its maximal ideal $\mathfrak m$ at $s$
is nonzero: otherwise $s$ would be the closed generic point of $S$, forcing $S$ to be a point; a
finite domain is a field. Hence $K=\operatorname{Frac}A$ is infinite. Apply the projective-ample
theorem to the embedding of $N_U$ from step 3, and to its base changes to $s$ and $K$. It makes
$L_U$, $L_s$ and $L_K$ ample invertible modules. The special fibre $N_s$ is nonempty, projective
and of dimension one, since its geometric fibre is pure of dimension one. The $G$-action
restricts to each of these fibres; only its generic restriction is required to be faithful.
Uses: lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-projective-ample-invertible.

5. Apply [lem-sfb-ample-curve-two-section-pencil] to $(N_s,L_s,G)$ to obtain $d\geq1$ and
sections $a_s,b_s$ whose norm pair gives a finite special-fibre pencil. For any $m\geq1$, the
sections $a_s^m,b_s^m$ have norms $\mathcal N_G(a_s)^m,\mathcal N_G(b_s)^m$. This is still a
generating pair and its pencil is the old finite pencil composed with $[x:y]\mapsto[x^m:y^m]$.
That power map is finite: on each standard affine chart the coordinate ring is free over the
power subring, with basis $1,t,\ldots,t^{m-1}$. Choose $m$ so large that $n=dm$ is at least both
the lifting threshold of [lem-trf-ample-fibre-section-lifting] for $(N_U,L_U,s)$ and the
threshold of [lem-sfb-separating-pair-open] for $(C,L_K,G)$. Lift the ordinary sections
$a_s^m,b_s^m$, intersect the two supplied neighbourhoods, and shrink to an affine neighbourhood
of $s$. Denote these ordinary lifts by $a_0,b_0$. Their norms restrict to the finite special
pencil. No assertion about lifting invariant sections is used.
Uses: lem-sfb-ample-curve-two-section-pencil, lem-weil-pbc-finite-composition,
lem-trf-ample-fibre-section-lifting, lem-sfb-separating-pair-open.

6. Put $V=\Gamma(C,L_K^{\otimes n})$ and $H=\Gamma(N_U,L^{\otimes n})$. Properness gives
quasi-compactness and quasi-separatedness. Since $A\to K$ is a flat localization, degree-zero
flat base change gives $H\otimes_AK=V$. Proper coherent cohomology gives finite dimensionality
of $V$. Choose $e_1,\ldots,e_t\in H$ whose images form a $K$-basis of $V$, by clearing the
finitely many denominators of a basis in $H\otimes_AK$. Fix $0\ne u\in\mathfrak m$. For
arbitrary $r_j,s_j\in A$, the ordinary pair $(a_0+u\sum r_je_j,b_0+u\sum s_je_j)$ keeps the
chosen special-fibre values, and therefore keeps their norms too. These pairs are Zariski dense
in $V^2$: their coefficient map is an invertible affine change of coordinates over $K$, and a
polynomial over $K$ vanishing on all of $A^{2t}$ is zero, by induction on the number of
variables and the univariate root bound over the infinite set $A$.
Uses: lem-pc-flat-base-change-cohom, lem-pc-coherent-hi.

7. By [lem-sfb-separating-pair-open], the chosen degree $n$ has a nonempty open $W_n\subseteq
V^2$ of ordinary section pairs whose norm pencil is finite, surjective and generically etale on
$C$. The faithful action required there was checked in step 2. The dense set in step 6 meets
$W_n$. Choose the corresponding global ordinary pair $(a,b)$ on $N_U$ and put $\alpha=\mathcal
N_G(a)$, $\beta=\mathcal N_G(b)$. On $N_s$ these keep the finite norm pencil; on $C$ their
pencil is finite surjective and generically etale. In particular they have no generic base
point. The residue field $\kappa(s)$ need not be infinite. The construction used only $N$, its
sections and its action.
Uses: lem-sfb-separating-pair-open.

8. The simultaneous zero locus $Z$ of $\alpha,\beta$ is closed, by the nonvanishing-section
theorem, and misses $N_s$. Since $N_U\to U$ is proper, its image is closed and misses $s$.
Remove this image and shrink affinely about $s$. The generating-sections criterion and the
projective-space construction now give $\psi=[\alpha:\beta]:N_U\to\mathbf P^1_U$, invariant by
step 3. This morphism is proper: its source is proper over $U$ and its target is proper, hence
separated, over $U$. Its fibre over $s$ is the finite norm pencil retained in step 7.
Uses: lem-weil-pbc-nonvanishing-section-trivializes, lem-weil-pbc-proper-closed-image,
lem-weil-pbc-invertible-generating-sections-fibre,
def-weil-pbc-morphism-to-projective-space-by-sections, lemma-nagata-proper-to-separated-target,
lemma-nagata-projective-space-base-change-proper.

9. For every $z\in\mathbf P^1_s$, the fibre of $\psi$ over $z$ is finite. The
proper-finite-fibre theorem gives an open neighbourhood $W_z\subseteq\mathbf P^1_U$ over which
$\psi$ is finite. Put $W=\bigcup_zW_z$. Its closed complement misses $\mathbf P^1_s$. The
projection $\mathbf P^1_U\to U$ is proper, so the image of that complement is closed and misses
$s$. Remove that image and shrink affinely once more. Now $\mathbf P^1_U\subseteq W$, so every
fibre of $\psi$ is finite, as it is a fibre of a finite restriction over some $W_z$. The target
is Noetherian, being of finite type over the Noetherian affine $U$. The proper-finite-fibres
criterion [thm-pqf-finite-iff-proper-finite-fibres] therefore makes $\psi$ finite. It remains
the invariant map directly constructed on $N_U$.
Uses: lem-trf-proper-finite-fibre-finite-near, lemma-nagata-projective-space-base-change-proper,
lem-weil-pbc-proper-closed-image, thm-pqf-finite-iff-proper-finite-fibres,
lem-weil-pbc-finite-closed-map-finite-fibres, lem-weil-pbc-finite-type-over-noetherian.

10. The finite map $\psi$ is surjective. It is surjective on the generic fibre by the
separating-pair lemma. Its image is closed by the finite-closed-map theorem and therefore
contains the closure of that generic fibre in $\mathbf P^1_U$, which is all of $\mathbf P^1_U$:
on either standard chart $\operatorname{Spec}A[t]$ the inclusion into $K[t]$ shows that every
function vanishing on the generic fibre is zero. Thus no point of the target is missed. The
restriction $\psi_K$ is generically etale by step 7.
Uses: lem-sfb-separating-pair-open, lem-weil-pbc-finite-closed-map-finite-fibres.

11. By the conclusion of [lem-sfb-separating-pair-open] choose a nonempty open $V_0\subseteq C$
on which $\psi_K$ is etale. Its complement $R$ is finite: it is a closed subset of the
Noetherian integral curve $C$ missing the generic point, so its dimension is at most zero (a
positive chain inside it could be extended by the generic point to a chain of length two); apply
[lem-sc-zero-dim-noetherian-closed-finite]. Hence $B=\psi_K(R\cup|M|)$ is a finite set of closed
points of $\mathbf P^1_K$, using the closed-map assertion for the finite map. Choose a nonzero
homogeneous polynomial $P(X,Y)\in K[X,Y]$ vanishing on $B$: homogenize the finitely many minimal
polynomials of its affine closed points and include a factor $Y$ if infinity belongs to $B$.
Uses: lem-sfb-separating-pair-open, lem-weil-pbc-finite-type-over-noetherian,
lem-sc-zero-dim-noetherian-closed-finite, lem-weil-pbc-finite-closed-map-finite-fibres.

12. Here is the coordinate change explicitly. Let $E_{ij}$ be the two-by-two matrix unit, and
write $u(a)=I+aE_{12}$ and $l(b)=I+bE_{21}$. The map $(a,b,c)\mapsto g=u(a)l(b)u(c)$ has
determinant one and parametrizes the open cell of $\mathrm{SL}_2$ with lower-left entry $b\ne0$:
its diagonal entries are $1+ab,1+bc$, which recover $a,c$. The condition $P(g^{-1}(v))\ne0$ for
each $v\in\{[0:1],[1:1],[1:0]\}$ is a nonempty open condition on this cell. Indeed each
vanishing condition is proper, since determinant-one matrices act transitively on the projective
line over an algebraic closure; explicitly extend any nonzero column to a determinant-one
matrix. A finite union of these proper polynomial zero loci cannot fill the integral affine
parameter space. Therefore their product gives a nonzero polynomial in $K[a,b,c]$. As in step 6,
it is nonzero at some $(a,b,c)\in A^3$. The resulting matrix defines an automorphism of $\mathbf
P^1_U$ over all of $U$, since its determinant is one. Put $\varphi=g\circ\psi$. Then
$\varphi_K^{-1}\{0,1,\infty\}$ avoids both $R$ and $M$.

13. All points above the three values now lie in the etale open $V_0$ for $\psi_K$ (with its
target relabelled by $g$). Base change of this etale morphism along each of the three rational
points shows that each inverse fibre is etale over $K$. It is finite because $\varphi_K$ is
finite; the finite-etale algebra criterion makes it a product of finite separable fields, so it
is reduced. The union of the three disjoint fibres has the same properties. This proves the
required marked-fibre assertion, including its separate disjointness from $M$. Finiteness,
surjectivity and $J$-invariance were preserved by the target automorphism.
Uses: lem-weil-pbc-etale-base-change-finite-limits, lem-sc-finite-etale-algebra-criterion.

14. Repeat steps 4--13 for every closed point $s$. The resulting affine neighbourhoods cover
$S$: a nonempty closed complement would contain a closed point. To see the latter directly,
choose a minimal nonempty closed subset using Noetherianity; it is a singleton since schemes are
$T_0$, and its point is closed in $S$. Quasi-compactness of the Noetherian scheme $S$ now
supplies a finite subcover. With $E=K$, step 1 identifies $X_E=N$ and $S_E=S$, giving exactly
the positive-dimensional assertion.
Uses: lem-weil-pbc-finite-type-over-noetherian.

15. If $\dim S=0$, the normal integral scheme $S$ is $\operatorname{Spec}K$: its underlying
space has just its generic point, an affine neighbourhood is all of $S$, and its reduced
zero-dimensional domain is a field. Thus $X=C$ is smooth and normal. Reduce $J$ to its effective
image $G$ as in step 2. Choose an embedding of $C$ in projective space and its ample $L$ by the
projective-ample theorem. By [lem-sfb-separating-pair-open], for any sufficiently large $n$
there is a nonempty open $W_n$ of ordinary section pairs giving finite surjective generically
etale norm pencils on $C$. Choose a separable closure $\Omega/K$. It is infinite: if it had $q$
elements, $T^q-T-1$, with derivative $-1$, would be separable without an $\Omega$-root. The
polynomial argument of step 6 gives a pair in $W_n(\Omega)$. Its norm pencil is invariant by
permutation of factors as in step 3. Steps 11--12 over $\Omega$ give a determinant-one
coordinate change avoiding the marking and the complement of an etale open. No quotient of $C$
is formed.
Uses: lem-sc-smooth-normal, lem-weil-pbc-projective-ample-invertible, lem-sfb-separating-pair-open,
lem-weil-pbc-separable-closure-exists-galois.

16. Let $E\subseteq\Omega$ be generated over $K$ by the finitely many coefficients of that
ordinary section pair and coordinate-change matrix. The algebraic-generators theorem makes $E/K$
finite, and the separable-closure theorem makes it separable. The pair belongs to $W(E)$ because
its defining nonvanishing polynomial conditions hold in $\Omega$, hence already in the subfield
$E$. Taking its norm pair therefore defines a finite surjective invariant pencil on $C_E$,
generically etale by the separating-pair lemma. The avoidance conditions hold after extension to
$\Omega$; etaleness at points descends along field extension by
[lem-sc-etale-base-change-geometric], and disjointness descends because field extension is
faithfully flat (a nonempty finite scheme over a field stays nonempty, as its nonzero
finite-dimensional coordinate algebra stays nonzero after tensoring). Apply step 13 over $E$.
Finally the scalar-extension clause of the normal-model theorem identifies
$S_E=\operatorname{Spec}E$ and $X_E=C_E$, identifies $k(X)\otimes_KE$ as a field, and extends
the $J$-action by fixing $E$. One affine open suffices. This gives every zero-dimensional
clause, including the finite-ground-field case.
Uses: lem-weil-pbc-algebraic-generators-finite-extension,
lem-weil-pbc-separable-closure-exists-galois, lem-sfb-separating-pair-open,
lem-sc-etale-base-change-geometric, lem-sfb-finite-normal-relative-curve-model.
-/
theorem exists_invariant_local_curve_pencils
    (k : Type u) [Field k] (S X : Scheme.{u})
    (pS : S ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [IsIntegral S] [IsIntegral X] [IsHProjective pS]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f] (hf : f ≫ pS = pX)
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback (C := Scheme.{u}) f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (M : Closeds (pullback (C := Scheme.{u}) f S.fromSpecFunctionField))
    (hMfinite : IsFinite ((Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField))
    (hMetale : Etale ((Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField))
    (J : Type v) [Group J] [Finite J] (σ : J →* Aut X)
    (hJ : ∀ j : J, (σ j).hom ≫ f = f)
    (hMstable : ∀ (j : J) (x y : pullback (C := Scheme.{u}) f S.fromSpecFunctionField),
      (σ j).hom (pullback.fst f S.fromSpecFunctionField x) =
        pullback.fst f S.fromSpecFunctionField y → (x ∈ M ↔ y ∈ M)) :
    ∃ (hη : f (genericPoint X) = genericPoint S)
      (_ : Algebra S.functionField X.functionField),
      algebraMap S.functionField X.functionField =
        (S.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
          f.stalkMap (genericPoint X)).hom ∧
    ∃ (E : Type u) (_ : Field E) (_ : Algebra S.functionField E)
      (_ : IsDomain (X.functionField ⊗[S.functionField] E)),
      Module.Finite S.functionField E ∧ Algebra.IsSeparable S.functionField E ∧
      (0 < topologicalKrullDim S →
        Function.Bijective (algebraMap S.functionField E)) ∧
    ∃ (q : X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] E)) ⟶
        S.normalizationIn E)
      (τ : J →* Aut (X.normalizationIn
        (FractionRing (X.functionField ⊗[S.functionField] E))))
      (r : ℕ) (U : Fin r → (S.normalizationIn E).Opens),
      q ≫ S.fromNormalizationIn E =
        X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] E)) ≫ f ∧
      (X.fromSpecOfAlgebraFunctionField
          (FractionRing (X.functionField ⊗[S.functionField] E))).toNormalization ≫ q =
        Spec.map (CommRingCat.ofHom
          (invariantPencilConstantMap S.functionField X.functionField E)) ≫
            (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
      (∀ j : J, (τ j).hom ≫
          X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] E)) =
        X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] E)) ≫
          (σ j).hom) ∧
      (∀ j : J, (τ j).hom ≫ q = q) ∧
      (⨆ i : Fin r, U i) = ⊤ ∧ (∀ i : Fin r, IsAffineOpen (U i)) ∧
      (topologicalKrullDim S = 0 →
        r = 1 ∧ IsIso (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
          IsIso (pullback.fst q (S.fromSpecOfAlgebraFunctionField E).toNormalization)) ∧
      ∀ i : Fin r,
        ∃ (φ : pullback (C := Scheme.{u}) q (U i).ι ⟶ ProjectiveLine (U i).toScheme)
          (τi : J →* Aut (pullback (C := Scheme.{u}) q (U i).ι))
          (e : Spec (.of E) ⟶ (U i).toScheme),
          e ≫ (U i).ι = (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
          φ ≫ ProjectiveLine (U i).toScheme ↘ (U i).toScheme =
            pullback.snd q (U i).ι ∧ IsFinite φ ∧ Surjective φ ∧
          (∀ j : J, (τi j).hom ≫ pullback.fst q (U i).ι =
            pullback.fst q (U i).ι ≫ (τ j).hom) ∧
          (∀ j : J, (τi j).hom ≫ φ = φ) ∧
        ∃ (ψ : pullback (C := Scheme.{u}) (pullback.snd q (U i).ι) e ⟶
            ProjectiveLine (Spec (.of E)))
          (c : pullback (C := Scheme.{u}) (pullback.snd q (U i).ι) e ⟶
            pullback (C := Scheme.{u}) f S.fromSpecFunctionField),
          ψ ≫ ProjectiveLine (Spec (.of E)) ↘ Spec (.of E) =
            pullback.snd (pullback.snd q (U i).ι) e ∧
          ψ ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) e =
            pullback.fst (pullback.snd q (U i).ι) e ≫ φ ∧
          c ≫ pullback.fst f S.fromSpecFunctionField =
            pullback.fst (pullback.snd q (U i).ι) e ≫ pullback.fst q (U i).ι ≫
              X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] E)) ∧
          c ≫ pullback.snd f S.fromSpecFunctionField =
            pullback.snd (pullback.snd q (U i).ι) e ≫
              Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) ∧
          (∃ V : (pullback (C := Scheme.{u}) (pullback.snd q (U i).ι) e).Opens,
            Nonempty V ∧ Etale (V.ι ≫ ψ)) ∧
          (∀ j : Fin 3,
            IsFinite (pullback.snd ψ (invariantPencilSpecialPoint (Spec (.of E)) j)) ∧
            Etale (pullback.snd ψ (invariantPencilSpecialPoint (Spec (.of E)) j))) ∧
          (∀ (z : pullback (C := Scheme.{u}) (pullback.snd q (U i).ι) e),
            (∃ j : Fin 3, ψ z ∈
              Set.range (invariantPencilSpecialPoint (Spec (.of E)) j)) → c z ∉ M) := by
  sorry

end AlgebraicGeometry
