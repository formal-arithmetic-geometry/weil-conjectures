/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.TraceFormula.MultipointedCurve
import Sheaf.AlgebraicGeometry.MultipointedCurveModification
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine
import Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection
import Sheaf.AlgebraicGeometry.FiniteSurjectiveAmpleReflection
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.ReducedCurveNormalization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Projective nodal pinching over a discrete valuation ring

Source: Stacks Project, more-morphisms.tex, Tags 0E25--0E27; curves.tex,
Tags 0E36 and 0C1J; the trait argument recorded in the DAG.
(blueprint: lem-sfb-trait-etale-branch-pinching).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pinching finite étale double branches in the relative smooth locus of a projective
nodal curve over a DVR. The geometric fibres are nonempty and reduced of pure dimension
one, with the nodal completion at every nonsmooth closed point; they may be disconnected.
The `Over` morphisms retain all structure-map compatibilities. `IsPushout` is in schemes,
so its universal property applies to maps to every scheme, without base-linearity.
The fraction and residue fields are the canonical `FractionRing R` and
`IsLocalRing.ResidueField R`; no choice of either field changes the assertion.

Source: Stacks Project, more-morphisms.tex, Tags 0E25--0E27; curves.tex,
Tags 0E36 and 0C1J (blueprint: lem-sfb-trait-etale-branch-pinching).

Proof plan from the DAG:

1. Choose a projective-space embedding of $C/S$. Its hyperplane bundle restricts to an ample
invertible sheaf $L$ on $C$ by [lem-weil-pbc-projective-ample-invertible]. Also $C/S$ is proper:
projective space is proper by [lemma-nagata-projective-space-base-change-proper], and a closed
subscheme of a proper scheme is proper by [lem-weil-pbc-closed-immersion-proper]. The spectrum of
a DVR consists of its generic and closed points [def-sc-discrete-valuation-ring]. By
[lem-weil-pbc-finite-closed-map-finite-fibres], both fibres of $B/S$ are finite sets, so $|B|$ is
finite. Apply [lem-sc-ample-finite-set-affine] to obtain an affine open of $C$ containing $B$. In
particular it contains each fibre of $B\to N$, verifying the affine-neighbourhood hypothesis of
the Ferrand theorem. The constant degree two condition makes $B\to N$ surjective, including when
both are empty.
   Uses: lem-weil-pbc-projective-ample-invertible,
lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-closed-immersion-proper,
def-sc-discrete-valuation-ring, lem-weil-pbc-finite-closed-map-finite-fibres,
lem-sc-ample-finite-set-affine.

2. Apply [lem-sfb-ferrand-scheme-pushout] with $(X,Z,T)=(C,B,N)$; finite implies integral. Obtain
$Y$ and maps $a:C\to Y$, $b:N\hookrightarrow Y$. The theorem gives the cartesian square, the
universal property for maps to every scheme, and the isomorphism $C\setminus B\simeq Y\setminus
N$, since $B\to N$ is surjective. Its quotient-space description also makes $a$ surjective. On a
simultaneous affine chart write $P=A\times_DE$, with $\operatorname{Spec}A\subseteq C$,
$\operatorname{Spec}E\subseteq N$, $\operatorname{Spec}D\subseteq B$. The map $E\to D$ is finite.
Choose $E$-module generators $d_1,\ldots,d_r$ of $D$ and lifts $x_i\in A$. For $x\in A$ write its
image as $\sum e_id_i$ and lift each $e_i$ to a pair $(u_i,e_i)\in P$, possible because $A\to D$
is surjective. Then $x-\sum u_ix_i$ belongs to $\ker(A\to D)$ and is the $A$-coordinate of a pair
in $P$. Thus $1,x_1,\ldots,x_r$ generate $A$ over $P$. The affine morphism $a$ is finite.
   Uses: lem-sfb-ferrand-scheme-pushout.

3. The base $S$ is Noetherian, since a DVR is Noetherian [def-sc-discrete-valuation-ring]. The
Ferrand theorem [lem-sfb-ferrand-scheme-pushout] makes $Y/S$ separated and locally of finite type.
The finite surjection $a$ and quasi-compactness of $C$ make $Y$ quasi-compact, so $Y/S$ is of
finite type. It is universally closed: after any $S'\to S$, the map $a_{S'}$ is surjective by
[lem-weil-pbc-surjective-base-change], and $C_{S'}/S'$ is proper by
[lem-weil-pbc-proper-base-change]. For a closed subset $F\subseteq Y_{S'}$, its inverse image in
$C_{S'}$ is closed and has the same image in $S'$ as $F$; that image is closed. Hence $Y/S$ is
proper by [def-weil-proper-morphism]. Finally [pqf-lem-lft-fp-locnoeth] gives local finite
presentation; quasi-compactness and separatedness give finite presentation.
   Uses: def-sc-discrete-valuation-ring, lem-sfb-ferrand-scheme-pushout,
lem-weil-pbc-surjective-base-change, lem-weil-pbc-proper-base-change, def-weil-proper-morphism,
pqf-lem-lft-fp-locnoeth.

4. On the affine charts of Step 2 the $R$-modules $A,E,D$ are flat: $C/S$ is flat and $B/S,N/S$
are etale, hence flat by [def-weil-etale-morphism]. In particular $A\oplus E$ is torsion free over
the DVR $R$, and so is its submodule $P=A\times_DE$. By
[lem-weil-pbc-pid-torsion-free-module-flat], $P$ is $R$-flat. Thus $Y/S$ is flat. Moreover the
sequence $$0\longrightarrow P\longrightarrow A\oplus E\xrightarrow{(u,v)\mapsto\bar
u-j^*v}D\longrightarrow0$$ is exact, because $A\to D$ is surjective. Since its last term $D$ is
$R$-flat, [lem-weil-pbc-flat-quotient-tensor-injective] keeps it exact after tensoring with every
$R$-algebra $R'$, so $$P\otimes_RR'\cong(A\otimes_RR')\times_{D\otimes_RR'}(E\otimes_RR'),$$ and
$A\otimes_RR'\to D\otimes_RR'$ is still surjective. Now let $S'=\operatorname{Spec}R'$ be the
generic point or a geometric point of $S$. The base-changed diagram $C_{S'}\hookleftarrow
B_{S'}\to N_{S'}$ satisfies the hypotheses of [lem-sfb-ferrand-scheme-pushout]: $B_{S'}\to C_{S'}$
is a closed immersion by [lem-weil-pbc-closed-immersion-base-change]; $B_{S'}\to N_{S'}$ is
finite, since on affine charts the finite module generators persist under $-\otimes_RR'$; and the
inverse image $U\times_SS'$ of the affine open $U\supseteq B$ of Step 1 is affine, being
$\operatorname{Spec}$ of a tensor product of rings, and contains $B_{S'}$. So the pushout
$P'=C_{S'}\amalg_{B_{S'}}N_{S'}$ exists, and the base changes of $a,b$ induce a canonical map
$\varphi:P'\to Y_{S'}$. For a chart $W$ of Step 2, the open
$W_{S'}=\operatorname{Spec}(P\otimes_RR')$ has inverse images $\operatorname{Spec}(A\otimes_RR')$,
$\operatorname{Spec}(E\otimes_RR')$, $\operatorname{Spec}(D\otimes_RR')$ in
$C_{S'},N_{S'},B_{S'}$. By the affine clause of [lem-sfb-ferrand-scheme-pushout] and the displayed
identity, $W_{S'}$ is the pushout of these three affine schemes. By its open-restriction clause,
applied in $P'$, so is $\varphi^{-1}(W_{S'})$, which has the same three inverse images. Hence
$\varphi$ is an isomorphism over every $W_{S'}$, and these opens cover $Y_{S'}$. So $Y_{S'}$ is
the pushout of the base-changed diagram, and its square is the Ferrand square of that diagram.
This includes the nonflat base change to a geometric point of the special fibre.
   Uses: def-weil-etale-morphism, lem-weil-pbc-pid-torsion-free-module-flat,
lem-weil-pbc-flat-quotient-tensor-injective, lem-weil-pbc-closed-immersion-base-change,
lem-sfb-ferrand-scheme-pushout.

5. Fix a geometric fibre over an algebraically closed field $\Omega$. Base change of the etale
maps is etale by [lem-sbc-smooth-relative-dimension-permanence], using relative dimension zero.
The finite maps remain finite: on affine charts, tensor the finite lists of module generators. The
fibre decomposition [lem-weil-pbc-etale-fibre-discrete-separable-points], applied over $\Omega$,
identifies $B_\Omega,N_\Omega$ with finite disjoint unions of $\operatorname{Spec}\Omega$. Each
fibre of $B_\Omega\to N_\Omega$ consists of two distinct points, by constant degree two. The
immersion remains closed by [lem-weil-pbc-closed-immersion-base-change], and its image is smooth
on $C_\Omega$ by [lem-pc-proper-base-change](2). The given reduced pure one-dimensional nodal
curve $C_\Omega$ is proper over $\Omega$ by [lem-weil-pbc-proper-base-change], hence separated and
of finite type. Its nonsmooth closed points are ordinary double points by hypothesis. Each
nonclosed point is the generic point of an irreducible component, since $C_\Omega$ has dimension
one. Such a point is smooth: [lem-weil-pbc-reduced-curve-normalization] gives a dense open
$X'\subseteq C_\Omega$ isomorphic to an open of a smooth $\Omega$-scheme, and a dense open
contains every generic point. Hence, with the flatness and finite presentation of the base change,
$(C_\Omega,\varnothing)$ is a semistable multipointed $\Omega$-curve with empty marking, by
[def-trf-multipointed-curve, def-trf-multipointed-curve-modification]. Apply
[lem-trf-relative-nodal-point-pinching] with reference scheme $\operatorname{Spec}\Omega$. By Step
4 and uniqueness of the pushout, its output is $Y_\Omega$. Hence $Y_\Omega$ has pure dimension one
and is nodal. It is reduced because its structure sheaf $a_*\mathcal
O_{C_\Omega}\times_{c_*\mathcal O_{B_\Omega}}b_*\mathcal O_{N_\Omega}$ is a subsheaf of
$a_*\mathcal O_{C_\Omega}\times b_*\mathcal O_{N_\Omega}$, whose rings of sections are reduced
[lem-sfb-ferrand-scheme-pushout]; at each new node its completed local ring is
$$\Omega[[u]]\times_\Omega\Omega[[v]]\cong\Omega[[u,v]]/(uv).$$ Old nonsmooth points are unchanged
since the branches were in the smooth locus. Surjectivity gives nonempty fibres. No connectedness
is required in the cited multipointed-curve definitions or field pinching lemma.
   Uses: lem-sbc-smooth-relative-dimension-permanence,
lem-weil-pbc-etale-fibre-discrete-separable-points, lem-weil-pbc-closed-immersion-base-change,
lem-pc-proper-base-change, def-trf-multipointed-curve, def-trf-multipointed-curve-modification,
lem-weil-pbc-proper-base-change, lem-trf-relative-nodal-point-pinching,
lem-weil-pbc-reduced-curve-normalization, lem-sfb-ferrand-scheme-pushout.

6. Use the affine open $U\subseteq C$ containing $B$ from Step 1. By
[lem-sfb-affine-invertible-finite-set-section] there is $s\in\Gamma(U,L)$ nonzero in every residue
fibre at a point of $B$. Let $U_s$ be its nonvanishing locus. Locally in a frame of the rank-one
locally free sheaf, $s$ is a scalar; nonzero residue means a unit in the local ring, and the
invertibility locus of a scalar is open. Thus $U_s$ is open, contains $B$, and $s$ trivializes
$L|_{U_s}$. Since $a$ is finite, [lem-weil-pbc-finite-closed-map-finite-fibres] makes
$a(C\setminus U_s)$ closed. Set $W=Y\setminus a(C\setminus U_s)$. Then $N\subseteq W$: the
cartesian square gives $a^{-1}(N)=B\subseteq U_s$. Also $a^{-1}(W)\subseteq U_s$. We have
therefore trivialized $L$ on the full inverse image of a neighbourhood of $N$, rather than just on
its branch subscheme.
   Uses: lem-sfb-affine-invertible-finite-set-section, def-sc-invertible-module,
lem-weil-pbc-finite-closed-map-finite-fibres.

7. Cover $Y$ by $W$ and $Y\setminus N$. On $W$ take $\mathcal O_W$; on $Y\setminus N\simeq
C\setminus B$ take $L|_{C\setminus B}$. On their intersection identify these sheaves by the frame
$s$ on $a^{-1}(W)$. The transition and its inverse satisfy the cocycle identities, so
[lem-weil-pbc-glue-sheaves-of-modules] gives a sheaf $M$ on $Y$. It is locally free of rank one on
both members of this cover, hence invertible by [def-sc-invertible-module]. Its pullback $a^*M$ is
identified with $L$ on $a^{-1}(W)$ by $s$ and on $C\setminus B$ by the identity; these two
identifications agree on their overlap by the chosen transition. They glue to $a^*M\simeq L$.
   Uses: lem-weil-pbc-glue-sheaves-of-modules, def-sc-invertible-module.

8. Both $C$ and $Y$ are proper over the Noetherian ring $R$, and $a:C\to Y$ is finite surjective.
By [lem-trf-finite-surjective-ample-reflection], $a^*M\simeq L$ ample implies that $M$ is ample.
Apply [lem-weil-pbc-ample-very-ample-immersion-affine-base] to obtain an $S$-immersion $h:Y\to
P_n=\operatorname{Proj}(R[x_0,\ldots,x_n])$. With $\mathbf Z\to R$ and the graded isomorphism
$R\otimes_{\mathbf Z}\mathbf Z[x_0,\ldots,x_n]\cong R[x_0,\ldots,x_n]$,
[lem-nagata-affine-proj-scalar-extension] identifies $P_n$ over $S$ with
$S\times_{\operatorname{Spec}\mathbf Z}\mathbf P^n_{\mathbf Z}=\mathbf P(\{0,\ldots,n\};S)$. This
target is proper by [lemma-nagata-projective-space-base-change-proper], hence separated, and
[lem-weil-pbc-proper-to-separated] makes $h$ proper. An immersion is a monomorphism. Write it as a
closed immersion followed by an open immersion; the latter is a monomorphism by
[lem-weil-pbc-open-immersion-monomorphism]. A closed immersion is one too: it is injective on
points, and $\mathcal O_X\to i_*\mathcal O_Z$ is surjective [def-weil-closed-immersion]. Therefore
[lem-pc-proper-monomorphism-closed] makes $h$ a closed immersion. This is projectivity in the
precise finite-projective-space convention of the item.
   Uses: lem-trf-finite-surjective-ample-reflection,
lem-weil-pbc-ample-very-ample-immersion-affine-base,
lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-proper-to-separated,
lem-pc-proper-monomorphism-closed, def-weil-closed-immersion,
lem-nagata-affine-proj-scalar-extension, lem-weil-pbc-open-immersion-monomorphism.

9. For every open subscheme $V\subseteq Y$, [lem-sfb-ferrand-scheme-pushout] gives exactly the
pushout of its inverse images in $C,N,B$. In particular the universal property is a property in
all schemes, so the compatible maps in the statement require no separatedness or base-linearity
hypothesis. If $B=N=\varnothing$, the construction is $Y=C$; the ring formula has $D=E=0$ and
$P=A$, and all conclusions hold. This also covers the empty branch case without forcing
connectedness of any fibre.
   Uses: lem-sfb-ferrand-scheme-pushout.
-/
theorem exists_trait_etale_branch_pinching
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (C B N : Over (Spec (.of R)))
    [IsHProjective C.hom] [Flat C.hom] [LocallyOfFinitePresentation C.hom]
    [IsFinite B.hom] [Etale B.hom] [IsFinite N.hom] [Etale N.hom]
    (i : B ⟶ C) (j : B ⟶ N) [IsClosedImmersion i.left] [Etale j.left]
    [j.left.IsFiniteLocallyFreeOfDegree 2]
    (hi : ∀ z : B.left, i.left z ∈ C.hom.smoothLocus)
    (hC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
      Nonempty ↥(pullback (C := Scheme.{u}) C.hom g) ∧
        IsReduced (pullback (C := Scheme.{u}) C.hom g) ∧
        (pullback (C := Scheme.{u}) C.hom g).IsPureDimension 1 ∧
        ∀ x : ↥(pullback (C := Scheme.{u}) C.hom g),
          IsClosed ({x} : Set ↥(pullback (C := Scheme.{u}) C.hom g)) →
          x ∉ (pullback.snd C.hom g).smoothLocus →
            IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) C.hom g) x) :
    ∃ (Y : Over (Spec (.of R))) (a : C ⟶ Y) (b : N ⟶ Y),
      IsHProjective Y.hom ∧ Flat Y.hom ∧
      ∃ hfp : LocallyOfFinitePresentation Y.hom,
      letI := hfp
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
        Nonempty ↥(pullback (C := Scheme.{u}) Y.hom g) ∧
        IsReduced (pullback (C := Scheme.{u}) Y.hom g) ∧
          (pullback (C := Scheme.{u}) Y.hom g).IsPureDimension 1 ∧
          ∀ x : ↥(pullback (C := Scheme.{u}) Y.hom g),
          IsClosed ({x} : Set ↥(pullback (C := Scheme.{u}) Y.hom g)) →
            x ∉ (pullback.snd Y.hom g).smoothLocus →
              IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) Y.hom g) x) ∧
      IsFinite a.left ∧ Surjective a.left ∧ IsClosedImmersion b.left ∧
      IsPullback i.left j.left a.left b.left ∧
      (∃ (U : C.left.Opens) (V : Y.left.Opens) (e : U.toScheme ≅ V.toScheme),
        (U : Set C.left) = (Set.range i.left)ᶜ ∧
        (V : Set Y.left) = (Set.range b.left)ᶜ ∧
        e.hom ≫ V.ι = U.ι ≫ a.left) ∧
      (let F := Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
       IsPushout (F.map i).left (F.map j).left (F.map a).left (F.map b).left) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
        let F := Over.pullback g
        IsPushout (F.map i).left (F.map j).left (F.map a).left (F.map b).left) ∧
      ∃ hs : IsPushout i.left j.left a.left b.left,
        let iY : Over.mk (i.left ≫ a.left) ⟶ Over.mk a.left := Over.homMk i.left rfl
        let jY : Over.mk (i.left ≫ a.left) ⟶ Over.mk b.left := Over.homMk j.left hs.w.symm
        ∀ V : Y.left.Opens,
          let F := Over.pullback V.ι
          IsPushout (F.map iY).left (F.map jY).left
            (pullback.snd a.left V.ι) (pullback.snd b.left V.ι) := by
  sorry

end AlgebraicGeometry
