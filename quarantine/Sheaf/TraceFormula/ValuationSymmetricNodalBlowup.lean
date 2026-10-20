/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.Paper.OrgogozoInductionData
public import Sheaf.TraceFormula.StrictSemistableCurve
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.Blowup.Affine.Defs
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.RingTheory.ValuationRingNormal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleFiniteNeighbourhoods
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedOnePointClosed
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Mathlib.RingTheory.Kaehler.Basic
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.FieldTheory.ValueGroupDivisible
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.FiniteDegree.Algebra
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion
import Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced

public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Symmetric blowup of the closure of a node

Source: Temkin, Stable modification of relative curves, Remark 4.5.2 and §4.3,
Proposition 4.3.1; the DAG reconstructs the symmetric version using Stacks Tag 0CBY.
(blueprint: lem-trf-valuation-symmetric-nodal-blowup).

The auxiliary data retain the three actual subalgebra charts, their coordinates,
the intrinsic centre, and the étale comparison over each chart source.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The constant in a nodal model algebra. Source: Temkin §4.3, Proposition 4.3.1
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def symmetricNodalConstant (R : CommRingCat.{u}) (a c : R) : strictNodalRing R a :=
  Ideal.Quotient.mk _ (MvPolynomial.C c)

/-- One of the two coordinates of the nodal model. Source: Temkin §4.3, Proposition 4.3.1
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def symmetricNodalCoordinate (R : CommRingCat.{u}) (a : R) (i : Fin 2) :
    strictNodalRing R a :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The ideal `(u,v)` in the nodal model. Source: Stacks Tag 0CBY and the differential
presentation in the node's proof, Step 4
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def symmetricNodalSingularIdeal (R : CommRingCat.{u}) (a : R) :
    Ideal (strictNodalRing R a) :=
  Ideal.span {symmetricNodalCoordinate R a 0, symmetricNodalCoordinate R a 1}

/-- The symmetric model centre `(u,v,π)`. Source: Temkin §4.3, symmetric reconstruction
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def symmetricNodalCentre (R : CommRingCat.{u}) (a π : R) :
    Ideal (strictNodalRing R a) :=
  symmetricNodalSingularIdeal R a ⊔ Ideal.span {symmetricNodalConstant R a π}

/-- The ideal sheaf associated to an ideal on an affine spectrum, with the canonical
identification of its global sections. Source: Stacks Tag 01IN, used in the local model
of Temkin §4.3 (blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def symmetricNodalAffineIdeal (A : CommRingCat.{u}) (I : Ideal A) :
    (Spec A).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso A).inv.hom)

/-- The open complement of the whole closure of the chosen node. Source: the DAG's
reconstruction of Temkin Remark 4.5.2, Steps 2 and 6
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def symmetricNodalComplement (X : Scheme.{u}) (z : X) : X.Opens :=
  ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩

/-- The three chart algebras and their maps to the original nodal model. The order of
coordinates is `(u,p)`, `(r,t)`, `(v,h)`. Each isomorphism is to the actual subalgebra
`A[I/g]`, so the assertion includes saturation, not merely a presentation with torsion.
The equations for constants make the isomorphisms isomorphisms over `R`.
Source: Temkin §4.3, Proposition 4.3.1, symmetric calculation in node Steps 9--10
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
def SymmetricNodalChartRings (R : CommRingCat.{u}) (a π b : R) : Prop :=
  ∃ (e₀ : strictNodalRing R π ≃+*
        AffineBlowup.chartRing (symmetricNodalCentre R a π)
          (symmetricNodalCoordinate R a 0))
    (e₁ : strictNodalRing R b ≃+*
        AffineBlowup.chartRing (symmetricNodalCentre R a π)
          (symmetricNodalConstant R a π))
    (e₂ : strictNodalRing R π ≃+*
        AffineBlowup.chartRing (symmetricNodalCentre R a π)
          (symmetricNodalCoordinate R a 1)),
    (∀ c : R,
      e₀ (symmetricNodalConstant R π c) =
        algebraMap (strictNodalRing R a) _ (symmetricNodalConstant R a c)) ∧
    (∀ c : R,
      e₁ (symmetricNodalConstant R b c) =
        algebraMap (strictNodalRing R a) _ (symmetricNodalConstant R a c)) ∧
    (∀ c : R,
      e₂ (symmetricNodalConstant R π c) =
        algebraMap (strictNodalRing R a) _ (symmetricNodalConstant R a c)) ∧
    e₀ (symmetricNodalCoordinate R π 0) =
      algebraMap (strictNodalRing R a) _ (symmetricNodalCoordinate R a 0) ∧
    algebraMap (strictNodalRing R a) _ (symmetricNodalCoordinate R a 1) =
      e₀ (symmetricNodalConstant R π (π * b) * symmetricNodalCoordinate R π 1) ∧
    algebraMap (strictNodalRing R a) _ (symmetricNodalCoordinate R a 0) =
      e₁ (symmetricNodalConstant R b π * symmetricNodalCoordinate R b 0) ∧
    algebraMap (strictNodalRing R a) _ (symmetricNodalCoordinate R a 1) =
      e₁ (symmetricNodalConstant R b π * symmetricNodalCoordinate R b 1) ∧
    e₂ (symmetricNodalCoordinate R π 0) =
      algebraMap (strictNodalRing R a) _ (symmetricNodalCoordinate R a 1) ∧
    algebraMap (strictNodalRing R a) _ (symmetricNodalCoordinate R a 0) =
      e₂ (symmetricNodalConstant R π (π * b) * symmetricNodalCoordinate R π 1)

/-- One affine member of the neighbourhood cover, its localized valuation base, its
étale nodal cover, the intrinsic Fitting ideal identity, the flat blowup comparison,
and the three standard model chart calculations.
Source: Stacks Tag 0CBY; Temkin §4.3, symmetric reconstruction in node Steps 3--10
(blueprint: lem-trf-valuation-symmetric-nodal-blowup). -/
structure SymmetricNodalLocalChart {K : Type u} [Field K] (V : ValuationSubring K)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of V)) [LocallyOfFinitePresentation f]
    (π : V) (I : X.IdealSheafData) (U : X.Opens) where
  affine : IsAffineOpen U
  R : CommRingCat.{u}
  scalar : V →+* R
  denominators : Submonoid V
  localization : @IsLocalization V _ denominators R _ scalar.toAlgebra
  baseOpen : (Spec (.of V)).Opens
  baseAffine : IsAffineOpen baseOpen
  baseIso : Spec R ≅ baseOpen.toScheme
  baseMap : baseIso.hom ≫ baseOpen.ι = Spec.map (CommRingCat.ofHom scalar)
  toBase : U.toScheme ⟶ Spec R
  overBase : toBase ≫ Spec.map (CommRingCat.ofHom scalar) = U.ι ≫ f
  a : R
  a_ne_zero : a ≠ 0
  b : R
  division : a = scalar π ^ 2 * b
  T : Scheme.{u}
  cover : T ⟶ U.toScheme
  cover_etale : Etale cover
  cover_surjective : Surjective cover
  modelMap : T ⟶ (StrictSemistableModel.nodal a).scheme
  model_etale : Etale modelMap
  model_over : modelMap ≫ (StrictSemistableModel.nodal a).baseMap = cover ≫ toBase
  fitting : (Scheme.firstFittingIdealSheaf f).comap (cover ≫ U.ι) =
    (symmetricNodalAffineIdeal (.of (strictNodalRing R a))
      (symmetricNodalSingularIdeal R a)).comap modelMap
  comparison : Nonempty
    (Over.mk (pullback.snd I.blowupMap (cover ≫ U.ι)) ≅
      Over.mk (pullback.snd (AffineBlowup.toSpec (symmetricNodalCentre R a (scalar π)))
        modelMap))
  charts : SymmetricNodalChartRings R a (scalar π) b

/-- Symmetric blowup along the whole closure of one nodal point, with its local
coordinate formulas and smooth reduced fibre components above the centre.

Source: Temkin Remark 4.5.2 and §4.3, Proposition 4.3.1; agent reconstruction using
Stacks Tag 0CBY (blueprint: lem-trf-valuation-symmetric-nodal-blowup).

Proof plan (the fifteen steps of the DAG node):
1. By the nodal Fitting theorem, $N$ is the closed nonsmooth locus and $N\to S$ is unramified;
   hence $C\subseteq|N|$ and $s_0\ne\eta$. The valuation ring and its localizations are normal
   domains. Apply 09Z9 to $S$: after taking affine neighbourhoods in any etale base neighbourhood,
   their maps to $S$ split into open immersions. Moreover $N\to S$ is locally on $N$ a closed
   immersion into an open of $S$. Indeed apply the finite-unramified-neighbourhood theorem to one
   point, replace its etale base by an open-immersion component containing the marked base point,
   and apply 04DG to its finite unramified piece with unique purely inseparable fibre point. Its
   open piece contains the original point. Thus every point of $N$ has an open neighbourhood in
   $N$ whose map to $S$ is injective, induces residue-field isomorphisms, and reflects
   specialization.

   Inputs: lem-trf-nodal-family-fitting-singular, lem-weil-pbc-valuation-ring-normal, sbc-lem-
   etale-over-normal, lem-weil-pbc-unramified-etale-finite-neighbourhoods, lem-weil-pbc-finite-
   unramified-one-point-closed

2. Put $F=|N|\cap f^{-1}(\overline{\{s_0\}})$. This is a finite closed subset of $X$. If $c\in C$
   and $w\in F$ generalizes $c$, take the local immersion neighbourhood of $c$ obtained in step 1.
   It contains both $z$ and $w$. Their base points satisfy $s_0\leadsto f(w)$, since $f(w)$ is a
   specialization of $s_0$. A locally closed subspace reflects specialization, so $z\leadsto w$
   and $w\in C$. Thus $C$ is both specialization-closed and generalization-closed in $F$. For
   every $w\in F\setminus C$, its closure in $X$ is contained in $F$ and misses $C$. Delete the
   union of these finitely many closures from $X$, obtaining an open $W^0$ containing all of $C$
   with $F\cap W^0=C$. This uses no separatedness of $X$.

   Elementary step.

3. For every $c\in C$, apply 0CBY to $X/S$ at $c$. Its flatness, local finite presentation, pure
   dimension and geometric-node hypotheses are exactly the assumptions here. Restrict its etale
   base neighbourhood to an affine open and then to the component through the chosen point
   furnished by step 1; this is an open of $S$. Shrink it to $S_c=\operatorname{Spec}V_{f(c)}$.
   This is an open because the prime chain is finite: the set of primes contained in $f(c)$ is the
   complement of the closed set starting at the next prime. The etale source chart still contains
   a point over $c$. Its image in $X$ is open, by openness of flat locally finitely presented
   maps. Choose an affine open $W_c$ containing $c$ inside that image, inside $W^0$, and mapping
   into $S_c$. Its preimage $T_c$ in the chart is an etale surjective cover of $W_c$, with an
   etale $S_c$-map to $M_c=\operatorname{Spec}R_c[u,v]/(uv-a_c)$. Keep one such choice for each of
   the finitely many $c$. Set $W=\bigcup_c W_c$. Every $W_c$ contains $z$, because $z$ generalizes
   $c$.

   Inputs: lem-trf-nodal-family-etale-local-model, sbc-lem-etale-over-normal, lem-weil-pbc-flat-
   lfp-open, def-weil-etale-morphism

4. On $M_c$ the universal derivation gives $\Omega_{M_c/R_c}=(A\,du\oplus A\,dv)/(v\,du+u\,dv)$: a
   derivation is precisely a pair satisfying this relation. The first minors of this presentation
   generate $(u,v)$. The affine etale criterion gives $H_1(L)=0$ and $\Omega=0$ for each etale
   chart map. Thus the formally-etale differential equivalence, followed by Fitting base change,
   identifies both pullbacks to $T_c$. Thus $J\mathcal O_{T_c}=(u,v)\mathcal O_{T_c}$. In
   particular, a lift of $z$ shows that $a_c$ vanishes at $s_0$. Also $a_c\ne0$. Otherwise the
   image of $T_c\to M_c$ is an open containing a point of the node section $u=v=0$, and therefore
   contains its generic point over $S_c$. A point of $T_{c,\eta}$ above that generic node has
   nonunit first Fitting ideal by this calculation. But $T_{c,\eta}\to X_\eta$ is etale and
   $X_\eta$ is smooth, whose first Fitting ideal is the unit ideal by the nodal Fitting theorem.
   This is a contradiction.

   Inputs: def-weil-pbc-kahler-differentials, lem-weil-pbc-etale-ring-map-iff-etale-affine, lem-
   trf-formally-etale-differentials-base-change, lem-trf-fitting-ideal-independence-base-change,
   lem-trf-nodal-family-fitting-singular, lem-weil-pbc-flat-lfp-open

5. Write $\mathfrak p_0$ for $s_0$, and let $\mathfrak p_-$ be the immediately preceding prime,
   which exists because $\mathfrak p_0\ne0$. Choose $d\in\mathfrak p_0\setminus\mathfrak p_-$.
   Each $a_c\in V_{f(c)}$ actually lies in $\mathfrak p_0\subset V$: write $a_c=n/e$ with $e\notin
   f(c)\supseteq\mathfrak p_0$ and $n\in\mathfrak p_0$. If $n/e\notin V$, its inverse lies in $V$,
   forcing $e\in\mathfrak p_0$, a contradiction; primality then gives $n/e\in\mathfrak p_0$. In
   additive valuation notation choose $\gamma=\min(v(d),v(a_c):c\in C)$. It is achieved by an
   element $d_0\in\mathfrak p_0\setminus\mathfrak p_-$: a member of $\mathfrak p_-$ cannot have
   value at most $v(d)$. Divisibility of the value group gives $\pi\in K^\times$ with
   $3v(\pi)=\gamma$. Then $\pi\in V$ and $\pi^3/d_0$ is a unit of $V$, so
   $\sqrt{(\pi)}=\sqrt{(d_0)}=\mathfrak p_0$, since no smaller prime contains $d_0$. Finally
   $v(a_c/\pi^2)\ge\gamma/3=v(\pi)$, so $b_c=a_c/\pi^2\in(\pi)V\subseteq\mathfrak p_0$. This
   stronger choice makes every $b_c$ vanish on $\overline{\{s_0\}}$.

   Inputs: lem-trf-separably-closed-value-group-divisible

6. By step 2 and $V_S(\pi)=\overline{\{s_0\}}$, the support of $\mathcal O_W/(J+(\pi))$ is
   precisely $C$. Thus $J+(\pi)$ is the unit ideal on $W\setminus C$ and glues with the unit ideal
   on $X\setminus C$. This constructs $I$ by equality of sheaves on the overlap. It is quasi-
   coherent because the Fitting ideals commute with localization, and finite type: locally write a
   finite presentation $B=R[x_1,\ldots,x_n]/(g_1,\ldots,g_m)$ of $X/S$; its differential module
   has the finite presentation with generators $dx_i$ and the $m$ relations $dg_j$, so its first
   Fitting ideal has finitely many minors. Adjoining the generator $\pi$ preserves finite
   generation. Hence $I$ is a finite-type quasi-coherent ideal without any Noetherian assumption.

   Inputs: def-trf-first-fitting-singular-subscheme, def-weil-pbc-kahler-differentials, def-sbc-
   locally-finite-presentation, lem-trf-fitting-ideal-independence-base-change

7. Form $q=\operatorname{Bl}_I X\to X$. The global finite-type blowup theorem makes $q$ proper.
   Its complement theorem, applied to $V(I)=C$, makes $q$ an isomorphism over $X\setminus C$.
   Since $C$ misses $X_\eta$, this includes the whole generic fibre. For any closed subscheme
   $E\hookrightarrow X$ whose underlying set misses $C$, the morphism factors through the open
   $X\setminus C$; base change of that restricted isomorphism gives $q^{-1}(E)\simeq E$, with its
   full scheme structure.

   Inputs: thm-nagata-global-blowup-proper, thm-nagata-global-blowup-complement

8. Etale maps are flat. Apply the flat blowup comparison to $T_c\to W_c$ and to $T_c\to M_c$. The
   extended ideals on $T_c$ coincide, both being $(u,v,\pi)$ by step 4. Thus $X^+\times_XT_c$
   identifies with $T_c\times_{M_c}\operatorname{Bl}_{(u,v,\pi)}M_c$. These are flat base changes,
   not blowup base change along a residue field. The affine-chart-cover theorem gives, for every
   affine presentation of $I$, the asserted cover by $A[I/g]\subseteq A_g$. In particular the
   model blowup is covered by the $u$, $\pi$ and $v$ charts.

   Inputs: def-weil-etale-morphism, def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-
   flat-base-change, prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring

9. Fix a chart and omit its subscript. The domain $A=R[u,v]/(uv-a)$ embeds in
   $\operatorname{Frac}(R)[u,u^{-1}]$ via $v=a/u$, since every class has a unique normal form
   $c_0+\sum_{i>0}c_i u^i+\sum_{j>0}d_jv^j$; independence follows from distinct Laurent exponents
   and $a\ne0$. In $A_u$ set $p=\pi/u$. Then $v=\pi bp$ and $v/u=bp^2$, so the subalgebra
   generated by $A,v/u,\pi/u$ is generated by $u,p$ with relation $up=\pi$. The same normal-form
   argument, now with nonzero $\pi$, proves injectivity of $R[u,p]/(up-\pi)\to A_u$ and therefore
   identifies this ring with the actual $u$ blowup chart. Interchanging $u,v$ gives
   $R[v,h]/(vh-\pi)$ with $h=\pi/v$ and $u=\pi bh$. These are the subalgebra charts, so there is
   no extra torsion or exceptional component from an unsaturated presentation.

   Inputs: def-nagata-blowup-chart-ring

10. In $A_\pi$ set $r=u/\pi$, $t=v/\pi$. They generate the $\pi$ chart and satisfy $rt=b$. The map
   $R[r,t]/(rt-b)\to A_\pi$, $r\mapsto u/\pi$, $t\mapsto v/\pi$, is injective by the normal-form
   argument of step 9 ($b=a/\pi^2\ne0$); after embedding in $\operatorname{Frac}(R)[u,u^{-1}]$,
   its distinct positive and negative powers cannot cancel. It is surjective onto the generated
   chart algebra, since $u=\pi r$ and $v=\pi t$. This proves all three displayed chart rings and
   all the claimed maps to $M$.

   Inputs: def-nagata-blowup-chart-ring

11. For each nonzero $e\in R$, the normal form in $R[x,y]/(xy-e)$ is the free $R$-basis
   $1,x,x^2,\ldots,y,y^2,\ldots$; hence it is flat and finitely presented over $R$. A geometric
   fibre is $\Omega[x,y]/(xy-\bar e)$. If $\bar e\ne0$ it is $\Omega[x,x^{-1}]$; if $\bar e=0$, it
   is the union of two affine lines, smooth off their intersection, with completed local ring
   $\Omega[[x,y]]/(xy)$ there (both rings have the same quotients modulo every power of $(x,y)$).
   It is pure one-dimensional in either case. Apply nodal source locality first to the etale
   pullbacks of these three models, and then to the jointly surjective etale cover of $X^+$
   consisting of those pullbacks and $X\setminus C$. On the latter open the original nodal family
   is unchanged. Thus $X^+\to S$ is flat, locally finitely presented, and has pure one-dimensional
   geometric nodal fibres.

   Inputs: lem-trf-nodal-family-etale-source-locality, def-weil-pbc-flat-ring-map

12. The proper morphism $q$ is quasi-compact and quasi-separated; together with finite
   presentation of $X/S$, the qcqs permanence statements make $X^+/S$ quasi-compact and quasi-
   separated. Combined with local finite presentation from step 11, this is finite presentation.
   For reducedness take a local ring $B$ of $X^+$. Flatness over its base valuation ring implies
   $B\hookrightarrow B\otimes_VK$: tensor the injections given by multiplication by each nonzero
   scalar, then localize. Its generic localization is reduced because $X^+_\eta\simeq X_\eta$ is
   smooth over a field and hence geometrically reduced. A nilpotent of $B$ therefore maps to zero
   in that localization and was already zero. This proves $X^+$ reduced, including away from the
   chosen charts.

   Inputs: def-weil-proper-morphism, lem-weil-pbc-qcqs-morphism-permanence, def-sbc-locally-
   finite-presentation, def-weil-pbc-flat-ring-map, sbc-lem-smooth-geometrically-reduced

13. Fix $s\in S$ and $x\in C\cap X_s$. Step 1 shows $\kappa(x)=\kappa(s)=k$: the local immersion
   of $N$ into $S$ has this property. In particular $x$ is closed in $X_s$ (in every affine
   neighbourhood it is a $k$-rational maximal ideal). The residue-field theorem also says $k$ is
   separably closed. Choose a chart lift $t\in T_c$ of $x$; its residue extension is finite
   separable, so it is $k$. The image in $M_c$ is its rational node $u=v=0$. Base change the
   isomorphism of schemes in step 8 further along $\operatorname{Spec}k\to T_c$. It identifies the
   entire fibre $q^{-1}(x)$ with the fibre of the computed model blowup over its node. This is
   base change of an already proved isomorphism, and does not assert blowup commutes with the
   nonflat map to $k$. Here $\pi(s)=b_c(s)=0$ by step 5.

   Inputs: lem-trf-sepclosed-valuation-geometric-components, lem-trf-unramified-maximal-ideal-
   residue-criterion

14. In this model fibre the $u$ chart is $k[p]$ ($u=0$), the middle chart is $k[r,t]/(rt)$, and
   the $v$ chart is $k[h]$ ($v=0$). On the overlap of the $u$ and middle charts, $p=1/r$ and
   $t=0$; on the middle/$v$ overlap, $h=1/t$ and $r=0$. The $u$/$v$ overlap is empty in this
   fibre. Thus the fibre is exactly two copies $L_u,L_v$ of $\mathbf P^1_k$, meeting only at
   $r=t=0$. These are distinct closed integral curves in $(X^+)_s$, since the fibre over the
   closed point $x$ is closed. Every fibre is a pure one-dimensional finite-type $k$-scheme by
   step 11, so each $L_u,L_v$ is a whole irreducible component: otherwise a closed point of $L_u$,
   then $L_u$, then a larger irreducible component would give a chain of length two, contradicting
   dimension one (and similarly for $L_v$). This explicitly distinguishes the two global
   components through the middle node.

   Inputs: def-weil-irreducible-components

15. The other possible nonsmooth points above $x$ are the endpoints $u=p=0$ and $v=h=0$ in the
   outer charts. At the first, the branch $u=0$ lies in $L_u$, whereas the branch $p=0$ is not
   contracted: the coordinate $u$ is nonconstant on it and maps to the original branch $v=0$. An
   etale chart preserves that nonconstancy. Hence these branches lie in different global fibre
   components. The second endpoint is the same calculation with $u,v$ exchanged. At the middle
   node they lie in $L_u,L_v$, already distinguished in step 14. The nodal fibre is geometrically
   reduced by the nodal reducedness theorem, and the separably-closed residue-field theorem
   identifies its reduced components with geometrically integral components. Etale base change
   preserves the reducedness of a reduced component, by the etale-reducedness theorem.
   Consequently, in an etale node chart a fixed reduced global component has exactly one of the
   two local branches at each of these three nodes: locally its pullback is the quotient by that
   branch ideal, $k[u,p]/(up,u)=k[p]$ or $k[u,p]/(up,p)=k[u]$, and similarly in the middle and
   right charts. It is smooth there; etale source locality of smoothness descends this to the
   component itself. At all other points over $x$ the fibre is already smooth and has just one
   local component. This proves the component assertion for every $x\in C_s$ and every $s$, even
   when a component of the original fibre has a self-node.

   Inputs: lem-trf-nodal-geometric-fibres-reduced, lem-trf-sepclosed-valuation-geometric-
   components, lem-trf-etale-source-smoothness, etale-proposition-etale-reduced, lem-weil-pbc-
   etale-scheme-base-change
-/
theorem exists_valuation_symmetric_nodal_blowup
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] {X : Scheme.{u}} (f : X ⟶ Spec (.of V))
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hpure : ∀ s : Spec (.of V), (f.fiber s).IsPureDimension 1)
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of V)) (x : ↥(pullback (C := Scheme) f g)),
      (∃ U : (pullback f g).Opens, x ∈ U ∧ Smooth (U.ι ≫ pullback.snd f g)) ∨
        Orgogozo.IsOrdinaryDoublePoint (pullback.snd f g) x)
    (hgeneric : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom V.subtype))))
    (hfinite : (Set.range (Scheme.firstFittingSingularSubscheme f)).Finite)
    (z : X) (hz : z ∈ Set.range (Scheme.firstFittingSingularSubscheme f)) :
    closure ({z} : Set X) ⊆ Set.range (Scheme.firstFittingSingularSubscheme f) ∧
      ∃ (π : V) (W : X.Opens) (n : ℕ) (U : Fin n → X.Opens) (I : X.IdealSheafData),
        π ≠ 0 ∧ closure ({z} : Set X) ⊆ W ∧ (⨆ i, U i) = W ∧
        PrimeSpectrum.zeroLocus ({π} : Set V) = closure ({f z} : Set (Spec (.of V))) ∧
        Set.range (Scheme.firstFittingSingularSubscheme f) ∩ (W : Set X) ∩
          f ⁻¹' PrimeSpectrum.zeroLocus ({π} : Set V) = closure ({z} : Set X) ∧
        (∀ i, Nonempty (SymmetricNodalLocalChart V f π I (U i))) ∧
        I.comap W.ι =
          (Scheme.firstFittingIdealSheaf f ⊔
            (symmetricNodalAffineIdeal (.of V) (Ideal.span {π})).comap f).comap W.ι ∧
        I.comap (symmetricNodalComplement X z).ι = ⊤ ∧
        (∀ A : X.affineOpens, (I.ideal A).FG) ∧
        IsProper I.blowupMap ∧
        IsIso (pullback.snd I.blowupMap (symmetricNodalComplement X z).ι) ∧
        IsIso (pullback.snd I.blowupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom V.subtype)))) ∧
        IsReduced I.blowup ∧ Flat (I.blowupMap ≫ f) ∧
        LocallyOfFinitePresentation (I.blowupMap ≫ f) ∧
        QuasiCompact (I.blowupMap ≫ f) ∧ QuasiSeparated (I.blowupMap ≫ f) ∧
        (∀ s : Spec (.of V), ((I.blowupMap ≫ f).fiber s).IsPureDimension 1) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (g : Spec (.of Ω) ⟶ Spec (.of V))
          (x : ↥(pullback (C := Scheme) (I.blowupMap ≫ f) g)),
          (∃ B : (pullback (I.blowupMap ≫ f) g).Opens,
            x ∈ B ∧ Smooth (B.ι ≫ pullback.snd (I.blowupMap ≫ f) g)) ∨
              Orgogozo.IsOrdinaryDoublePoint (pullback.snd (I.blowupMap ≫ f) g) x) ∧
        (∀ (A : X.affineOpens) (m : ℕ) (g : Fin m → Γ(X, A))
          (_ : ∀ j, g j ∈ I.ideal A) (_ : Ideal.span (Set.range g) = I.ideal A),
          ∃ c : ∀ j, Spec (.of (AffineBlowup.chartRing (I.ideal A) (g j))) ⟶ I.blowup,
            (∀ j, IsOpenImmersion (c j) ∧
              c j ≫ I.blowupMap =
                Spec.map (CommRingCat.ofHom (algebraMap Γ(X, A)
                  (AffineBlowup.chartRing (I.ideal A) (g j)))) ≫ A.2.fromSpec) ∧
            (⋃ j, Set.range (c j)) = I.blowupMap ⁻¹' (A.1 : Set X)) ∧
        (∀ (s : Spec (.of V))
          (Z : TopologicalSpace.Closeds ((I.blowupMap ≫ f).fiber s)),
          (Z : Set ((I.blowupMap ≫ f).fiber s)) ∈
            irreducibleComponents ((I.blowupMap ≫ f).fiber s) →
          ∀ x : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
            I.blowupMap ((I.blowupMap ≫ f).fiberι s
              ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι x)) ∈
                closure ({z} : Set X) →
              ∃ B : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
                x ∈ B ∧ Smooth (B.ι ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
                  (I.blowupMap ≫ f).fiberToSpecResidueField s)) ∧
        (∀ (E : Scheme.{u}) (i : E ⟶ X) [IsClosedImmersion i],
          Disjoint (Set.range i) (closure ({z} : Set X)) →
            IsIso (pullback.snd I.blowupMap i)) := by
  sorry

end AlgebraicGeometry
