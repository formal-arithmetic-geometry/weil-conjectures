/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.Blowup.FlatBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Blowup.Complement

/-! # Regularization of a nodal family over a discrete valuation ring

Source: Stacks Project, models.tex, Tag 0CDE, with the charts of Tag 0CDC
(blueprint: lem-sfb-nodal-trait-regularization).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective nodal family over a DVR with smooth generic fibre admits a finite
sequence of blowups at reduced nonregular closed special-fibre points, ending in a
regular scheme. Fibres of the intermediate families may be disconnected. The maps
`p` and their compatibility equations identify the composite of the displayed arrows.
The finite clopen partition describes the terminal scheme as integral regular surfaces.

Source: Stacks Project, models.tex, Tag 0CDE, with Tag 0CDC; Properties Tags 033M
and 04MU and Algebra Tag 00PD for the terminal component and DVR conclusions.
(blueprint: lem-sfb-nodal-trait-regularization).

Proof, following the twelve steps of the DAG node:

1. The DVR $R$ is Noetherian. Finite presentation gives finite type by forgetting the relations in
   each finite algebra presentation. Hence $X$ is Noetherian by [lem-weil-pbc-finite-type-over-
   noetherian]. The first-Fitting singular subscheme $N$ of [lem-trf-nodal-family-fitting-
   singular] is closed and has exactly the nonsmooth locus as underlying set. Its generic fibre is
   empty by smoothness of $X_K$ and the base-change clause of that lemma. Its special fibre is
   unramified by [lem-weil-pbc-unramified-base-change-open], so [lem-trf-unramified-field-fibre-
   decomposition] makes it a disjoint union of spectra of finite separable extensions of $k$. This
   union is finite: $N$ is a closed subspace of the quasi-compact space $X$, is supported in
   $X_k$, and the one-point open components of the disjoint union cover it. Thus the nonsmooth
   points form a finite set of closed special-fibre points. This argument needs no connectedness
   of any fibre.

2. At any nonsmooth special-fibre point $x$, apply [lem-sfb-trait-nodal-etale-dvr-model] to obtain
   $(U,u)\to(X,x)$ and $(U,u)\to(W,w)$ over $S$, with $W$ one of the two displayed models over
   $R'$. The zero-parameter model cannot occur at $u$: its nodal section $a=b=0$ has generic point
   specializing to $w=(\pi,a,b)$. The image in $W$ of any open neighbourhood of $u$ is open by
   [def-weil-etale-morphism, lem-weil-pbc-flat-lfp-open], so contains that generic point. Thus
   $U_K$ would have a point etale over the origin of $K'[a,b]/(ab)$, a nonsmooth node. The
   pointwise equivalence of smoothness in [lem-trf-etale-source-smoothness], applied to both etale
   maps, contradicts smoothness of $X_K$. Consequently we have the model $ab=\pi^n$, with $n\geq1$
   since $x$ is nonsmooth. Here $w$ is its origin: outside $a=b=0$ the equation eliminates the
   other variable and is smooth. This conclusion is also exactly the smooth-generic clause of
   [lem-sfb-trait-nodal-etale-dvr-model], which supplies at the nonsmooth point $x$ a diagram
   whose model is $ab=\pi^n$ with $n\geq1$; the argument above only explains why that clause
   holds.

3. Apply [lem-sfb-dvr-nodal-chart-blowup-calculus] to these pointed models, using its stated
   invariance under a common pointed etale neighbourhood. A point of $X$ outside the nonsmooth
   locus has a smooth $R$-neighbourhood of pure relative dimension one, so is regular. At a
   nonsmooth point with model $ab=\pi^n$, regularity holds exactly for $n=1$. Thus all nonregular
   points lie in the finite set of step 1, and a nonregular point has $n\geq2$. Also every local
   ring of $X$ has dimension at most two and every closed point of $X_k$ has local dimension two,
   by the smooth-case and model-case assertions of that same node. These conclusions apply equally
   to every later nodal family with smooth generic fibre.

4. Choose a nonregular $x$ and the diagram of step 2, with $n\geq2$. Shrink $U$ about $u$ so that
   $u$ is the sole point over $x$ and the sole point over the origin $w$ of $W$. To justify this
   shrinking, first choose an affine neighbourhood of $x$ in $X$ and an affine neighbourhood of
   $u$ mapping into it. Both targets (this affine open and $W$) are affine, hence quasi-separated,
   so the two fibres are quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence] and are disjoint
   unions of spectra of separable fields by [def-weil-etale-morphism, lem-weil-pbc-unramified-
   base-change-open, lem-trf-unramified-field-fibre-decomposition]. Hence they are finite reduced
   sets of closed points, and deleting the other points does the job. Both scheme-theoretic
   inverse images of the reduced centres are then precisely the reduced point $u$. Let
   $X^+=\operatorname{Bl}_xX$, $U^+=\operatorname{Bl}_uU$, and $W^+=\operatorname{Bl}_wW$. By
   [thm-nagata-blowup-flat-base-change] for the comparison of [def-nagata-blowup-flat-base-change-
   map], both squares with common upper-left object $U^+$ are Cartesian. Their horizontal maps
   remain etale by [lem-weil-pbc-etale-scheme-base-change].

5. The three charts of $W^+$ are those in [lem-sfb-dvr-nodal-chart-blowup-calculus]: the two outer
   charts have equations $at=\pi$ and $bt'=\pi$, and the middle chart has $rs=\pi^{n-2}$. They
   have nodal geometric fibres over $R'$. They are nodal over $R$ as well: the image of the fixed
   uniformizer of $R$ is a uniformizer of $R'$ (step 2), so each displayed chart is the etale base
   change of the identical chart over $R$; apply [lem-weil-pbc-etale-scheme-base-change] and the
   forward direction of [lem-trf-nodal-family-etale-source-locality]. The map $U^+\to X^+$ covers
   every point above $x$, since it is the base change of $U\to X$ and its fibre above $x$ contains
   $\operatorname{Spec}\kappa(u)\to\operatorname{Spec}\kappa(x)$. Together with the open
   complement of that fibre these maps are an etale cover. Away from $x$ the blowup is an
   isomorphism by [thm-nagata-global-blowup-complement]. The reverse direction of [lem-trf-nodal-
   family-etale-source-locality] therefore proves $X^+\to S$ flat and locally finitely presented,
   with nodal geometric fibres.

6. For $n=2$ the middle chart is $rs=1$ and is regular; for $n=3$ it is $rs=\pi$ and is regular
   too. If $n\geq4$, the only nonregular point of $W^+$ is the middle origin with local equation
   $rs=\pi^{n-2}$, and its residue field equals that of $w$, by [lem-sfb-dvr-nodal-chart-blowup-
   calculus]. Over the single point $u$, its inverse image in $U^+$ is consequently a single point
   with residue field $\kappa(u)$: the Cartesian square makes that fibre the base change of this
   rational point. All other points of $U^+$ above $u$ are regular by the same node. The common
   pointed etale criterion in that node and surjectivity above $x$ then show that $X^+$ has
   exactly one nonregular point above $x$ when $n\geq4$, and none when $n=2,3$. In the former case
   it has a common pointed etale neighbourhood with the model of exponent $n-2$. Away from $x$ no
   new nonregular point occurs.

7. The ideal of the reduced closed point is quasi-coherent and of finite type: on a Noetherian
   affine neighbourhood it is a finitely generated maximal ideal, and away from the point it is
   the unit ideal. By [lem-sfb-projective-affine-base-blowup], both $X^+\to X$ and $X^+\to S$ are
   H-projective. In particular they are proper by [lem-kun-projective-implies-proper]. Properness
   supplies finite type and hence quasi-compactness by [def-weil-proper-morphism, def-weil-finite-
   type-morphism]; separatedness gives quasi-separatedness by [lem-pc-separated-quasi-separated];
   with the local finite presentation from step 5 this is finite presentation by [def-sbc-locally-
   finite-presentation]. The finite-type-over-Noetherian conclusion of [lem-weil-pbc-finite-type-
   over-noetherian] also makes $X^+$ Noetherian, so these hypotheses persist at every subsequent
   step.

8. Off the centre, every fibre of $X^+\to X$ is a point. Over the centre, base change to
   $\kappa(u)$ identifies the exceptional fibre with the exceptional fibre of $W^+$ after the
   corresponding residue extension, by the Cartesian squares in step 4. By [lem-sfb-dvr-nodal-
   chart-blowup-calculus] its geometric fibre is a projective line for $n=2$, or two projective
   lines meeting at one point for $n>2$. Either is nonempty and connected: each projective line is
   connected and the two have a common point. An algebraic closure of $\kappa(x)$ contains an
   embedding of the finite separable extension $\kappa(u)$, so this computes the geometric fibre
   of $X^+\to X$ itself. For an arbitrary field extension $k'/\kappa(x)$, connectedness of the
   fibre after base change to $k'$ then follows from connectedness after base change to an
   algebraically closed extension, by [lem-weil-geometrically-connected-algebraic-closure]; a
   fibre $\operatorname{Spec}\kappa(y)$ off the centre stays one point after any field extension.
   Thus the morphism has nonempty geometrically connected fibres everywhere. In particular it is
   surjective, and the nonemptiness of all geometric fibres of the family over $S$ is preserved.

9. Fix a nonregular point with chosen exponent $n\geq2$. Induct on $\lfloor n/2\rfloor$ to remove
   it and its descendants. For $n=2$ or $3$, steps 4--8 give one permissible blowup and no
   nonregular point over it. For $n\geq4$ they give exactly one remaining nonregular point, with
   pointed exponent $n-2$; repeat the construction there and use the inductive hypothesis, since
   $\lfloor(n-2)/2\rfloor=\lfloor n/2\rfloor-1$. The same pointed diagram pulls back at each
   repetition after the shrinking of step 4. Thus at most $\lfloor n/2\rfloor$ blowups remove the
   selected point without changing any other original nonregular point. Now induct on the finite
   number of nonregular points of step 3. Zero points requires zero blowups; otherwise the
   preceding finite tower reduces their number by one and the outer induction applies. This gives
   a finite tower ending in a regular $T$. Projectivity, flatness, finite presentation, nodality,
   nonemptiness and the fibre properties follow at each arrow from steps 5, 7 and 8.

10. All chosen centres are nonregular points, hence special-fibre points by step 3. Each blowup is
   an isomorphism off its centre by [thm-nagata-global-blowup-complement], so the composite is an
   isomorphism on the generic fibre. It is also an isomorphism over the original relative smooth
   locus: initially that locus is regular by step 3; inductively its inverse image is still
   isomorphic to it and hence regular, so no subsequent nonregular centre lies there. This proves
   both isomorphism clauses without assuming that all special-fibre nodes must be blown up.

11. By [rem-pc-regular-normal], the regular Noetherian scheme $T$ is a finite disjoint union of
   integral normal open-and-closed components $T_i$; each is regular because its local rings are
   local rings of $T$. The dimension bounds of step 3 apply to $T$: all local dimensions are at
   most two, and closed points of $T_k$ have dimension two. Every $T_i$ meets the generic fibre:
   if it did not, its nonzero integral local rings would have $\pi=0$, contradicting flatness over
   $R$. Here multiplication by the nonzero element $\pi$ is injective after tensoring $0\to
   R\xrightarrow{\pi}R$ with a flat local ring, using the injectivity definition in [def-weil-pbc-
   flat-ring-map]. Since $T\to S$ is proper, the image of the closed subset $T_i$ is closed by
   [def-weil-proper-morphism]. It contains the generic point, so also the closed point of $S$.
   Choose a closed point in the nonempty Noetherian special fibre of $T_i$. Its local dimension is
   two. The equality between scheme dimension and the supremum of local dimensions in [lem-pc-
   scheme-dimension-local-rings] now gives $\dim T_i=2$. Thus these components are precisely
   integral regular surfaces.

12. Let $\xi$ be the generic point of a special-fibre component of $T$. The reduced nodal special
   fibre has field local ring at its generic point. Consequently, for $A=\mathcal O_{T,\xi}$, the
   quotient $A/\pi A=\mathcal O_{T_k,\xi}$ is a field, so its maximal ideal is $(\pi)$. The ring
   $A$ is a Noetherian local domain by regularity and [rem-pc-regular-normal]. Flatness makes
   $\pi$ nonzero in $A$, by the injectivity argument of step 11. Hence [lem-sc-principal-ideal-
   dvr] applies and makes $A$ a DVR. No excellence or completion of $R$ was used anywhere.
-/
theorem exists_nodal_trait_regularization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
      Nonempty ↥(pullback f g) ∧ IsReduced (pullback f g) ∧
        (pullback f g).IsPureDimension 1)
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)) (x : ↥(pullback f g)),
      IsClosed ({x} : Set ↥(pullback f g)) →
      x ∉ (pullback.snd f g).smoothLocus →
        Nonempty
          (AdicCompletion (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk x))
            ((pullback f g).presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))) :
    ∃ (m : ℕ) (Y : Fin (m + 1) → Scheme.{u})
      (e₀ : Y 0 ≅ X) (b : ∀ j : Fin m, Y j.succ ⟶ Y j.castSucc)
      (p : ∀ j : Fin (m + 1), Y j ⟶ X),
      p 0 = e₀.hom ∧
      (∀ j : Fin m, p j.succ = b j ≫ p j.castSucc) ∧
      (∀ j : Fin m,
        ∃ (x : Y j.castSucc) (hx : IsClosed ({x} : Set (Y j.castSucc)))
          (e : Y j.succ ≅ (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowup),
          e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap = b j ∧
          ¬ IsRegularLocalRing ((Y j.castSucc).presheaf.stalk x) ∧
          (p j.castSucc ≫ f) x = IsLocalRing.closedPoint R) ∧
      (∀ j : Fin m, IsProper (b j) ∧ GeometricallyConnected (b j)) ∧
      (∀ j : Fin (m + 1),
        IsHProjective (p j ≫ f) ∧ Flat (p j ≫ f) ∧
          LocallyOfFinitePresentation (p j ≫ f) ∧
            QuasiCompact (p j ≫ f) ∧ QuasiSeparated (p j ≫ f) ∧
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (g : Spec (.of Ω) ⟶ Spec (.of R)),
              Nonempty ↥(pullback (p j ≫ f) g) ∧ IsReduced (pullback (p j ≫ f) g) ∧
              (pullback (p j ≫ f) g).IsPureDimension 1 ∧
              ∀ x : ↥(pullback (p j ≫ f) g),
                IsClosed ({x} : Set ↥(pullback (p j ≫ f) g)) →
                (¬ ∃ V : (pullback (p j ≫ f) g).Opens,
                  x ∈ V ∧ Smooth (V.ι ≫ pullback.snd (p j ≫ f) g)) →
                Nonempty
                  (AdicCompletion
                    (IsLocalRing.maximalIdeal ((pullback (p j ≫ f) g).presheaf.stalk x))
                    ((pullback (p j ≫ f) g).presheaf.stalk x) ≃+*
                    (MvPowerSeries (Fin 2) Ω ⧸
                      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))) ∧
      IsRegularScheme (Y (Fin.last m)) ∧
      IsIso (pullback.snd (p (Fin.last m))
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) ∧
      IsIso (p (Fin.last m) ∣_ f.smoothLocus) ∧
      (∃ (n : ℕ) (U : Fin n → (Y (Fin.last m)).Opens),
        (∀ i : Fin n, IsClosed (U i : Set (Y (Fin.last m)))) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (U i) (U j)) ∧
        (⨆ i : Fin n, U i) = ⊤ ∧
        ∀ i : Fin n, IsIntegral (U i).toScheme ∧ IsRegularScheme (U i).toScheme ∧
          topologicalKrullDim ↥((U i).toScheme) = 2) ∧
      ∀ Z : Set ↥((p (Fin.last m) ≫ f).fiber (IsLocalRing.closedPoint R)),
        Z ∈ irreducibleComponents ↥((p (Fin.last m) ≫ f).fiber (IsLocalRing.closedPoint R)) →
        ∀ ξ : (p (Fin.last m) ≫ f).fiber (IsLocalRing.closedPoint R),
          IsGenericPoint ξ Z →
          ∃ hdomain : IsDomain
            ((Y (Fin.last m)).presheaf.stalk
              ((p (Fin.last m) ≫ f).fiberι (IsLocalRing.closedPoint R) ξ)),
            @IsDiscreteValuationRing
              ((Y (Fin.last m)).presheaf.stalk
                ((p (Fin.last m) ≫ f).fiberι (IsLocalRing.closedPoint R) ξ))
              inferInstance hdomain := by
  sorry

end AlgebraicGeometry
