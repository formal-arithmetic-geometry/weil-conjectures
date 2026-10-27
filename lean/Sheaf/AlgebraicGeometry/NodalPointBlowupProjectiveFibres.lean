module

public import Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus
public import Sheaf.AlgebraicGeometry.SurfacePointBlowupData
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Blowup.Gluing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.BinomialBlowupChartAlgebras
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.Blowup.Complement
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Projectivity and fibres of an arithmetic nodal point blowup

Source: Stacks Project, models.tex, Tags 0CDC and 0CDE; divisors.tex, Tag 02NS.
(blueprint: lem-sfb-nodal-point-blowup-projective-fibres).

The nodal model and reduced closed-point ideal are the published constructions.
All identifications of exceptional curves are over the specified algebraic closure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SurfacePointBlowup

namespace AlgebraicGeometry

/-- Projectivity, finiteness and the full geometric-fibre description of the ordinary
blowup at an arithmetic nodal point. No splitting over the point's residue field is assumed.
Source: Stacks Project, models.tex, Tags 0CDC and 0CDE; divisors.tex, Tag 02NS.
(blueprint: lem-sfb-nodal-point-blowup-projective-fibres).

Proof plan from the DAG:
1. Let $\mathcal I$ be the ideal of the reduced closed point $x$. By
[def-sbc-closed-immersion-ideal-sheaf] it is quasi-coherent and on each affine open it is an
ordinary ideal. Since $X$ is locally Noetherian, each of these ideals is finitely generated, so
$\mathcal I$ is of finite type. The DVR $R$ is Noetherian by [def-sc-discrete-valuation-ring].
Apply [lem-sfb-projective-affine-base-blowup] to $A=R$, the given H-projective $f$, and $\mathcal
I$. Both $b$ and $g$ are H-projective. Apply [lem-kun-projective-implies-proper] to each to obtain
properness.

2. Properness includes finite type and separatedness by [def-weil-proper-morphism]. Thus $g$ is
quasi-compact and, by [lem-pc-separated-quasi-separated], quasi-separated. Together with the
assumed local finite presentation, the definition [def-sbc-locally-finite-presentation] gives
finite presentation. Flatness is already assumed. Since $S=\operatorname{Spec}R$ is Noetherian and
$g$ is finite type, [lem-weil-pbc-finite-type-over-noetherian] gives that $B$ is Noetherian.

3. Put $l=\kappa(x)$, $k_o=\kappa(o)=R\prime/(\pi)$ and $L=\kappa(u)$. The two etale maps have
discrete reduced fibres consisting of spectra of finite separable residue extensions by
[lem-weil-pbc-etale-fibre-discrete-separable-points]. Write $p:U\to X$ and $q:U\to M_n$. Since $x$
and $o$ are closed points, the fibres $p^{-1}(x)$ and $q^{-1}(o)$ are closed in $U$. Each is
discrete, so $\{u\}$ is open in it and $p^{-1}(x)\setminus\{u\}$, $q^{-1}(o)\setminus\{u\}$ are
closed in the fibre, hence closed in $U$. Remove these two closed sets from $U$; the restrictions
of $p$ and $q$ to this open neighbourhood of $u$ remain etale. On the resulting common
neighbourhood, both scheme-theoretic inverse images are exactly $\operatorname{Spec}L$. Etaleness
gives flatness by [def-weil-etale-morphism]. Apply [thm-nagata-blowup-flat-base-change] with its
comparison [def-nagata-blowup-flat-base-change-map] to both maps. Taking their fibres at $u$ gives
$E_x\times_l L\cong E_o\times_{k_o}L$, where $E_x=b^{-1}(x)$ and $E_o$ is the exceptional fibre of
the model point blowup. This uses the whole fibre via the Cartesian squares, not just an etale
cover of it.

4. Apply [lem-sfb-binomial-blowup-chart-algebras] with domain $R\prime$, nonzero element $\pi$ and
exponent $n$. Its extended-ideal quotients and overlap maps give a cover of $E_o$ by
$\operatorname{Spec}k_o[t]$, $\operatorname{Spec}k_o[r,s]/(rs-\epsilon)$ and
$\operatorname{Spec}k_o[h]$, with $\epsilon=1$ for $n=2$ and $0$ for $n>2$. For $n=2$ the middle
open is the common punctured affine line and $h=t^{-1}$. These are precisely the two standard
charts of $\mathbf P^1_{k_o}$ in [def-sc-p1-standard]. For $n>2$ the closed subschemes $s=0$ and
$r=0$ of the middle chart extend respectively across the first and third outer charts. The overlap
coordinates are $r=t^{-1}$ and $s=h^{-1}$; each closed subscheme is therefore $\mathbf P^1_{k_o}$.
They cover $E_o$ scheme-theoretically since $(r)\cap(s)=0$ in $k_o[r,s]/(rs)$, and their
scheme-theoretic intersection is $\operatorname{Spec}k_o$ since the sum of the ideals is $(r,s)$.
This proves the stated configuration including reducedness of the intersection. All the displayed
quotient rings and substitutions stay the same after every field extension of $k_o$.

5. Over every field $F$ extending $k_o$, each standard affine line of $\mathbf P^1_F$ is
irreducible: the zero prime of $F[t]$ belongs to every nonempty basic open. The two affine lines
meet in $\operatorname{Spec}F[t,t^{-1}]$, so their union is nonempty and connected. In the
two-component case a clopen partition restricts to a trivial partition on each of the two
projective lines; their common $F$-point forces both lines into the same part. Thus $E_o$ is
nonempty and geometrically connected. Step 3 and
[lem-weil-geometrically-connected-check-after-extension] first give geometric connectedness of
$(E_x)_L$ and then of $E_x$ over $l$. By
[lem-weil-pbc-algebraic-extension-embeds-algebraically-closed], embed the finite separable
extension $L/l$ into an algebraic closure $\bar l$. Base changing the isomorphism of Step 3 to
$\bar l$ and using Step 4 identifies $(E_x)_{\bar l}$ with exactly the asserted projective-line
configuration. This does not assert that its components are individually defined over $l$.

6. By [thm-nagata-global-blowup-complement], $b$ is an isomorphism over $X\setminus\{x\}$. For
every $y\ne x$ its fibre is $\operatorname{Spec}\kappa(y)$, and after any extension $F/\kappa(y)$
it is $\operatorname{Spec}F$, a single point. Together with Step 5 this gives all the nonempty
geometrically connected fibres and surjectivity of $b$. For a geometric point $\bar s\to S$,
[lem-weil-pbc-surjective-base-change] applied to $b$ and $X_{\bar s}\to X$ gives a surjection
$B\times_X X_{\bar s}\to X_{\bar s}$. The source is $B_{\bar s}$ by the fibre-product universal
property. Hence $X_{\bar s}\ne\varnothing$ implies $B_{\bar s}\ne\varnothing$, as claimed.
-/
theorem nodal_point_blowup_projective_fibres
    (R R' : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [IsDomain R'] [IsDiscreteValuationRing R']
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (ι : R ⟶ R') [IsLocalHom ι.hom] (hι : Function.Injective ι.hom)
    [Etale (Spec.map ι)]
    (hπ' : IsLocalRing.maximalIdeal R' = Ideal.span {ι π})
    (X : Scheme.{u}) [IsNoetherian X] (f : X ⟶ Spec R) [IsHProjective f]
    (x : X) (hx : IsClosed ({x} : Set X))
    (hxs : f x = IsLocalRing.closedPoint R)
    (n : ℕ) (hn : 2 ≤ n) (U : Scheme.{u})
    (p : U ⟶ X) (q : U ⟶ DvrNodal.model R' (ι π) n) [Etale p] [Etale q]
    (hover : p ≫ f = q ≫ DvrNodal.projection R' (ι π) n ≫ Spec.map ι)
    (z : U) (hz : p z = x) (ho : DvrNodal.IsOrigin R' (ι π) n (q z))
    [Flat ((pointIdeal x hx).blowupMap ≫ f)]
    [LocallyOfFinitePresentation ((pointIdeal x hx).blowupMap ≫ f)] :
    IsHProjective (pointIdeal x hx).blowupMap ∧
    IsProper (pointIdeal x hx).blowupMap ∧
    IsHProjective ((pointIdeal x hx).blowupMap ≫ f) ∧
    IsProper ((pointIdeal x hx).blowupMap ≫ f) ∧
    Flat ((pointIdeal x hx).blowupMap ≫ f) ∧
    LocallyOfFinitePresentation ((pointIdeal x hx).blowupMap ≫ f) ∧
    QuasiCompact ((pointIdeal x hx).blowupMap ≫ f) ∧
    QuasiSeparated ((pointIdeal x hx).blowupMap ≫ f) ∧
    IsNoetherian (pointIdeal x hx).blowup ∧
    (∀ y : X, Nonempty ((pointIdeal x hx).blowupMap.fiber y) ∧
      GeometricallyConnected ((pointIdeal x hx).blowupMap.fiberToSpecResidueField y)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      Nonempty (pullback (pointIdeal x hx).blowupMap t : Scheme.{u}) ∧
        ConnectedSpace (pullback (pointIdeal x hx).blowupMap t : Scheme.{u})) ∧
    (∀ (y : X), y ≠ x → ∀ (K : Type u) [Field K] [Algebra (X.residueField y) K],
      IsIso (pullback.snd ((pointIdeal x hx).blowupMap.fiberToSpecResidueField y)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) K))))) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra (X.residueField x) Ω]
      [IsAlgClosure (X.residueField x) Ω], n = 2 →
      ∃ e : pullback ((pointIdeal x hx).blowupMap.fiberToSpecResidueField x)
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω))) ≅
          ProjectiveLine (Spec (.of Ω)),
        e.hom ≫ ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) =
          pullback.snd ((pointIdeal x hx).blowupMap.fiberToSpecResidueField x)
            (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)))) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra (X.residueField x) Ω]
      [IsAlgClosure (X.residueField x) Ω], 2 < n →
      ∃ (i j : ProjectiveLine (Spec (.of Ω)) ⟶
          pullback ((pointIdeal x hx).blowupMap.fiberToSpecResidueField x)
            (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω))))
        (a b : Spec (.of Ω) ⟶ ProjectiveLine (Spec (.of Ω))),
        IsClosedImmersion i ∧ IsClosedImmersion j ∧
        i ≫ pullback.snd ((pointIdeal x hx).blowupMap.fiberToSpecResidueField x)
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω))) =
            ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) ∧
        j ≫ pullback.snd ((pointIdeal x hx).blowupMap.fiberToSpecResidueField x)
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω))) =
            ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) ∧
        a ≫ ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) = 𝟙 _ ∧
        b ≫ ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) = 𝟙 _ ∧
        IsPullback a b i j ∧
        i.ker ⊓ j.ker = ⊥ ∧ Set.range i ∪ Set.range j = Set.univ) ∧
    Surjective (pointIdeal x hx).blowupMap ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec R),
      Nonempty (pullback f s : Scheme.{u}) →
        Nonempty (pullback ((pointIdeal x hx).blowupMap ≫ f) s : Scheme.{u})) := by
  sorry

end AlgebraicGeometry
