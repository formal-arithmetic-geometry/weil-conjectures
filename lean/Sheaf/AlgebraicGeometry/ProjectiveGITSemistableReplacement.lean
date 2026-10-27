module

public import Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization
public import WeilConjectures.AlgebraicGeometry.GenericQuotient
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Jacobson.Ring
import Sheaf.RingTheory.DiscreteValuationRing.FinitelyGeneratedExtension

/-! # Projective GIT semistable replacement over a trait

Source: Morrison, arXiv:0810.2340, §3.3, Corollary 11(2), printed p.17,
semistable replacement citing Mumford, Stability of projective varieties, Lemma 5.3.
(blueprint: lem-sfb-projective-git-semistable-replacement)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Semistable replacement after a finite fraction-field extension. The specified
PGL presentation is the fpqc scalar quotient, and the supplied open is characterized
on all geometric points by the recorded invariant-section semistability convention.
Writing the replacement ring as a subalgebra of its fraction field loses no DVR:
the injective fraction map identifies any DVR with its image.
Source: Morrison, arXiv:0810.2340, §3.3, Corollary 11(2), printed p.17.

Proof (the six steps of the DAG):
1. Apply [lem-sfb-projective-pgl-invariant-quotient] to obtain $q:Z^{ss}(A)\to Q$. The scheme $Q$
is proper over $k$, because it is projective. The generic quotient point $q\circ
z:\operatorname{Spec}K\to Q$ therefore extends by the valuative existence criterion to
$u:S=\operatorname{Spec}R\to Q$. Here $R$ is a valuation ring with its specified fraction field.
Form $X=Z^{ss}(A)\times_Q S$; since $q$ is affine and of finite type, $X=\operatorname{Spec}B$ for
a finite-type $R$-algebra $B$. The point $z$ defines a $K$-point of the generic fibre of $X$.

2. Let $\alpha:G_K\to X_K$ be $g\mapsto g\cdot z$ and put $I=\ker(B\to K[G])$, $D=B/I$,
$Y=\operatorname{Spec}D\subset X$. The algebra $K[G]$ is a domain: $\operatorname{PGL}_{r,K}$ is
the determinant-nonzero open in the projective space of matrices, hence is integral. Thus $D$ is a
domain, $R\hookrightarrow D$, and $Y$ is an integral finite-type $S$-scheme dominating $S$. Its
generic fibre is the reduced schematic closure of the orbit image. To verify invariance over the
whole trait, write $H=R\otimes_k k[G]$. It is a free $R$-module, by choosing a $k$-basis of
$k[G]$. The coaction of an element of $I$ maps to zero in $(D\otimes_RH)[1/\pi]$: write
$\beta:B[1/\pi]\to K[G]$ for the orbit homomorphism. Equivariance says
$(\beta\otimes1)\rho=\Delta\beta$, so it annihilates $I$. The injection $D[1/\pi]\hookrightarrow
K[G]$ stays injective after tensoring over the field $K$; hence the image of $\rho(I)$ in
$(D\otimes_RH)[1/\pi]$ is zero. Since $D\otimes_RH$ is a direct sum of copies of the torsion-free
module $D$, localization at $\pi$ is injective. The coaction already vanishes in $D\otimes_RH$.
Hence $I$ is preserved by the $G_S$-action and $Y$ is an invariant closed subscheme of $X$.

3. The universal closed-image clause of [lem-sfb-projective-pgl-invariant-quotient], with $T=S$
and $C=Y$, says that the image of $Y\to S$ is closed. It contains the generic point, since
$\alpha$ factors through $Y_K$. The closure of that generic point is all of $S$, so $Y_s$ is
nonempty. This applies to the actual base change along $u$, without any assertion that taking
invariants commutes with this possibly nonflat base change.

4. The morphism $\alpha:G_K\to Y_K$ is a morphism of affine finite-type $K$-schemes. By
[lem-wf-affine-constructible-open], its image is constructible and contains a nonempty open $U$ of
its closure. The injection $D[1/\pi]\hookrightarrow K[G]$ shows that this closure is all of $Y_K$.
Thus $U\subseteq Y_K$ is nonempty open and every point of $U$ has nonempty fibre under $\alpha$.
This avoids requiring that a chosen lift of a quotient point belong to the original orbit.

5. Apply [lem-sfb-dense-generic-trait-selection] to $Y\to S$ and this $U$. Step 2 gives
integrality, finite type and dominance, and Step 3 gives the required nonempty special fibre. We
obtain $R\hookrightarrow R_0$, locally, with fraction field $K_0$ finite over $K$, and
$c:\operatorname{Spec}R_0\to Y$ whose generic restriction is a point $y_0\in U(K_0)$.

6. The fibre $G_K\times_{Y_K}\operatorname{Spec}K_0$ over $y_0$ is a nonempty affine finite-type
$K_0$-scheme. Choose a maximal ideal of its nonzero coordinate ring; its residue field $K'$ is
finite over $K_0$ by [lem-weil-pbc-zariski-lemma]. The resulting point is $h\in G(K')$ with
$\alpha(h)=y_{0,K'}$. Apply [lem-sfb-local-domain-fg-field-dvr] to the Noetherian local domain
$R_0$ and the finite, hence finitely generated, field extension $K'/K_0$. It gives a DVR
$R'\subset K'$ dominating $R_0$ and with fraction field $K'$. Pull $c$ back along
$\operatorname{Spec}R'\to\operatorname{Spec}R_0$, then compose $Y\hookrightarrow X\to Z^{ss}(A)$
to obtain $b$. On the generic fibre the defining equality $\alpha(h)=y_{0,K'}$ is exactly
$b_{K'}=h\cdot z_{K'}$. The composite $R\to R_0\to R'$ is injective and local; hence closed points
map to closed points. The tower $K\subset K_0\subset K'$ is finite by multiplying vector-space
bases. All maps are over $k$.
(blueprint: lem-sfb-projective-git-semistable-replacement) -/
theorem exists_projective_git_semistable_replacement
    (k : Type u) [Field k] (r : ℕ) (hr : 2 ≤ r)
    (G : Grp (Over (Spec (.of k))))
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k ⟶ G.X)
    (j : StandardGroupSchemes.roots k r ⟶ LinearGroupSchemes.specialLinear k r)
    (hG : ProjectiveMatrixCentralCover.Presentation k r hr G π j)
    (Z : Over (Spec (.of k))) [IsHProjective Z.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (action : ModObj G.X Z) (A : Z.left.Modules) [A.IsInvertible]
    (hA : Scheme.Modules.IsAmple Z.left A)
    (D : GroupSchemeLinearization.Linearization action A)
    (U : Z.left.Opens)
    (hU : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : PGLLinearization.fieldTest k Ω ⟶ Z),
      x.left (IsLocalRing.closedPoint Ω) ∈ U ↔ D.IsSemistable Ω x)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K]
    (z : PGLLinearization.fieldTest k K ⟶ Z)
    (hz : z.left (IsLocalRing.closedPoint K) ∈ U) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra k K')
      (_ : IsScalarTower k K K') (_ : Module.Finite K K') (R' : Subalgebra k K')
      (_ : IsDiscreteValuationRing R') (_ : IsFractionRing R' K') (φ : R →ₐ[k] R'),
      Function.Injective φ ∧ IsLocalHom φ ∧
      R'.val.comp φ = (IsScalarTower.toAlgHom k K K').comp
        (IsScalarTower.toAlgHom k R K) ∧
      ∃ (h : PGLLinearization.fieldTest k K' ⟶ G.X) (b : specAlgOver (k := k) R' ⟶ Z),
        (∀ p : Spec (.of R'), b.left p ∈ U) ∧
        specAlgOverMap R'.val ≫ b = GroupSchemeLinearization.act action
          (PGLLinearization.fieldTest k K') h
          (specAlgOverMap (IsScalarTower.toAlgHom k K K') ≫ z) ∧
        (Spec.map (CommRingCat.ofHom φ.toRingHom)) (IsLocalRing.closedPoint R') =
          IsLocalRing.closedPoint R := by
  sorry

end AlgebraicGeometry
