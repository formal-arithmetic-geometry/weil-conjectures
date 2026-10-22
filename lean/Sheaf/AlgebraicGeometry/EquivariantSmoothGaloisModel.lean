module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sober
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-!
# Equivariant smooth Galois models

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Lemma 2.2,
printed pp. 149--150, and 2.3 Step 2 through diagram (2.b), pp. 150--151.
(blueprint: lem-sfb-equivariant-smooth-galois-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A simultaneous smooth projective semilinear model, with all subgroup quotients.
The given Cartier ideal is used only through its support: radical pullback gives exactly
its reduced inverse image. The quotient by the top subgroup is the full group quotient.
The quotient predicate includes affine admission, which follows here from projectivity
over the field, and encodes the orbit quotient topology and invariant structure sheaf.
Categorical descent and geometric orbit fibres are stated explicitly for every subgroup.
The inverse in the scalar action accounts for the contravariance of `Spec`.

Source: ILO, Expose X, Lemma 2.2, pp. 149--150, and 2.3 Step 2 through (2.b), pp. 150--151.
(blueprint: lem-sfb-equivariant-smooth-galois-model)

Proof (the nine steps of the live DAG):
1. Write $B=\coprod_{j=1}^n B_j$ using the given finite disjoint integral components. Apply the
Galois component presentation to each $B_j$. It gives $e_{0j}/e$, a normal geometrically integral
proper $e_{0j}$-scheme $X_j$, its finite group $H_j$, and $u_j:X_j\to B_j$. In particular $u_j$ is
finite etale surjective and its geometric fibres are single $H_j$-orbits. The pullback of $C_B$ is
an $H_j$-stable Cartier support $Z_j$. This also verifies the nowhere dense hypothesis: in an
integral local domain a nonzero Cartier equation does not vanish at the generic point. The
faithful semilinear action and geometric integrality are exactly the hypotheses of the nodal-tower
input, not properties inferred merely from the notation $B_{e_{0j}}$.
Uses: lem-sfb-galois-component-presentation.

2. For each $(X_j/e_{0j},H_j,Z_j)$ apply the equivariant marked plurinodal alteration. Denote its
constants by $F_j$, its group by $J_j$, the surjection by $\rho_j:J_j\to H_j$, and its tower and
marked closed sets by $T_{ji},Z_{ji}$. We obtain an equivariant projective generically finite
surjection $a_j:T_{jd_j}\to X_j$, with $a_j^{-1}Z_j\subseteq Z_{jd_j}$. Over a dense open of
$X_j$, every geometric fibre is one orbit under $N_j=\ker\rho_j$. Retain this orbit assertion when
making the following birational modifications; it will control the full quotient, rather than only
the degree of the alteration.
Uses: lem-sfb-equivariant-plurinodal-field-alteration.

3. Resolve the tower by induction on $i$. The induction data are a smooth integral projective
$F_j$-scheme $S_{j,i-1}$ with an equivariant projective birational map to $T_{j,i-1}$ and relative
SNC boundary equal to the reduced preimage of $Z_{j,i-1}$. Start with
$S_{j0}=\operatorname{Spec}F_j$ and empty boundary. Apply the one-curve resolution lemma to
$f_{ji}:T_{ji}\to T_{j,i-1}$, $D=Z_{j,i-1}$, its marked sections and the already constructed base
modification $S_{j,i-1}\to T_{j,i-1}$. Its conclusion resolves the fibre product and makes the
composite back to $T_{ji}$ projective birational and surjective, giving $S_{ji}$ and precisely
that induction datum with $i$ in place of $i-1$. The projectivity clause of the lemma applies
because the preceding base is projective over $F_j$. At the top obtain $S_j=S_{jd_j}$, smooth
integral projective over $F_j$, with equivariant birational $r_j:S_j\to T_{jd_j}$ and relative SNC
boundary $E_j=(r_j^{-1}Z_{jd_j})_{\mathrm{red}}$. The lemma gives regular local rings and
parameter equations for $E_j$. Length zero requires no resolution. Each modification induces
equality of function fields; thus $a_jr_j$ remains dominant and generically finite.
Uses: lem-sfb-equivariant-nodal-smooth-pair-resolution,
lem-sfb-equivariant-plurinodal-field-alteration.

4. The reduced inverse image $D_j$ of $C_B$ in $S_j$ is a sub-divisor of $E_j$, not necessarily
the whole marked boundary. Indeed, the composite $S_j\to B_j$ is dominant, so a local Cartier
equation $c$ on $B_j$ pulls back to a nonzero element in the integral local ring of $S_j$. Off
$E_j$ it is a unit, since its zero set is contained in $E_j$. At a point, write the boundary
equations as distinct regular parameters $t_1,\ldots,t_r$. The cited regular-local UFD
factorization gives $c=u\prod t_i^{a_i}$. Its reduced zero divisor is therefore cut out by
$\prod_{a_i>0}t_i$. Globally these are a subset of the finitely many components of $E_j$. Their
intersections are among the same smooth intersections, with the same codimensions, so $D_j$ is
relative strict normal crossings. If $c$ is a unit, this subset is empty.
Uses: lem-trf-regular-local-ufd-boundary-factorization,
lem-sfb-equivariant-nodal-smooth-pair-resolution, def-trf-smooth-strict-normal-crossings-divisor.

5. Put $v_j=u_ja_jr_j:S_j\to B_j$. It is $J_j$-invariant since $u_j$ is $H_j$-invariant. At a
geometric generic point of $B_j$, its lifts to $X_j$ form one $H_j$-orbit by the component
presentation. Above each such lift, the geometric generic fibre of $a_jr_j$ is one $N_j$-orbit:
the birational map $r_j$ induces equality of generic residue fields, and hence changes none of
these geometric generic fibres. Given two points, first lift an element of $H_j$ carrying their
images to one another along the surjection $\rho_j$, then use an element of $N_j$ in that fibre.
Thus the whole geometric generic fibre of $v_j$ is one $J_j$-orbit. All generic residue extensions
remain finite, and every generic point maps to the generic point of $B_j$.
Uses: lem-sfb-galois-component-presentation, lem-sfb-equivariant-plurinodal-field-alteration,
lem-sfb-equivariant-nodal-smooth-pair-resolution.

6. Apply common-field semilinear induction to the finite family $(F_j,J_j,S_j,v_j)$. Obtain one
finite normal $K/e$, one finite group $G$ acting on $K$, and the induced schemes $Y_j$ with
invariant maps to $B_j$. Set $Y=\coprod_jY_j$ and $h=\coprod_j(Y_j\to B_j)$. The induction lemma
gives $K^G/e$ purely inseparable, single $G$-orbit geometric generic fibres, and finite residue
extensions at every generic point. Every summand of $Y$ is a scalar twist of $S_j\times_{F_j}K$.
Consequently $Y$ is smooth projective over $K$ and the reduced inverse image of $C_B$ is relative
SNC: field extension preserves smoothness and all the intersection codimensions; any components
that split are disjoint smooth components, so taking the reduced irreducible components gives the
same condition. Twisting changes only the scalar structure. Finite disjoint unions preserve these
properties (embed the finitely many projective summands in disjoint linear subspaces of one
sufficiently large projective space). The map $h$ is surjective since each $v_j$ is surjective,
the field base changes are surjective, and every coset family is nonempty.
Uses: lem-sfb-common-field-semilinear-induction, def-trf-smooth-strict-normal-crossings-divisor,
lem-sbc-smooth-relative-dimension-permanence, lem-sc-fibre-dimension-after-base-change,
lem-weil-pbc-closed-immersion-base-change, def-kun-projective.

7. The projective $K$-scheme $Y$ is also H-projective over $e$. The finite map
$\operatorname{Spec}K\to\operatorname{Spec}e$ is projective-bundle by the finite-morphism lemma;
$\mathcal O$ is ample on the affine point (the section $1$ has affine nonvanishing locus), so the
ample-base conversion makes it H-projective, and H-projective composition applies. Choose
$i:Y\hookrightarrow\mathbf P^m_e$. Since $B$ is proper over $e$, its diagonal is closed. The graph
$Y\to Y\times_eB$ of $h$ is its base change, and $i\times\mathrm{id}_B$ is also a closed immersion
by base change. Their composite embeds $Y$ into $\mathbf P^m_e\times_eB=\mathbf P^m_B$ over $B$.
Thus $h$ is H-projective and therefore projective in the projective-bundle convention as well (use
the free module $\mathcal O_B^{m+1}$). This establishes projectivity even though $B$ need not
itself be projective over $e$.
Uses: lem-trf-finite-projective-bundle, def-weil-pbc-ample-invertible-module,
lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition,
def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change,
lem-weil-pbc-closed-immersion-comp, def-nagata-projective-space-base-change, def-kun-projective,
def-trf-projective-bundle-morphism.

8. Apply finite quotient existence over $e$ to $Y$ and to every subgroup of $G$; the preceding
projective embedding supplies its quasi-projective admission hypothesis. This gives all the finite
categorical geometric quotients and their orbit and invariant-sheaf properties. In particular $h$
factors through $Q=Y/G$. For each $B_j$, choose a nonempty affine open $\operatorname{Spec}A_j$.
It is Noetherian by the component preparation. The morphism $h$ is projective and its generic
fibre is zero-dimensional, since its finitely many generic residue extensions are finite. The
projective-generically-finite lemma gives a nonempty open on which $h$ is finite; shrink this to a
principal affine open in $\operatorname{Spec}A_j$. The quotient lemma then gives finiteness of
$Q\to B$ there. These finitely many opens together meet every component. The generic fibre of
$Q\to B_j$ is reduced, since invariant subrings of reduced rings are reduced, and has one
geometric point by the orbit calculation. The radicial criterion applies also over the generic
field: two distinct field-valued lifts would remain distinct over an algebraic closure,
contradicting the one-point geometric fibre. Thus this generic morphism is radicial. Its reduced
finite coordinate algebra has a single prime ideal, which is zero; being a finite-dimensional
domain, it is a field, purely inseparable over $\kappa(B_j)$ by the same criterion.
Uses: lem-sfb-admissible-finite-type-field-quotient, lem-sfb-galois-component-presentation,
lem-fin-projective-generically-finite, def-weil-radicial-morphism.

9. Here is the dense-open radicial verification. On one of the preceding affine opens write
$A\subseteq L=\operatorname{Frac}A$ and $Q=\operatorname{Spec}R$ with $R$ finite over $A$. Its
generic algebra $R\otimes_A L$ is the purely inseparable field just found. Choose finitely many
algebra generators $b_i$ of $R$. In characteristic $p>0$, choose a common $q=p^r$ with $b_i^q\in
L$ in the generic algebra. Clear the finitely many denominators and annihilators of $b_i^q-a_i$ to
obtain one nonzero $s\in A$ and $a_i\in A[1/s]$ such that $b_i^q=a_i$ in $R[1/s]$. In
characteristic zero the generic field equals $L$ and the same argument uses $q=1$. For any field
$M$ over $A[1/s]$, an $M$-valued point of $Q$ must send each $b_i$ to the unique possible root of
$T^q-a_i$ in $M$. Hence there is at most one such point. The cited radicial criterion proves
universal injectivity. Surjectivity holds because both $h$ and the quotient map are surjective.
The integral-radicial-surjective lemma now makes this finite morphism a universal homeomorphism.
Taking the union of these principal opens gives the required dense $U$ meeting every component.
This last shrinking changes none of $Y,K,G,h$ or the boundary.
Uses: def-weil-radicial-morphism, lem-pc-integral-radicial-surjective-universal-homeomorphism.
-/
theorem exists_equivariant_smooth_galois_model
    (e : Type u) [Field e] (B : Scheme.{u}) (b : B ⟶ Spec (.of e))
    [Nonempty B] [IsProper b] [GeometricallyReduced b]
    (hBnormal : ∀ x : B, IsDomain (B.presheaf.stalk x) ∧
      IsIntegrallyClosed (B.presheaf.stalk x))
    (hBcomponents : ∃ (n : ℕ) (V : Fin n → B.Opens),
      (∀ i, IsIntegral (V i).toScheme) ∧ Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      (⨆ i, V i) = ⊤)
    (C : B.IdealSheafData) (hC : C.IsInvertible) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra e K),
      Module.Finite e K ∧
      ∃ (G : Type u) (_ : Group G) (_ : Finite G) (ρ : G →* (K ≃ₐ[e] K)),
        IsPurelyInseparable e (IntermediateField.fixedField ρ.range) ∧
        ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of K)) (a : G →* Aut Y) (h : Y ⟶ B),
          Smooth p ∧ IsHProjective p ∧ IsProjectiveBundle h ∧ Surjective h ∧
          h ≫ b = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)) ∧
          (∀ g : G, (a g).hom ≫ h = h) ∧
          (∀ g : G, (a g).hom ≫ p =
            p ≫ Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom)) ∧
          (∀ y ∈ genericPoints Y,
            h y ∈ genericPoints B ∧ (h.residueFieldMap y).hom.Finite) ∧
          (C.comap h).radical.IsSmoothStrictNormalCrossingsDivisor p ∧
          ∃ (Q : Subgroup G → Scheme.{u}) (q : ∀ H : Subgroup G, Y ⟶ Q H)
            (d : ∀ H : Subgroup G, Q H ⟶ B),
            (∀ H : Subgroup G,
              IsAdmissibleFiniteSchemeQuotient (a.comp H.subtype) (q H)) ∧
            (∀ (H : Subgroup G) (T : Scheme.{u}) (f : Y ⟶ T),
              (∀ g : H, (a g).hom ≫ f = f) →
                ∃! r : Q H ⟶ T, q H ≫ r = f) ∧
            (∀ (H : Subgroup G) (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
              Function.Surjective (fun t : Spec (.of Ω) ⟶ Y ↦ t ≫ q H) ∧
              ∀ t₁ t₂ : Spec (.of Ω) ⟶ Y, t₁ ≫ q H = t₂ ≫ q H ↔
                ∃ g : H, t₁ ≫ (a g).hom = t₂) ∧
            (∀ H : Subgroup G, q H ≫ d H = h) ∧
            ∃ U : B.Opens, Dense (U : Set B) ∧
              (∀ x ∈ genericPoints B, x ∈ U) ∧
              IsFinite ((d ⊤).resLE U ((d ⊤) ⁻¹ᵁ U) le_rfl) ∧
              (topologically IsHomeomorph).universally
                ((d ⊤).resLE U ((d ⊤) ⁻¹ᵁ U) le_rfl) := by
  sorry

end AlgebraicGeometry
