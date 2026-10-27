module

public import Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability
public import Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective
public import Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover
public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import Sheaf.AlgebraicGeometry.HilbertUniformSectionBound
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.MvPolynomial.Basic

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.Descent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen

/-! # Hilbert embeddings and descent of their determinant linearizations

Source: Morrison, arXiv:0810.2340, §2.1, pp.4--5, with the full central-scheme
and field-extension argument in the DAG.
(blueprint: lem-sfb-hilbert-plucker-pgl-linearization)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.HilbertPlucker

/-- We write r = n + 2, which parametrizes exactly all r ≥ 2.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
abbrev Coordinates (n : ℕ) := LinearGroupSchemes.Index.{u} (n + 2)

/-- The specified component of the recorded Hilbert representation. The universal
ideal is transported along the canonical projective-space base-change square.
Source: Grothendieck Exposé 221, Theorems 3.1--3.2; Morrison §2.1
(blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
structure Hilbert (k : Type u) [Field k] (n : ℕ) (P : NumericalHilbertPolynomial) where
  total : Over (Spec (.of k))
  representation : (properHilbertPresheaf
    (ℙ(Coordinates.{u} n; Spec (.of k)) ↘ Spec (.of k))).RepresentableBy total
  components : NumericalHilbertPolynomial → Over (Spec (.of k))
  inclusion : ∀ Q, components Q ⟶ total
  coproduct : Nonempty (IsColimit (Cofan.mk total inclusion))
  projective : ∀ Q, IsHProjective (components Q).hom
  component : ∀ (Q : NumericalHilbertPolynomial) (T : Over (Spec (.of k))) (b : T ⟶ total),
    HasProjectiveFibreHilbertPolynomial
      (ℙ(Coordinates.{u} n; Spec (.of k)) ↘ Spec (.of k))
      (𝟙 (ℙ(Coordinates.{u} n; Spec (.of k)))) T
      (representation.homEquiv b).1 Q.1 ↔ ∃! a : T ⟶ components Q, a ≫ inclusion Q = b
  ideal : (ℙ(Coordinates.{u} n; (components P).left)).IdealSheafData
  universal_ideal : ideal = (representation.homEquiv (inclusion P)).1.comap
    (ProjectiveSpace.isPullback_map (Coordinates n) (components P).hom).isoPullback.hom

variable {k : Type u} [Field k] {n : ℕ} {P : NumericalHilbertPolynomial}

/-- The specified polynomial component, with no choice of a representing object.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def Hilbert.H (D : Hilbert k n P) : Over (Spec (.of k)) := D.components P

/-- The actual degree-m direct image on the universal family.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def sections (D : Hilbert k n P) (m : ℕ) : D.H.left.Modules :=
  HilbertSectionBound.closedSections D.ideal.subschemeι (m : ℤ)

/-- Restriction of the actual degree-m monomial section.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def monomialRestriction (D : Hilbert k n P) (m : ℕ)
    (a : RelativeProjectiveSpace.monomials.{u} (n + 1) m) : Γ(sections D m, ⊤) :=
  (SheafOfModules.freeHomEquiv (sections D m)
    (HilbertSectionBound.polynomialMap D.H.left (n + 1) m ≫
      HilbertSectionBound.sectionRestriction D.ideal.subschemeι (m : ℤ)) a).val (op ⊤)

/-- The constant symmetric-power module maps by restriction, in a specified monomial
ordering. The ordering is an equivalence, so this does not discard any monomial.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def quotient (D : Hilbert k n P) (m N : ℕ)
    (e : ULift.{u} (Fin N) ≃ RelativeProjectiveSpace.monomials.{u} (n + 1) m) :
    SheafOfModules.free (R := D.H.left.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ sections D m :=
  Sigma.desc fun a ↦ Scheme.Modules.homOfGlobalSection _ (monomialRestriction D m (e a))

/-- The determinant is the recorded top exterior sheaf, including rank zero.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def determinant (D : Hilbert k n P) (m p : ℕ) : D.H.left.Modules :=
  Scheme.Modules.exteriorSheaf (sections D m) p

/-- The generating Plücker sections, before imposing an increasing ordering.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def wedgeSection (D : Hilbert k n P) (m p N : ℕ)
    (e : ULift.{u} (Fin N) ≃ RelativeProjectiveSpace.monomials.{u} (n + 1) m)
    (a : Fin p → Fin N) : Γ(determinant D m p, ⊤) :=
  Scheme.Modules.exteriorSheafSection (sections D m) p ⊤
    (fun j ↦ monomialRestriction D m (e (ULift.up (a j))))

/-- Entries of a scheme-valued matrix, by pullback of the existing coordinate functions.
No affine-test or reducedness restriction is made.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def entry (T : Over (Spec (.of k)))
    (g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k) (i j : Coordinates.{u} n) :
    Γ(T.left, ⊤) :=
  g.left.appTop.hom ((Scheme.ΓSpecIso
    (.of (Matrix.GeneralLinearGroup.CoordinateRing (Coordinates n) k))).inv.hom
      (Matrix.GeneralLinearGroup.coord (Coordinates n) k i j))

/-- Coefficients of the contragredient degree-m polynomial substitution. This fixes
which SL linearization is meant, rather than permitting an arbitrary line action.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
def coefficient (T : Over (Spec (.of k)))
    (g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k) (m : ℕ)
    (a b : RelativeProjectiveSpace.monomials.{u} (n + 1) m) : Γ(T.left, ⊤) :=
  MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm b.down.val)
    (∏ i : Fin (n + 2),
      (∑ j : Fin (n + 2),
        MvPolynomial.C (entry T g⁻¹ (ULift.up i) (ULift.up j)) * MvPolynomial.X j) ^
          a.down.val i)

/-- The SL group, bundled without choosing any new group law.
Source: Morrison §2.1 (blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
abbrev SL (k : Type u) [Field k] (n : ℕ) : Grp (Over (Spec (.of k))) :=
  ⟨LinearGroupSchemes.specialLinear k (n + 2)⟩

/-- The data and properties in one sufficiently high Hilbert degree. All arrows on
quotients, Plücker coordinates, projective coordinates and determinant lines are fixed
by their displayed generator formulas.
Source: Morrison §2.1 and the DAG central-descent expansion
(blueprint: lem-sfb-hilbert-plucker-pgl-linearization). -/
structure Presentation (D : Hilbert k n P) (m : ℕ) where
  p : ℕ
  value : P.1.eval (m : ℚ) = (p : ℚ)
  rank : (sections D m).IsFiniteLocallyFreeOfRank p
  base_change : ∀ (T : Scheme.{u}) (a : T ⟶ D.H.left),
    IsIso (Scheme.Modules.moduleBaseChangeMap
      (D.ideal.subschemeι ≫ HilbertSectionBound.projection D.H.left (n + 1))
      (pullback.snd
        (D.ideal.subschemeι ≫ HilbertSectionBound.projection D.H.left (n + 1)) a)
      a (pullback.fst
        (D.ideal.subschemeι ≫ HilbertSectionBound.projection D.H.left (n + 1)) a)
      pullback.condition (HilbertSectionBound.closedTwist D.ideal.subschemeι (m : ℤ)))
  N : ℕ
  monomials : ULift.{u} (Fin N) ≃ RelativeProjectiveSpace.monomials.{u} (n + 1) m
  rank_bound : p ≤ N
  surjective : Epi (quotient D m N monomials)
  grassmann : Over (Spec (.of k))
  universal : grassmann.left.Modules
  universal_quotient :
    SheafOfModules.free (R := grassmann.left.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ universal
  universal_surjective : Epi universal_quotient
  universal_rank : universal.IsFiniteLocallyFreeOfRank p
  grassmann_classifies : ∀ (T : Over (Spec (.of k))) (Q : T.left.Modules)
    (q : SheafOfModules.free (R := T.left.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q),
    Epi q → Q.IsFiniteLocallyFreeOfRank p →
    ∃! a : T ⟶ grassmann, ∃ f : (Scheme.Modules.tensorPullback a.left).obj universal ≅ Q,
      freeQuotientPullback a.left universal_quotient ≫ f.hom = q
  hilbert_map : D.H ⟶ grassmann
  hilbert_quotient : ∃ f :
    (Scheme.Modules.tensorPullback hilbert_map.left).obj universal ≅ sections D m,
    freeQuotientPullback hilbert_map.left universal_quotient ≫ f.hom =
      quotient D m N monomials
  plucker : grassmann.left ⟶ ℙ(ULift.{u} (Set.powersetCard (Fin N) p); Spec (.of k))
  plucker_over : plucker ≫ ℙ(ULift.{u} (Set.powersetCard (Fin N) p); Spec (.of k)) ↘
    Spec (.of k) = grassmann.hom
  plucker_closed : IsClosedImmersion plucker
  plucker_line : (Scheme.Modules.tensorPullback plucker).obj
    (ProjectiveSpace.twist (ULift.{u} (Set.powersetCard (Fin N) p)) (Spec (.of k)) 1) ≅
      Scheme.Modules.exteriorSheaf universal p
  plucker_coordinates : ∀ I : ULift.{u} (Set.powersetCard (Fin N) p),
    plucker_line.hom.app ⊤
      (((Scheme.Modules.tensorPullbackSectionAdjunction plucker).unit.app
        (ProjectiveSpace.twist (ULift.{u} (Set.powersetCard (Fin N) p))
          (Spec (.of k)) 1)).app ⊤
            (ProjectiveSpace.twistOneSection (ULift.{u} (Set.powersetCard (Fin N) p))
              (Spec (.of k)) I)) =
      Scheme.Modules.exteriorSheafSection universal p ⊤
        (fun j ↦ (SheafOfModules.freeHomEquiv universal universal_quotient
          (ULift.up (I.down.val.orderEmbOfFin I.down.property j))).val (op ⊤))
  embedding : IsClosedImmersion (hilbert_map.left ≫ plucker)
  hyperplane : Nonempty ((Scheme.Modules.tensorPullback (hilbert_map.left ≫ plucker)).obj
    (ProjectiveSpace.twist (ULift.{u} (Set.powersetCard (Fin N) p)) (Spec (.of k)) 1) ≅
      determinant D m p)
  invertible : (determinant D m p).IsInvertible
  ample : @Scheme.Modules.IsAmple D.H.left (determinant D m p) invertible
  power_invertible : ((determinant D m p).tensorPow (n + 2)).IsInvertible
  power_ample : @Scheme.Modules.IsAmple D.H.left
    ((determinant D m p).tensorPow (n + 2)) power_invertible
  G : Grp (Over (Spec (.of k)))
  π : GeneralLinearGroup (Coordinates.{u} n) k ⟶ G.X
  roots : StandardGroupSchemes.roots k (n + 2) ⟶ LinearGroupSchemes.specialLinear k (n + 2)
  cover : ProjectiveMatrixCentralCover.Presentation k (n + 2) (by omega) G π roots
  action : ModObj G.X D.H
  sl_action : ModObj (SL k n).X D.H
  sl_restriction : ∀ (T : Over (Spec (.of k)))
    (g : T ⟶ (SL k n).X) (x : T ⟶ D.H),
    GroupSchemeLinearization.act sl_action T g x =
      GroupSchemeLinearization.act action T
        (g ≫ LinearGroupSchemes.inclusion k (n + 2) ≫ π) x
  coordinate_automorphism : ∀ (T : Over (Spec (.of k)))
    (_g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k),
    ℙ(Coordinates.{u} n; T.left) ≅ ℙ(Coordinates.{u} n; T.left)
  coordinate_over : ∀ (T : Over (Spec (.of k)))
    (g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k),
    (coordinate_automorphism T g).hom ≫ HilbertSectionBound.projection T.left (n + 1) =
      HilbertSectionBound.projection T.left (n + 1)
  coordinate_line : ∀ (T : Over (Spec (.of k)))
    (g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k),
    (Scheme.Modules.pullback (coordinate_automorphism T g).hom).obj
      (ProjectiveSpace.twist (Coordinates n) T.left 1) ≅
        ProjectiveSpace.twist (Coordinates n) T.left 1
  coordinate_formula : ∀ (T : Over (Spec (.of k)))
    (g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k) (i : Coordinates.{u} n),
    (coordinate_line T g).hom.app ⊤
      (pullbackΓ (coordinate_automorphism T g).hom
        (ProjectiveSpace.twist (Coordinates n) T.left 1)
        (ProjectiveSpace.twistOneSection (Coordinates n) T.left i)) =
      ∑ j : Coordinates.{u} n,
        (HilbertSectionBound.projection T.left (n + 1)).appTop.hom (entry T g i j) •
          ProjectiveSpace.twistOneSection (Coordinates n) T.left j
  coordinate_action : ∀ (T : Over (Spec (.of k)))
    (g : T ⟶ GeneralLinearGroup (Coordinates.{u} n) k) (x : T ⟶ D.H),
    D.ideal.comap (ProjectiveSpace.map (Coordinates n)
      (GroupSchemeLinearization.act action T (g ≫ π) x).left) =
      (D.ideal.comap (ProjectiveSpace.map (Coordinates n) x.left)).comap
        (coordinate_automorphism T g).inv
  sl_line : GroupSchemeLinearization.Linearization sl_action (determinant D m p)
  determinant_formula : ∀ (T : Over (Spec (.of k))) (g : T ⟶ (SL k n).X)
    (x : T ⟶ D.H) (a : Fin p → Fin N),
    (sl_line.lift T g x).hom.app ⊤
      (pullbackΓ x.left (determinant D m p) (wedgeSection D m p N monomials a)) =
      ∑ b : Fin p → Fin N,
        (∏ j : Fin p, coefficient T (g ≫ LinearGroupSchemes.inclusion k (n + 2)) m
          (monomials (ULift.up (a j))) (monomials (ULift.up (b j)))) •
        pullbackΓ (GroupSchemeLinearization.act sl_action T g x).left
          (determinant D m p) (wedgeSection D m p N monomials b)
  pgl_line : GroupSchemeLinearization.Linearization action
    ((determinant D m p).tensorPow (n + 2))
  descent : ∀ (T : Over (Spec (.of k))) (g : T ⟶ (SL k n).X) (x : T ⟶ D.H),
    HEq (pgl_line.lift T (g ≫ LinearGroupSchemes.inclusion k (n + 2) ≫ π) x)
      (sl_line.powerLift T g x (n + 2))
  semistable : D.H.left.Opens
  stable : D.H.left.Opens
  semistable_points : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (x : PGLLinearization.fieldTest k Ω ⟶ D.H),
    (x.left (IsLocalRing.closedPoint Ω) ∈ semistable ↔ sl_line.IsSemistable Ω x) ∧
    (sl_line.IsSemistable Ω x ↔ pgl_line.IsSemistable Ω x)
  stable_points : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (x : PGLLinearization.fieldTest k Ω ⟶ D.H),
    (x.left (IsLocalRing.closedPoint Ω) ∈ stable ↔ sl_line.IsStable Ω x) ∧
    (sl_line.IsStable Ω x ↔ pgl_line.IsStable Ω x)

end AlgebraicGeometry.HilbertPlucker

namespace AlgebraicGeometry

/-- The field-independent Hilbert embedding bound, determinant linearizations and
base-change-compatible common stable and semistable opens. A Hilbert representative
is supplied as data, exactly as in the node; existence is the recorded representability
theorem. The parameter n writes r = n + 2 and includes every allowed matrix size.
Source: Morrison, arXiv:0810.2340, §2.1, pp.4--5.

Proof, following all eleven DAG steps:

1. Apply [lem-sfb-hilbert-uniform-section-bound] with $n=r-1$ and polynomial $P$ to the universal
closed family over $H$ furnished by [lem-sfb-projective-hilbert-polynomial-representability]. It
is flat and finitely presented, and every geometric fibre has polynomial $P$, exactly the
hypotheses of the bound. Choose its integer $b\geq1$ and set $M(P,r)=b$. For every $m\geq b$ we
obtain the base-change-compatible exact sequence $0\to I_m\to V_m\otimes_k\mathcal O_H\to
Q_m\to0$, with $V_m=\operatorname{Sym}^m(k^r)$, $Q_m=f_*L^{\otimes m}$ locally free of rank
$P(m)$, and $I_m=p_*\mathcal I(m)$. The bound is uniform over all base schemes, so in particular
independent of the field. The universal-quotient property of [lem-sfb-free-quotient-grassmann-
projective] now gives a morphism $j_m:H\to G_k(N_m,P(m))$, where $N_m=\dim_k V_m$.

2. The degree-$m$ kernel determines the whole closed family, not merely its geometric fibres.
Indeed [lem-sfb-hilbert-uniform-section-bound] says that $\mathcal I$ is generated by
$I_b\otimes\mathcal O(-b)$ and that multiplication $V_{m-b}\otimes I_b\to I_m$ is onto. On the
projective chart $D_+(x_i)$, each local degree-$b$ generator $u$ equals $(x_i^{m-b}u)/x_i^m$ after
trivializing the twists. The numerator belongs to $I_m$. Thus the image of $I_m\otimes\mathcal
O(-m)$ is precisely $\mathcal I$. This calculation holds on arbitrary test schemes, including
nonreduced ones. Two $T$-points of $H$ inducing the same quotient of $V_m\otimes\mathcal O_T$ have
the same kernel, hence the same ideal sheaf and closed subscheme. Since $H$ represents embedded
subschemes, $j_m$ is a monomorphism.

3. The scheme $H$ is projective, hence proper, by [lem-sfb-projective-hilbert-polynomial-
representability]. Its Grassmannian target is projective by [lem-sfb-free-quotient-grassmann-
projective], hence proper and in particular separated by [lem-kun-projective-implies-proper].
Therefore $j_m$ is proper by [lem-weil-pbc-proper-to-separated]. Together with the monomorphism of
the preceding step, [lem-pc-proper-monomorphism-closed] makes $j_m$ a closed immersion. Compose
with the Plücker closed immersion of [lem-sfb-free-quotient-grassmann-projective], using [lem-
weil-pbc-closed-immersion-comp]. When $P(m)=0$ or $N_m$, the Grassmannian is the point
$\operatorname{Spec}k$, and its Plücker map is the identity to $\mathbf P^0_k$. This also covers
the empty subscheme and the full projective-space polynomial.

4. In the quotient convention the Plücker point of $V_m\twoheadrightarrow Q_m$ is the line
quotient $\bigwedge^{P(m)}V_m\twoheadrightarrow\bigwedge^{P(m)}Q_m$. Therefore its pulled-back
hyperplane line is $\Lambda_m=\det Q_m$, by the top-exterior-power definition [def-sc-sheaf-
exterior-power]; locally this sends $v_1\wedge\cdots\wedge v_{P(m)}$ to the wedge of their images.
In rank zero the same definition gives $\det(0)=\mathcal O_H$, so no exceptional determinant
convention is needed. By [lem-pc-very-ample-ample] the hyperplane pullback is ample; [lem-sc-
ample-positive-tensor-power] makes $A_m=\Lambda_m^{\otimes r}$ ample as well.

5. Changing coordinates acts on the Hilbert functor: an invertible matrix carries a closed family
to its image under the induced automorphism of projective space. Representability of $H$ by [lem-
sfb-projective-hilbert-polynomial-representability] and [lem-pc-yoneda] turns this natural
transformation into a GL action morphism. Scalar matrices induce the identity automorphism on
every test scheme. The fpqc quotient property in [lem-sfb-projective-matrix-central-cover],
together with full faithfulness for scheme morphisms under fpqc pullback [lem-galois-fpqc-
morphisms-descend], descends this action to $\operatorname{PGL}_{r,k}$. Its unit and
multiplication identities descend because they are the corresponding identities on families. The
degree-$m$ quotient commutes with arbitrary base change by [lem-sfb-hilbert-uniform-section-
bound], hence is equivariant for the natural SL action on $V_m$. Taking the exterior power gives
the action on $\Lambda_m$; its cocycle identity holds on wedges because the two composites apply
the same linear maps to every factor [def-sc-sheaf-exterior-power]. This is an SL linearization
lifting the coordinate action.

6. For an arbitrary $k$-algebra $R$ and $t\in\mu_r(R)$, the scalar $tI$ acts on degree-$m$
coordinate polynomials by $t^m$, hence on $Q_m$ by $t^m$, and on its top wedge by $t^{mP(m)}$.
Thus on $A_m$ the scalar is $t^{rmP(m)}=(t^r)^{mP(m)}=1$. This is an identity over $k[t]/(t^r-1)$,
not only an assertion about geometric roots. If coordinates are identified with dual vectors, both
exponents acquire a minus sign and the same identity holds. The torsor identity of [lem-sfb-
projective-matrix-central-cover] identifies two SL lifts of a PGL element as $g$ and $gz$ with
$z\in\mu_r$. Their isomorphisms on $A_m$ are equal by this calculation. By full faithfulness in
[lem-pc-fpqc-descent], the linearization isomorphism descends along $q\times\mathrm{id}_H$ to PGL.
Its unit and multiplication identities descend by the same faithfulness, checked after the covers
$q\times\mathrm{id}_H$ and $q\times q\times\mathrm{id}_H$. The descended isomorphism therefore
defines the required line action, with the stated SL pullback.

7. Fix any algebraically closed extension $\Omega/k$. Invariants on powers of $A_m$ for SL equal
invariants for PGL: the equality defining invariance is an equality of module maps after pullback
along the fpqc cover $q\times\mathrm{id}$, and is reflected by [lem-pc-fpqc-descent]. An SL-
invariant section $s$ of $\Lambda_m^{\otimes d}$ gives the PGL-invariant section $s^r$ of
$A_m^{\otimes d}$ with exactly the same nonvanishing set. Conversely a PGL-invariant section of
$A_m^{\otimes d}$ is an SL-invariant section of $\Lambda_m^{\otimes rd}$. Thus the semistable sets
coincide. The map $\operatorname{SL}_r(\Omega)\to\operatorname{PGL}_r(\Omega)$ is onto by [lem-
sfb-projective-matrix-central-cover] (equivalently rescale a matrix by an $r$th root of its
inverse determinant), so the orbits in this common set coincide. Both groups have dimension
$r^2-1$, and the orbit dimension formula [lem-sfb-smooth-group-orbit-geometry] consequently gives
equal dimensions of their scheme-theoretic stabilizers. Closedness of the common orbit and
dimension zero of the stabilizer are therefore equivalent for the two actions. This proves
equality of the stable sets too.

8. The common semistable locus is an open subscheme and commutes with field extension. For clarity
use the PGL linearization on $A_m$. For every $d>0$, flat cohomology base change [lem-pc-flat-
cohomology-separated], in degree zero on the projective separated scheme $H$, identifies sections
after $K/k$ with $K\otimes_k H^0(H,A_m^{\otimes d})$. The same flat-base-change result applied to
the flat algebra $k[G]$ identifies action pullbacks with the group coaction on sections. This
coaction defines invariants as the kernel of $v\mapsto\rho(v)-v\otimes1$; tensoring with a field
extension is exact, so invariants also commute with $K/k$. Every invariant section after extension
is a finite linear combination of extended invariant sections of the same degree. If it is nonzero
at a geometric point, at least one summand is nonzero there. The union of the invariant-section
nonvanishing opens over $k$ therefore has exactly the defined geometric semistable points over
every extension. These nonvanishing sets are the open subschemes in [def-weil-pbc-ample-
invertible-module].

9. Let $s$ be a positive-degree PGL-invariant section of a power of $A_m$. The open $U_s=H_s$ is
affine of finite type by [lem-sfb-projective-polarization-section-algebra], applied to $\Lambda_m$
and the section $s$ of its corresponding positive power. Over an algebraically closed extension,
an orbit in $U_s$ is closed in the full semistable locus if and only if it is closed in $U_s$.
Only the reverse direction needs an argument. Suppose $y$ is in its closure inside the semistable
locus and choose a homogeneous invariant $t$ nonzero at $y$. Then $t$ is nonzero on the orbit as
well, since its zero set is invariant and closed. If $s$ and $t$ have degrees $a,b$ in powers of
$A_m$, the invariant function $s^b/t^a$ on $H_t$ is a nonzero constant $c$ on the orbit. Its value
is $c$ on the orbit closure in $H_t$, so $s(y)\ne0$. Thus every such boundary point lies in $U_s$,
contradicting closedness there. Stabilizers do not change on an invariant open. Hence the
project's stability condition is equivalent on $U_s$ to a closed orbit there with stabilizer
dimension zero.

10. On $U=U_s$ let $\mathcal S\to U$ be the scheme of stabilizers, the equalizer of action and
projection inside $G\times U$ with identity section $e:U\to\mathcal S$. It is of finite type,
since $G$ and $U$ are of finite type and $U$ is separated. By [lem-weil-pbc-local-fibre-dimension-
open] the points of $\mathcal S$ with local fibre dimension zero form an open. Pull it back along
$e$. For a geometric point $\bar u$ over an algebraically closed $\Omega$, the fibre $\mathcal
S_{\bar u}$ is the stabilizer $G_{\bar u}$, a group scheme of finite type over $\Omega$ whose
identity $\bar e$ is an $\Omega$-rational point. Then [lem-kun-dimension-formula] gives
$\dim_{\bar e}G_{\bar u}=\dim\mathcal O_{G_{\bar u},\bar e}$, which equals $\dim G_{\bar u}$ by
[lem-ag-group-identity-local-dimension]; by [lem-sc-fibre-dimension-after-base-change] it is also
the local dimension of $\mathcal S_u$ at $e(u)$. It follows that $D=\{x:\dim G_{\bar x}>0\}$ is a
closed invariant subset of $U$. By [lem-sc-fibre-dimension-after-base-change], this closed subset
pulls back to the same positive-dimensional-stabilizer subset under every field extension. This
also explains why tangent-space dimension, which could detect nonreduced finite stabilizers, is
not used.

11. Apply [lem-sfb-affine-pgl-quotient-orbit-topology] to $U=\operatorname{Spec}E$, obtaining
$p:U\to Y=\operatorname{Spec}(E^G)$ and the closed subset $p(D)$. The open $W=U\setminus
p^{-1}(p(D))$ consists exactly of closed orbits with stabilizer dimension zero. Indeed a geometric
fibre disjoint from $D$ has all its orbits of dimension $\dim G$ by [lem-sfb-smooth-group-orbit-
geometry]; none can degenerate to a smaller-dimensional boundary orbit. Its unique closed orbit
from the affine quotient theorem must therefore be the whole fibre. Conversely, if a fibre
contains a closed orbit of dimension $\dim G$, any other orbit would have that orbit in its
boundary and therefore larger dimension, impossible. Thus that fibre is a single orbit, is
disjoint from $D$, and lies in $W$. The affine quotient and the image of $D$ commute with field
extension by [lem-sfb-affine-pgl-quotient-orbit-topology]; the preceding step gives the same fact
for $D$. Hence $W$ commutes with field extension. By the preceding comparison on invariant affine
opens, the union of these $W$ over all $s$ is precisely the stable open in $H$. Its formation
commutes with field extension: the extended invariant opens from the previous semistable-base-
change step cover every extended semistable locus. The SL stable and semistable opens are the same
opens, by step 7. All calculations used the full central group scheme and full stabilizers, so
they also apply when $\mu_r$ is nonreduced.
(blueprint: lem-sfb-hilbert-plucker-pgl-linearization) -/
theorem exists_hilbert_plucker_pgl_linearization (n : ℕ) (P : NumericalHilbertPolynomial)
    (hP : ∃ (k₀ : Type u) (F : Field k₀) (Z : Scheme.{u})
      (i : Z ⟶ ℙ(HilbertPlucker.Coordinates.{u} n;
        Spec (@CommRingCat.of k₀ F.toCommRing))),
      IsClosedImmersion i ∧
        @ProjectiveHilbertPolynomial.IsCoordinatePolynomial k₀ F (n + 1) Z i P.1) :
    ∃ M : ℕ, ∀ (k : Type u) [Field k] (D : HilbertPlucker.Hilbert k n P)
      (m : ℕ), M ≤ m → ∃ E : HilbertPlucker.Presentation D m,
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∃ (DK : HilbertPlucker.Hilbert K n P) (EK : HilbertPlucker.Presentation DK m)
          (h : DK.H.left ⟶ D.H.left),
          IsPullback h DK.H.hom D.H.hom (ProjectiveMatrixCentralCover.extension k K) ∧
          DK.ideal = D.ideal.comap (ProjectiveSpace.map (HilbertPlucker.Coordinates n) h) ∧
          EK.semistable = h ⁻¹ᵁ E.semistable ∧ EK.stable = h ⁻¹ᵁ E.stable := by
  sorry

end AlgebraicGeometry
