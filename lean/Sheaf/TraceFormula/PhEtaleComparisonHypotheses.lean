module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Sheaf.AlgebraicGeometry.PhSchemeSite
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.TraceFormula.BigSmallEtaleExactRetraction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.PhAffineStandardSieveBasis
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.TraceFormula.BigSmallEtalePullbackFormula
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm

/-!
# Proper and étale hypotheses for the ph/étale comparison

Source: Stacks Project, Étale Cohomology, Tag 0F0I, `lemma-compare-ph-etale`,
with the setup of section-ph-etale and Sites, Tag 0EZ3
(blueprint: lem-trf-ph-etale-comparison-hypotheses).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The category of abelian sheaves on the big étale site over `X`.
Source: Stacks, Tags 0F0I and 00EZ (blueprint: lem-trf-ph-etale-comparison-hypotheses). -/
abbrev BigEtaleSheaf (X : Scheme.{u}) :=
  Sheaf (Scheme.etaleTopology.over X) AddCommGrpCat.{u + 1}

/-- The category of abelian sheaves on the big ph site over `X`.
Source: Stacks, Tags 0F0I and 0DBL (blueprint: lem-trf-ph-etale-comparison-hypotheses). -/
abbrev BigPhSheaf (X : Scheme.{u}) :=
  Sheaf (Scheme.phTopology X) AddCommGrpCat.{u + 1}

/-- Membership in the subcategory `A'_X` of big étale sheaves coming from torsion
small-étale sheaves.  Source: Stacks, Tag 0F0I, condition (A)
(blueprint: lem-trf-ph-etale-comparison-hypotheses). -/
def IsEtaleOriginTorsion (X : Scheme.{u})
    (π : BigSmallEtaleRetractionData X)
    (H : BigEtaleSheaf X) : Prop :=
  ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
    F.IsTorsion ∧ Nonempty (H ≅ π.morphism.inverse.obj F)

/-- The weak-Serre closure conditions for `A'_X`.
Source: Stacks, Tag 0F0I, conditions (1)--(4)
(blueprint: lem-trf-ph-etale-comparison-hypotheses). -/
def IsWeakSerreOrigin (X : Scheme.{u})
    (π : BigSmallEtaleRetractionData X) : Prop :=
  (∃ Z : BigEtaleSheaf X, IsZero Z ∧ IsEtaleOriginTorsion X π Z) ∧
    (∀ {H K : BigEtaleSheaf X} (_e : H ≅ K),
      IsEtaleOriginTorsion X π H → IsEtaleOriginTorsion X π K) ∧
    (∀ {H K : BigEtaleSheaf X} (g : H ⟶ K),
      IsEtaleOriginTorsion X π H → IsEtaleOriginTorsion X π K →
        IsEtaleOriginTorsion X π (kernel g) ∧
        IsEtaleOriginTorsion X π (cokernel g)) ∧
    (∀ (Q : ShortComplex (BigEtaleSheaf X)), Q.ShortExact →
      IsEtaleOriginTorsion X π Q.X₁ → IsEtaleOriginTorsion X π Q.X₃ →
        IsEtaleOriginTorsion X π Q.X₂)

/- The following wrappers keep the continuity witnesses explicit in the statement.  This is
necessary because the site functors' sheaf transports take continuity as a typeclass argument. -/
/-- Canonical set-valued inverse image for the identity ph/étale comparison, with continuity
explicitly supplied. Source: Stacks, Tags 00XA and 0F0I. -/
noncomputable def phSetPullback (X : Scheme.{u})
    (h : (𝟭 (Over X)).IsContinuous (Scheme.etaleTopology.over X)
      (Scheme.phTopology X)) :
    Sheaf (Scheme.etaleTopology.over X) (Type (u + 1)) ⥤
      Sheaf (Scheme.phTopology X) (Type (u + 1)) := by
  letI := h
  exact (𝟭 (Over X)).sheafPullback (Type (u + 1))
    (Scheme.etaleTopology.over X) (Scheme.phTopology X)

/-- Canonical set-valued direct image for the identity ph/étale comparison. Source: Stacks,
Tags 00XA and 0F0I. -/
noncomputable def phSetPushforward (X : Scheme.{u})
    (h : (𝟭 (Over X)).IsContinuous (Scheme.etaleTopology.over X)
      (Scheme.phTopology X)) :
    Sheaf (Scheme.phTopology X) (Type (u + 1)) ⥤
      Sheaf (Scheme.etaleTopology.over X) (Type (u + 1)) := by
  letI := h
  exact (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.etaleTopology.over X) (Scheme.phTopology X)

/-- Canonical abelian inverse image for the identity ph/étale comparison. Source: Stacks,
Tags 00XA and 0F0I. -/
noncomputable def phAbPullback (X : Scheme.{u})
    (h : (𝟭 (Over X)).IsContinuous (Scheme.etaleTopology.over X)
      (Scheme.phTopology X)) : BigEtaleSheaf X ⥤ BigPhSheaf X := by
  letI := h
  exact (𝟭 (Over X)).sheafPullback AddCommGrpCat.{u + 1}
    (Scheme.etaleTopology.over X) (Scheme.phTopology X)

/-- Canonical abelian direct image for the identity ph/étale comparison. Source: Stacks,
Tags 00XA and 0F0I. -/
noncomputable def phAbPushforward (X : Scheme.{u})
    (h : (𝟭 (Over X)).IsContinuous (Scheme.etaleTopology.over X)
      (Scheme.phTopology X)) : BigPhSheaf X ⥤ BigEtaleSheaf X := by
  letI := h
  exact (𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.etaleTopology.over X) (Scheme.phTopology X)

/-- Canonical set-valued relocalization inverse image. Source: Stacks, Tags 00XA and 0F0I. -/
noncomputable def relocalizationSetPullback {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (h : (Over.map f.left).IsContinuous (Scheme.etaleTopology.over X.left)
      (Scheme.etaleTopology.over Y.left)) :
    Sheaf (Scheme.etaleTopology.over Y.left) (Type (u + 1)) ⥤
      Sheaf (Scheme.etaleTopology.over X.left) (Type (u + 1)) := by
  letI := h
  exact (Over.map f.left).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.etaleTopology.over X.left) (Scheme.etaleTopology.over Y.left)

/-- Canonical abelian relocalization inverse image. Source: Stacks, Tags 00XA and 0F0I. -/
noncomputable def relocalizationAbPullback {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (h : (Over.map f.left).IsContinuous (Scheme.etaleTopology.over X.left)
      (Scheme.etaleTopology.over Y.left)) :
    BigEtaleSheaf Y.left ⥤ BigEtaleSheaf X.left := by
  letI := h
  exact (Over.map f.left).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.etaleTopology.over X.left) (Scheme.etaleTopology.over Y.left)

/-- Data expressing the five hypotheses of the ph/étale comparison theorem.
Source: Stacks, Tag 0F0I, `lemma-compare-ph-etale`, and Sites, Tag 0EZ3
(blueprint: lem-trf-ph-etale-comparison-hypotheses). -/
structure PhEtaleComparisonData (S : Scheme.{u}) where
  /-- The canonical big-to-small étale retractions on all objects over `S`. -/
  pi : ∀ X : Over S, BigSmallEtaleRetractionData X.left
  /-- The étale topology is coarser than the ph topology. -/
  etale_le_ph : ∀ X : Over S,
    Scheme.etaleTopology.over X.left ≤ Scheme.phTopology X.left
  /-- Proper morphisms are stable under the canonical scheme pullbacks. -/
  base_change_P : ∀ {X Y : Over S} (f : X ⟶ Y), IsProper f.left →
    ∀ (Y' : Scheme) (g : Y' ⟶ Y.left),
      IsPullback (pullback.fst f.left g) (pullback.snd f.left g) f.left g ∧
        IsProper (pullback.snd f.left g)
  /-- The comparison geometric morphism has identity direct image on presheaves and
  ph-sheafification as inverse image. -/
  epsilon : ∀ X : Over S,
    ∃ h : (𝟭 (Over X.left)).IsContinuous (Scheme.etaleTopology.over X.left)
      (Scheme.phTopology X.left),
      ∃ e₀ : GeometricMorphism
          (Sheaf (Scheme.phTopology X.left) (Type (u + 1)))
          (Sheaf (Scheme.etaleTopology.over X.left) (Type (u + 1))),
        ∃ e₁ : GeometricMorphism (BigPhSheaf X.left) (BigEtaleSheaf X.left),
        e₀.inverse = phSetPullback X.left h ∧
        e₀.direct = phSetPushforward X.left h ∧
        e₁.inverse = phAbPullback X.left h ∧
        e₁.direct = phAbPushforward X.left h ∧
        Nonempty (e₁.direct ⋙ sheafToPresheaf (Scheme.etaleTopology.over X.left)
            AddCommGrpCat.{u + 1} ≅
          sheafToPresheaf (Scheme.phTopology X.left) AddCommGrpCat.{u + 1}) ∧
        Nonempty (e₁.inverse ≅
          sheafToPresheaf (Scheme.etaleTopology.over X.left) AddCommGrpCat.{u + 1} ⋙
            presheafToSheaf (Scheme.phTopology X.left) AddCommGrpCat.{u + 1})
  /-- The relocalization geometric morphisms on big étale sites. -/
  relocalization : ∀ {X Y : Over S} (f : X ⟶ Y),
    ∃ h : (Over.map f.left).IsContinuous (Scheme.etaleTopology.over X.left)
      (Scheme.etaleTopology.over Y.left),
      ∃ e₀ : GeometricMorphism
          (Sheaf (Scheme.etaleTopology.over X.left) (Type (u + 1)))
          (Sheaf (Scheme.etaleTopology.over Y.left) (Type (u + 1))),
        ∃ e₁ : GeometricMorphism (BigEtaleSheaf X.left) (BigEtaleSheaf Y.left),
        e₀.inverse = relocalizationSetPullback f h ∧
        e₁.inverse = relocalizationAbPullback f h
  /-- The subcategories `A'_X` are weak Serre subcategories. -/
  weak_serre : ∀ X : Over S, IsWeakSerreOrigin X.left (pi X)
  /-- Restriction along any morphism over `S` preserves `A'`. -/
  restriction_A : ∀ {X Y : Over S} (f : X ⟶ Y)
      (e : GeometricMorphism (BigEtaleSheaf X.left) (BigEtaleSheaf Y.left)),
      e.inverse =
        (Over.map f.left).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (Scheme.etaleTopology.over X.left) (Scheme.etaleTopology.over Y.left) →
      ∀ H : BigEtaleSheaf Y.left,
        IsEtaleOriginTorsion Y.left (pi Y) H →
        IsEtaleOriginTorsion X.left (pi X) (e.inverse.obj H)
  /-- Origin torsion sheaves satisfy the ph sheaf condition. -/
  A_sheaf : ∀ X : Over S, ∀ H : BigEtaleSheaf X.left,
      IsEtaleOriginTorsion X.left (pi X) H →
      ∀ {U : Over X.left} (R : Presieve U),
        Sieve.generate R ∈ Scheme.phTopology X.left U →
        Presieve.IsSheafFor
          (H.obj ⋙ (CategoryTheory.forget AddCommGrpCat)) R
  /-- Proper direct images preserve `A'` in every ordinary right-derived degree. -/
  A_and_P : ∀ {X Y : Over S} (f : X ⟶ Y)
      (_hf : IsProper f.left),
      ∃ hres : HasInjectiveResolutions (BigEtaleSheaf X.left),
        ∃ e : GeometricMorphism (BigEtaleSheaf X.left) (BigEtaleSheaf Y.left),
          e.inverse =
            (Over.map f.left).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (Scheme.etaleTopology.over X.left) (Scheme.etaleTopology.over Y.left) ∧
          ∃ hadd : e.direct.Additive,
            ∀ H : BigEtaleSheaf X.left, IsEtaleOriginTorsion X.left (pi X) H →
              ∀ i : ℕ,
                IsEtaleOriginTorsion Y.left (pi Y)
                  ((@Functor.rightDerived (BigEtaleSheaf X.left) _ (BigEtaleSheaf Y.left) _
                    (by infer_instance) hres (by infer_instance) e.direct hadd i).obj H)
  /-- Every ph covering admits the specified étale/proper/étale refinement. -/
  refine_tau_by_P : ∀ {X : Over S} {I : Type (u + 1)}
      (U : I → Over X.left) (a : ∀ i, U i ⟶ Over.mk (𝟙 X.left)),
      Sieve.generate (Presieve.ofArrows U a) ∈ Scheme.phTopology X.left (Over.mk (𝟙 X.left)) →
      ∃ (J : Type (u + 1)) (K : J → Type (u + 1))
        (V : J → Over X.left) (v : ∀ j, V j ⟶ Over.mk (𝟙 X.left))
        (W : J → Over X.left) (q : ∀ j, W j ⟶ V j)
        (W' : ∀ j, K j → Over X.left)
        (r : ∀ (j : J) (k : K j), W' j k ⟶ W j),
        Sieve.generate (Presieve.ofArrows V v) ∈
          Scheme.etaleTopology.over X.left (Over.mk (𝟙 X.left)) ∧
        (∀ j, IsProper (q j).left ∧ Function.Surjective (q j).left ∧
          Sieve.generate (Presieve.singleton (q j)) ∈ Scheme.phTopology X.left (V j)) ∧
        (∀ j, Sieve.generate (Presieve.ofArrows (W' j) (r j)) ∈
          Scheme.etaleTopology.over X.left (W j)) ∧
        (∀ (j : J) (k : K j), ∃ i : I, ∃ h : W' j k ⟶ U i,
          h ≫ a i = r j k ≫ q j ≫ v j)

/-- The proper morphism and torsion étale-sheaf hypotheses of Stacks Tag 0F0I.

Source: Stacks Project, Étale Cohomology, Tag 0F0I, `lemma-compare-ph-etale`,
and Sites, Tag 0EZ3. (blueprint: lem-trf-ph-etale-comparison-hypotheses)

Proof plan (the nine DAG proof steps):

1. First record explicitly that torsion small etale sheaves contain zero and are closed under
kernels, cokernels and extensions. A section of a kernel is a section of the source, so its local
annihilator also annihilates it in the kernel. A section of a cokernel locally lifts to the target
of the original map, since an epimorphism of abelian sheaves is locally surjective; a local
annihilator of that lift kills its image. For an extension $0\to F\to E\to F'\to0$ and $e\in
E(U)$, first refine $U$ until an integer $n>0$ kills the image of $e$ in $F'$. Then $ne$ is a
section of the kernel, identified with $F$; refine again and choose $m>0$ killing this section.
Thus $mn$ kills $e$. These coverings and integers may depend on the section; no uniform bound is
used. Closure under isomorphism is immediate from the same definition.

2. Fix $X$ and put $L=\pi_X^{-1}$ and $R=\pi_{X,*}$. Both are exact: $L$ by exactness of inverse
image for a morphism of sites, and $R$ by the exact-retraction lemma. The latter also gives the
unit $F\xrightarrow{\sim}RL F$. The adjunction therefore identifies $\operatorname{Hom}(LF,LF')$
with $\operatorname{Hom}(F,RL F')=\operatorname{Hom}(F,F')$. Every morphism between objects of
$\mathcal A'_X$ consequently comes, after their chosen isomorphisms, from a small-etale morphism
$u:F\to F'$. Exactness gives $\ker(Lu)=L\ker(u)$ and
$\operatorname{coker}(Lu)=L\operatorname{coker}(u)$. Step 1 shows the small sheaves on the right
are torsion. Exactness also sends zero to zero. This proves zero, isomorphism, kernel and cokernel
closure.

3. Given $0\to LF\to H\to LF'\to0$ with $F,F'$ torsion, exact $R$ and the unit isomorphisms give
$0\to F\to RH\to F'\to0$. Step 1 makes $RH$ torsion. Apply exact $L$ to this row, and map the
resulting short exact sequence to the original one using the adjunction counit $LR\to\mathrm{id}$.
Naturality gives the commutative diagram. Its endpoint maps $LRLF\to LF$ and $LRLF'\to LF'$ are
isomorphisms: by the triangle identity they are inverse to $L$ applied to the respective unit
isomorphisms. The short five lemma now makes the middle counit $LRH\to H$ an isomorphism. Thus
$H\cong L(RH)$ lies in $\mathcal A'_X$, proving extension closure and the weak Serre assertion.

4. For a proper $f:X\to Y$ and arbitrary $Y'\to Y$, the fibre product $X\times_Y Y'$ exists by the
scheme fibre-product statement. Properness is stable under this base change, by the cited
proper-base-change lemma. The induced structure map to $S$ makes the fibre product an object of
$\mathrm{Sch}/S$. This is property (1).

5. For $H'\cong\pi_Y^{-1}F$, the small/big pullback formula gives
$f_{\mathrm{Et}}^{-1}H'\cong\pi_X^{-1}f_s^{-1}F$ for every $f:X\to Y$. The small pullback
$f_s^{-1}F$ is torsion: at each geometric point its stalk is a stalk of $F$, by the inverse-image
stalk isomorphism. The local definition of torsion is equivalent to every stalk element having a
positive annihilator: one implication takes germs; for the other, represent a germ by a section
and shrink its pointed etale neighbourhood until the annihilating equality holds, then let the
geometric point vary. The resulting etale neighbourhoods cover. This proves (2), with no
restriction on $f$.

6. Let $H=\pi_X^{-1}F$, and let $a:U\to X$ and $p:V\to U$ be any proper surjection. Set
$G=a_s^{-1}F$ on $U_{\mathrm{Et}}$. Evaluation of $H$ identifies $H(U)$, $H(V)$ and
$H(V\times_UV)$ with the sections of $G$, $p_s^{-1}G$ and $q_s^{-1}G$, respectively, where
$q:V\times_UV\to U$. Naturality in that formula identifies both arrows with pullback along the two
projections. The proper-surjection section-equalizer lemma therefore proves that $H(U)\to
H(V)\rightrightarrows H(V\times_UV)$ is an equalizer. This uses no torsion hypothesis on $F$.

7. We verify ph gluing rather than treating a tag as a proof. The affine standard-sieve basis also
says etale coverings are ph, which is the asserted topology comparison. (a) Separatedness for
every ph covering $\{Y_l\to Y\}$ of every object $Y$: choose an affine open cover $\{Y'_j\to Y\}$;
by the basis lemma the pulled-back sieve on $Y'_j$ contains a proper surjection $W'_j\to Y'_j$
with a finite affine open cover $\{W'_{jk}\}$ whose members factor through some $Y_l$. A section
of $H(Y)$ restricting to zero on all $Y_l$ restricts to zero on all $W'_{jk}$, hence on $W'_j$
(Zariski separatedness), hence on $Y'_j$ (injectivity in Step 6), hence on $Y$. (b) Let $\{U_i\to
U\}$ be ph covering and $s_i\in H(U_i)$ matching. Choose an affine open cover $\{V_j\to U\}$ and,
as in (a), $W_j\to V_j$ proper surjective with finite affine open cover $\{W_{jk}\}$ and maps
$W_{jk}\to U_{i(k)}$ over $U$. The pullbacks $s_{i(k)}|_{W_{jk}}$ agree on $W_{jk}\cap W_{jl}$,
which maps to $U_{i(k)}\times_UU_{i(l)}$; the etale sheaf condition glues them to $t_j\in H(W_j)$.
Its two pullbacks to $W_j\times_{V_j}W_j$ agree on each open $W_{jk}\times_{V_j}W_{jl}$ by the
same matching, hence agree. Step 6 descends $t_j$ to $v_j\in H(V_j)$. (c) $v_j=s_i$ on
$Y=U_i\times_UV_j$: the family $\{W_{jk}\times_UU_i\to Y\}_k$ is a ph covering (base change of the
composite covering $\{W_{jk}\to V_j\}$, site axioms), and on $W_{jk}\times_UU_i$ both sections are
pullbacks of $s_{i(k)}$ and $s_i$, which match; apply (a). (d) On $V_j\times_UV_{j'}$, $v_j$ and
$v_{j'}$ both restrict to $s_i$ on the ph covering by the $U_i\times_UV_j\times_UV_{j'}$, by (c);
so they agree by (a), and glue to $v\in H(U)$. By (c), $v|_{U_i}$ and $s_i$ agree on the Zariski
cover $\{U_i\times_UV_j\}_j$, so $v|_{U_i}=s_i$; uniqueness is (a). Thus $H$ is a ph sheaf, and so
is every presheaf isomorphic to it, giving (3).

8. For proper $f:X\to Y$ and $H'\cong\pi_X^{-1}F$ with $F$ torsion, apply the proper derived
small/big comparison to $K=F[0]$. Taking degree $i$ gives
$$R^if_{\mathrm{Et},*}H'\cong\pi_Y^{-1}(R^if_{s,*}F).$$ Indeed $\pi_Y^{-1}$ is exact, so it
preserves the kernels, images and cokernels in the formula $H^i=\ker
d^i/\operatorname{im}d^{i-1}$. The degree-$i$ cohomology of a derived direct image of $F[0]$ is
its ordinary $R^i$, by definition. A proper map is quasi-compact because it is of finite type, and
quasi-separated because it is separated. Apply the existing qcqs higher-image theorem with the set
of all primes. Its input is exactly elementwise torsion of the geometric stalks of $F$, equivalent
to the local torsion definition by the germ argument of Step 5; its output says that $R^if_{s,*}F$
is torsion. Therefore the displayed big sheaf lies in $\mathcal A'_Y$ for every $i\geq0$. This is
(4), including $i=0$.

9. For (5), take an affine open cover $\{V_j\to U\}$. Pull back the sieve generated by the given
ph covering to each $V_j$. The affine standard-sieve basis supplies a proper surjection $W_j\to
V_j$ and a finite affine open covering $\{W_{jk}\to W_j\}$ whose composites belong to that sieve.
Membership means precisely that the composite $W_{jk}\to U$ factors through one of the original
$U_i$; thus the required refinement maps exist. Both open covers are etale by the basis lemma.
Each singleton $\{W_j\to V_j\}$ is ph covering directly from the generating definition of the ph
topology, and its arrow is proper. Composition of these three covering levels is a covering, by
the site axioms. The chosen presentations and basis lemma make all index sets small; $J$ need not
be finite. For empty $U$ one may take $J=\varnothing$. This proves all of (5).

The big étale abelian-sheaf categories admit injective resolutions; direct image is
additive as a right adjoint between abelian categories. Supply these witnesses in
`A_and_P`, then assemble the comparison, retraction, and five-property fields.
-/
theorem phEtaleComparisonHypotheses (S : Scheme.{u}) :
    Nonempty (PhEtaleComparisonData S) := by
  sorry

end AlgebraicGeometry
