/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.PolynomialDualityAffineCompatibility
import WeilConjectures.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.ZariskiLocalDualityAdjunction
import Sheaf.AlgebraicGeometry.RelativeDualizingPairOpenRigidity
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.RingTheory.ColimitFlatRingMap
import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalClass
import Sheaf.AlgebraicGeometry.RelativeDualizingPairBaseChange
import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentBaseChange
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Proper flat duality and normalized polynomial models over arbitrary bases

Source: Stacks Project, duality.tex, Tags 0E2X, 0E4P and 0BV2;
dualizing.tex, Tag 0BZJ, with its top-differential normalization.
(blueprint: lem-sfb-proper-flat-dualizing-polynomial-model).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- For a proper flat finitely presented morphism over any scheme, unbounded
quasi-coherent derived direct image has a right adjoint. Its value on the structure
sheaf underlies a coherent relative dualizing pair, with a single atlas of normalized
polynomial models. Each affine presentation system realizes that same atlas, including
principal-open restrictions. Its refinement and coordinate fields retain the ordered
Koszul contraction, exterior signs and cohomological signs. Comparisons through their
common intrinsic object satisfy the composition cocycle.

The existential proof hO merely places the actual derived tensor unit in D_QCoh(S);
it is part of the conclusion. The equation for K identifies it with fshriek(O_S).
Properness supplies quasi-compactness and quasi-separatedness, so local finite
presentation here is equivalent to finite presentation. There is no Noetherian,
Cohen--Macaulay, lci, dimension, concentration or invertibility hypothesis.

Source: Stacks Project, duality.tex, 0E2X, 0E4P, 0BV2; dualizing.tex, 0BZJ.
(blueprint: lem-sfb-proper-flat-dualizing-polynomial-model).

Proof:
1. Apply the space trace-duality theorem to the schemes $X,S$, viewed as algebraic spaces over
$S$, and transport it to Zariski quasi-coherent derived categories by the site comparison. This
supplies $K\in D_{\mathrm{QCoh}}(X)$ and $\tau:Rf_*K\to\mathcal O_S$. Over each affine $V\subset
S$, its restriction is identified, with its trace, with $a_V(\mathcal O_V)$ for the right
adjoint $a_V$ of $Rf_{V,*}$. Indeed $X_V$ is qcqs since it is proper over affine $V$, so the
qcqs adjoint theorem applies. The trace characterization and Yoneda fix the identification,
including its scalar normalization. No assertion about a global adjoint has yet been used.
Uses: lem-sfb-proper-flat-space-derived-duality, lem-sfb-derived-etale-zariski-equivalence,
lem-pc-qcqs-derived-direct-image-right-adjoint.
2. For $M\in D_{\mathrm{QCoh}}(S)$ define $G(M)=Lf^*M\otimes^{\mathbf L}K$ with trace-defined
counit. On every affine base $V$ the tensor formula identifies this functor with $a_V$, with
precisely that counit. The local adjunction criterion now gives $Rf_*\dashv G$ globally. Choose
$f^!=G$. Its value on $\mathcal O_S$ is canonically $K$ by the tensor unit, so the notation
$K_f$ is justified even when $S$ has no finite affine cover.
Uses: lem-sfb-proper-flat-adjoint-tensor-formula, lem-sfb-zariski-local-duality-adjunction.
3. Over every affine base $V$, the proper-adjoint diagonal theorem supplies the pair on $X_V/V$.
Its class is preserved on qcqs base-open overlaps, by that theorem's base-change clause and the
trace-normalized identifications of step 1. To compare two affine bases, cover their
intersection by affine opens; restriction and rigidity identify the classes there. Thus these
classes are compatible. For $Y=X\times_SX$ put $D=\Delta_*\mathcal O_X$ and $H=R\mathcal
Hom_Y(D,Lp_1^*K)$. On $X_V\times_VX_V$, $H$ is $D[0]$. These self-products already cover $Y$:
every point has a common image in $S$ lying in some affine $V$. Off the closed diagonal $H$ is
zero. Thus so $H$ has only degree-zero cohomology. The compatible classes are sections of that
sheaf (by the derived-Hom global-sections identification); they glue with zero off the diagonal.
The resulting section gives $\xi_f:D\to Lp_1^*K$, whose multiplication map is an isomorphism
locally and hence globally. Pseudo-coherence and relative finite Tor amplitude are local and
hold on all $X_V$. This constructs the intrinsic coherent pair $(K_f,\xi_f)$ on all of $Y$.
Uses: lem-sfb-proper-adjoint-diagonal-pair, lem-sfb-relative-dualizing-pair-open-rigidity,
lem-sc-derived-internal-hom-restrict-open, lem-pur-rhom-global-sections,
def-trf-coherent-relative-dualizing-pair.
4. Fix $U=\operatorname{Spec}B\subset f^{-1}(V)$, $V=\operatorname{Spec}R$. The affine criteria
give $R\to B$ flat of finite presentation. For the chosen surjection $P=R[t_1,\ldots,t_n]\to B$,
its kernel is finitely generated. Write finitely many generators as polynomials. In the directed
system of finitely generated $\mathbf Z$-subalgebras of $R$, include their coefficients and form
the same quotient $B_0$ of $P_0=R_0[t_1,\ldots,t_n]$. Its base change is $B$. The
eventual-flatness theorem permits increasing $R_0$ until $B_0/R_0$ is flat. These rings are
Noetherian; the selected presentation, not just the abstract algebra $B$, has descended. The
same construction descends any finite collection of refinement lifts and polynomial identities
used below.
Uses: lem-weil-pbc-flat-morphism-affine-criterion,
lem-weil-pbc-lfp-affine-opens-finite-presentation,
lem-weil-pbc-finite-presentation-surjection-kernel-fg,
lemma-nagata-noetherian-inverse-system-affine, lem-weil-pbc-colimit-flat-ring-map,
lem-weil-pbc-finite-type-algebra-noetherian.
5. At the Noetherian stage the chart theorem gives a relative pair with underlying sheaf model
$R\mathcal Hom_{P_0}(i_*\mathcal O_{U_0},\Omega^n[n])$. The affine algebra-class evaluation
comparison applies: $B_0$ is perfect over $P_0$ by the flat-polynomial-quotient theorem, hence
pseudo-coherent, and the coefficient line in degree $-n$ is bounded below. It identifies that
sheaf Hom with the sheafification of $C_0=C_{B_0}^{P_0}(\Omega^n[n])$, respecting evaluation and
every $B_0$-multiplication action. The affine-morphism derived equivalence realizes its
$B_0$-action on $U_0$. Equip $C_0$ with the specified class $\xi_{P_0}$ of the Koszul-diagonal
lemma, rather than an arbitrary chart class. Multiplication by this class is invertible by that
lemma. Its sheaf realization is therefore a coherent pair: the finiteness conditions concern the
underlying object, supplied by the chart theorem. Pull this pair back along $R_0\to R$. Since
$B_0/R_0$ is flat, $$B_0\otimes^{\mathbf L}_{P_0}P=B_0\otimes^{\mathbf L}_{R_0}R=B.$$ Perfect
Tor-independent coinduction base change identifies its object with
$C_P=C_B^P(\Omega^n_{P/R}[n])$ in $D(B)$. Affine pullback realizes the pair geometrically.
Ordered volume forms extend to the same volume.
Uses: lem-trf-relative-duality-polynomial-chart, lem-trf-flat-polynomial-quotient-perfect,
lem-trf-affine-algebra-class-evaluation-comparison, lem-sc-finite-affine-derived-equivalence,
lem-sfb-polynomial-koszul-diagonal-class, lem-sfb-relative-dualizing-pair-base-change,
lem-sfb-perfect-coinduction-tor-independent-base-change,
lem-pc-affine-derived-pullback-tensor-tilde.
6. First fix the class on the actual object $C_P$. For two coefficient stages of the same chosen
presentation, enlarge to a common finitely generated $\mathbf Z$-subalgebra of $R$. Include the
finite coefficients expressing each stage's defining equations in the ideal generated by the
other's equations; such expressions exist after mapping to $R$, and involve finitely many
coefficients. The extended presentation ideals then agree. Eventual flatness gives a common flat
stage. These stage rings are Noetherian, so the scalar-extension clause of the Koszul-diagonal
lemma applies to both transitions, even if nonflat. It identifies both classes with the same
graph-defined class at that common stage. Successive-extension compatibility of perfect
coinduction makes their further images equal as maps $B\to C_P\otimes_{B,p_1}^{\mathbf
L}(B\otimes_RB)$. Denote this stage-independent class by $\xi_P$. Only now restrict
$(K_f,\xi_f)$ to $U/V$ and apply supplied-pair rigidity, giving a unique isomorphism
$(K_f|_U,\xi_f|_U)\simeq(C_P,\xi_P)$. Under affine derived equivalence this is the required
canonical object comparison. The coinduction definition specifies its $B$-action
$(bh)(b')=h(b'b)$. Uniqueness of pair isomorphisms is used after equality of polynomial classes,
not to infer their equality.
Uses: lem-sfb-polynomial-koszul-diagonal-class, lemma-nagata-noetherian-inverse-system-affine,
lem-weil-pbc-colimit-flat-ring-map, lem-sfb-perfect-coinduction-tor-independent-base-change,
lem-sfb-relative-dualizing-pair-open-rigidity, lem-pc-affine-qcoh-derived-equivalence,
def-trf-derived-coinduction.
7. For a refinement adjoining $t$ with image $\bar a$, descend $a\in P$ and both presentations
to a common flat Noetherian stage as in step 4. The Koszul-diagonal lemma says that its
specified contraction for $t-a$ sends $\xi_{Q_0}$ to $\xi_{P_0}$; this concerns the actual
graph-defined classes. Extend this equality to $R$. Perfect coinduction base change preserves
the evaluation counits, so the arrow on polynomial objects is the prescribed contraction
$\operatorname{dual}(t-a)\otimes d(t-a)\mapsto1$. It sends $\xi_Q$ to $\xi_P$ by step 6. For
several coordinates use the ordered tensor evaluations with their exterior and cohomological
signs. For a principal source restriction descend a lift $h\in P$ of the inverted element and
use the Koszul-diagonal lemma's localization clause at that stage. For a base restriction use
its base-localization clause. These maps also preserve the specified classes after extension.
Check general affine-open restrictions on principal subopens of source and base; for a fresh
polynomial presentation pass to a common polynomial refinement there. No regularity of the
original defining ideal is used.
Uses: lem-sfb-polynomial-koszul-diagonal-class,
lem-sfb-perfect-coinduction-tor-independent-base-change.
8. Compare models through their unique class-preserving identifications with the intrinsic pair,
restricting that pair first on smaller opens. Direct and composite maps preserve the same fixed
classes $\xi_P$, so rigidity equates them. The concrete refinement and restriction maps of step
7 preserve these classes and therefore are exactly these comparisons, without an undetermined
unit. Any two finite presentations have a common refinement with both sets of variables,
choosing lifts of the extra images by surjectivity. Equality on principal subopens implies
equality on arbitrary affine restrictions by uniqueness after open restriction. This proves
identity, composition and overlap cocycles, including across different affine base opens. Empty
charts give zero objects and unique maps. For $n=0$, $\Omega^0_{R/R}=R$ and the shift is zero.
No dimension bound, concentration, or invertibility is asserted.
Uses: lem-sfb-relative-dualizing-pair-open-rigidity.
-/
theorem exists_properFlatDualizingPolynomialModel
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    ∃ hO : schemeDerivedQCohProperty S (𝟙_ (schemeDerivedCategory S)),
    ∃ hpres : ∀ E : schemeDerivedCategory X,
      schemeDerivedQCohProperty X E →
        schemeDerivedQCohProperty S ((schemeDerivedDirectImage f).obj E),
    ∃ (fshriek : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
      (K : schemeDerivedQCohCategory X),
      Nonempty (((schemeDerivedQCohProperty S).lift
        ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
        (fun E ↦ hpres E.obj E.property)) ⊣ fshriek) ∧
      K = fshriek.obj ⟨𝟙_ (schemeDerivedCategory S), hO⟩ ∧
      ∃ ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
          (derivedPullback (pullback.fst f f)).obj K.obj,
        IsCoherentRelativeDualizingPair f K.obj ξ ∧
        ∃ atlas : PolynomialDualityChartAtlas f K.obj,
        ∀ (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
          (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
          [IsOpenImmersion jB] [IsOpenImmersion jR],
          jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR →
          ∃ (M : DerivedCategory (ModuleCat.{u} B))
            (e : (polynomialOpenRestriction jB).obj K.obj ≅ (polynomialAffineTilde B).obj M)
            (F : PolynomialDualityPresentationSystem R B (algebraMap R B) M),
            IsPolynomialAffineAtlasCompatible atlas R B jB jR M e F ∧
            IsPolynomialLocalizedAffineAtlasCompatible atlas R B jB jR M e F := by
  sorry

end AlgebraicGeometry
