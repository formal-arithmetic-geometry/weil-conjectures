/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionData
import Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
import Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension
import Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion
import Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages
import Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine

/-!
# Prime coefficients in proper smooth curve families

Source: Stacks Project, more-etale.tex, Tag 0GKV, lemma-proper-smooth-family-curves,
the Noetherian case (blueprint: lem-weil-pbc-proper-smooth-curves-prime-coefficients).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- In a proper smooth family with nonempty geometrically connected one-dimensional
fibres over a Noetherian base, every nonnegative higher direct image of the constant
prime-field module sheaf is constructible. No invertibility of the prime is assumed.
`GeometricallyConnected f` includes nonemptiness. Dimension is measured on residue-field
fibres; field extension preserves their dimension, so this is the geometric fibre condition.
The lift of `ZMod ell` places the same finite prime field in the coefficient universe.

Source: Stacks Project, more-etale.tex, Tag 0GKV, lemma-proper-smooth-family-curves.
(blueprint: lem-weil-pbc-proper-smooth-curves-prime-coefficients)

Proof plan:

1. Put $G_q=R^qf_*\underline{\mathbf F_\ell}$ in module sheaves and
$A_q=\operatorname{For}(G_q)$. Coefficient forgetting identifies $A_q$ with the abelian higher
direct image. At each geometric point $\bar s$, proper base change identifies its stalk with
$H^q(C_{\bar s},\mathbf F_\ell)$; inverse image preserves the constant sheaf. The fibre is a
smooth proper connected curve over an algebraically closed field, by proper and smooth base-
change permanence and the given geometric fibre hypotheses. The curve-finiteness lemma makes
these stalks finite for every prime $\ell$, including the residue characteristic.
Uses: lem-weil-pbc-exchange-forget-coefficients, cor-weil-pbc-geometric-fiber-finite, lemma-
constructible-pullback-constant, lem-sc-c5, lem-weil-pbc-proper-base-change, lem-sbc-smooth-
relative-dimension-permanence.

2. Let $U=D(\ell)\subset S$ and $Z=V(\ell)\hookrightarrow S$ with its closed subscheme
structure. Prime proper base change along both inclusions identifies the restrictions of $A_q$
with the higher direct images of the constant sheaf on $C_U$ and $C_Z$; coefficient comparison
gives the module identifications for $G_q$. Properness and smooth relative dimension one persist
under base change. The geometric fibres are the given fibres after an algebraically closed field
extension, so remain nonempty geometrically connected curves. Both bases are Noetherian. A
finite constructible module stratification on each piece gives one on $S$ by concatenation:
every locally closed constructible subset of either piece is locally closed and constructible in
the Noetherian $S$, and its immersion into the piece composes with that piece's inclusion by
clause (e) of [lem-weil-pbc-proper-fp-permanence]. Thus it suffices to treat the two pieces.
Empty pieces are permitted. More explicitly, $U$ is locally Noetherian by the open-subscheme
clause of [pqf-def-locnoeth], and it is quasi-compact because every open in a Noetherian
topological space is quasi-compact. By [pqf-lem-affine-open-locnoeth], every affine open
$\operatorname{Spec}A$ of $S$ has Noetherian coordinate ring $A$. On such an affine open, the
corresponding closed piece is $\operatorname{Spec}(A/(\ell))$, which is Noetherian: any
ascending chain of ideals in the quotient pulls back to an ascending chain of ideals of $A$ and
stabilizes. The closed piece is quasi-compact as a closed subset of the Noetherian underlying
space. To justify the topological Noetherian assertions, choose a finite affine open cover of
$S$. Each affine has Noetherian underlying space by [lem-sc-affine-noetherian-underlying-space];
an ascending chain of opens stabilizes on each member, hence on their finite union. In such a
space every open covering of an open has a finite subcover: the finite unions of its members
have a maximal member, which must contain them all. For the quotient-ring check, the ascending-
chain condition follows directly from finite generation: the union of a chain is an ideal, and
its finite generators lie in one member.
Uses: lemma-weil-pbc-prime-proper-base-change, lem-weil-pbc-exchange-forget-coefficients, lemma-
constructible-pullback-constant, lem-weil-pbc-proper-base-change, lem-sbc-smooth-relative-
dimension-permanence, def-pc-geometrically-irreducible, pqf-def-locnoeth, def-weil-
constructible-subset, def-weil-pbc-etale-constructible-sheaf, lem-sc-affine-noetherian-
underlying-space, pqf-lem-affine-open-locnoeth, lem-weil-pbc-proper-fp-permanence.

3. On $U$, the input is locally constant and $\ell$ is invertible. The specialization-invariance
lemma gives bijective specialization maps in every degree. Coefficient comparison gives the same
bijections on module stalks, and Step 1 gives finite stalks. Apply the finite-stalk
specialization criterion to the Noetherian $U$ and the finite ring $\mathbf F_\ell$. Hence
$G_q|_U$ is finite locally constant. The one-piece stratum proves its constructibility.
Uses: lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic, lem-weil-pbc-etale-
finite-stalk-specialization-criterion, lem-weil-pbc-exchange-forget-coefficients, def-weil-pbc-
etale-constructible-sheaf.

4. On $Z$, put $p=\ell$; $p\cdot1=0$ in its structure sheaf, including if $Z$ is nonreduced. For
$q\geq2$, the proper fibre formula and characteristic-$p$ curve vanishing give zero stalks of
$A_q|_Z$. Stalk conservativity makes it the zero sheaf. For $q=0$, apply the flat quasi-compact
connected-fibre sections lemma to $C_Z\times_ZV\to V$ for every etale object $V\to Z$. The
smooth-flat lemma gives flatness, and smooth/proper permanence applies to each of these base
changes. Smooth implies flat and proper implies quasi-compact, and these hypotheses persist on
base change; its fibres remain the nonempty connected geometric fibres in question. The
resulting bijections are the pullback maps on sections of the constant sheaf and commute with
restrictions, giving $f_{Z,*}\underline{\mathbf F_p}\cong\underline{\mathbf F_p}$. Coefficient
forgetting reflects the isomorphisms. Degree zero and degrees at least two are therefore
constructible with one stratum.
Uses: lem-sc-artin-schreier-dimension, cor-weil-pbc-geometric-fiber-finite, lemma-weil-pbc-
geometric-stalk-conservative, lem-weil-pbc-etale-sections-flat-qc-connected-fibres, lemma-
constructible-pullback-constant, def-sbc-smooth-morphisms, def-weil-proper-morphism, lem-weil-
pbc-exchange-forget-coefficients, def-weil-pbc-etale-constructible-sheaf, lem-pc-smooth-flat,
lem-weil-pbc-proper-base-change, lem-sbc-smooth-relative-dimension-permanence.

5. For degree one on $Z$, the scheme Artin--Schreier section-data and exactness lemmas on $C_Z$
give $0\to\underline{\mathbf F_p}\to\mathcal O_{C_Z,\mathrm{et}}\xrightarrow{F-1}\mathcal
O_{C_Z,\mathrm{et}}\to0$, where $F=\wp+1$ is sectionwise $p$-th power. Use the same lifted
associated structure sheaf as in the section-data lemma and the structure-direct-image input, so
no coefficient-universe change occurs. Abelian direct image is additive left exact, and abelian
sheaves have enough injectives. Its right derived delta-functor gives an exact segment, hence
the short exact sequence $$0\to\operatorname{Coker}(F-1:f_{Z,*}\mathcal O_{C_Z,\mathrm{et}}\to
f_{Z,*}\mathcal O_{C_Z,\mathrm{et}})\to A_1|_Z\to\operatorname{Ker}(F-1:R^1f_{Z,*}\mathcal
O_{C_Z,\mathrm{et}}\to R^1f_{Z,*}\mathcal O_{C_Z,\mathrm{et}})\to0.$$ Exactness at the two
adjacent terms identifies the image of the connecting map with that cokernel, and the image of
its successor with that kernel. This is in abelian sheaves; it does not assert finite prime-
field dimension of the structure sheaf.
Uses: lem-sc-artin-schreier-scheme-section-data, lem-sc-artin-schreier-scheme-section-exact,
lem-weil-pbc-direct-image-left-exact, lem-weil-pbc-site-sheaves-enough-injectives, lem-weil-pbc-
right-derived-universal-delta-functor.

6. The structure-direct-image lemma identifies the first repeated term with $\mathcal
O_{Z,\mathrm{et}}$ and the second with $E_{\mathrm{et}}$ for a finite locally free module $E$.
On the first term $F$ is $p$-th power. Use the higher-direct-image presheaf lemma to express the
second term as the sheafification of $V\mapsto H^1(C_Z\times_ZV,\mathcal O_{C_Z,\mathrm{et}})$.
On the second term $F$ is Frobenius-semilinear: on every etale base object and for every base
section $a$, the sectionwise identity $F\circ m_{f^*a}=m_{f^*(a^p)}\circ F$ induces the same
identity on cohomology by functoriality. The natural scalar action specified in the structure-
direct-image lemma is the action of these multiplication maps. Thus $F(ae)=a^pF(e)$. For a
morphism $W\to V$ of etale base objects, pullback sends $a$ to $a|_W$, sends $a^p$ to
$(a|_W)^p$, and sends the sectionwise $p$-th-power map to the same map over $W$. The cohomology
restriction maps therefore respect the displayed identity. A section of the associated sheaf is
locally represented by a presheaf section, so the identity holds locally for every section and
hence holds in the sheaf. Apply the Frobenius vector-bundle lemma to $\mathcal O_Z$ and to $E$.
The first application makes the cokernel zero; the second makes the kernel constructible as an
abelian sheaf. The exact segment then identifies $A_1|_Z$ with that kernel.
Uses: lem-weil-pbc-smooth-curve-etale-structure-direct-images, lem-weil-pbc-frobenius-vector-
bundle-kernel, lem-sc-artin-schreier-scheme-section-data, def-weil-pbc-direct-image, sbc-lem-
higher-direct-image-presheaf.

7. On each finite abelian constant stratum of $A_1|_Z$, choose its additive constant charts with
values $B$. Each element of $B$ is killed by $p$: on a nonempty chart read $pG_1=0$ at a
geometric stalk, identified with $B$ by the constant-stalk lemma. Empty charts may be omitted.
Give $B$ the forced $\mathbf F_p$-action $(a\bmod p)b=ab$, with the right side repeated
addition. Every additive chart map commutes with this action, since every element of $\mathbf
F_p$ is an integer multiple of $1$. Thus the same charts are finite constant module charts.
Coefficient forgetting commutes with the inverse images on strata, so $G_1|_Z$ is constructible
in the module sense. Step 4 treats the other degrees on $Z$, and Step 3 treats every degree on
$U$. Concatenate their finite stratifications as in Step 2. This proves every $q\geq0$ on $S$
without requiring invertibility of $\ell$; zero sheaves and empty pieces cause no exception.
Uses: def-weil-pbc-constructible-abelian-sheaf, def-weil-pbc-etale-constructible-sheaf, lem-
weil-pbc-exchange-forget-coefficients, lem-weil-pbc-constant-sheaf-geometric-stalk.
-/
theorem properSmoothCurves_prime_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (ell : ℕ) [Fact ell.Prime] (q : ℕ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) 0).obj
            ((constantSheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod ell)) (ULift.{u + 1} (ZMod ell))))))) := by
  sorry

end AlgebraicGeometry.Etale
