/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural
public import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.CategoryTheory.SiteCechComplex
import Mathlib.Topology.Sheaves.Functors
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural

/-!
# Frobenius and the canonical coherent-etale comparisons

Source: Stacks Project, Tags 0A3P, 03P2, 03FD and 02KH
(blueprint: lem-weil-pbc-coherent-frobenius-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false

/-- Frobenius commutes with the canonical additive/coherent comparisons and field extension.
Source: Stacks Project, Tags 0A3P, 03P2, 03FD and 02KH
(blueprint: lem-weil-pbc-coherent-frobenius-comparison).

The three coefficient endomorphisms are specified by their sectionwise pth powers.
The coefficient map u is specified by its adjoint on regular functions. The linear
equivalence b is specified on v tensor 1 by the canonical coherent pullback. These
binders name the maps introduced in the statement, with their defining properties.
Tensor order is K tensor E; b(a tensor v) denotes the paper's b(v tensor a).
Additivity of coherent Frobenius is encoded by structureCoherentFrobenius's additive-hom type.

Proof:
1. Properness gives separatedness and finite type. The finite-type definition supplies a finite
   affine open cover $\mathcal U$ of $X$ over $\operatorname{Spec}k$. Repeated application of
   the separated-affine-intersection lemma makes every positive-length tuple intersection
   affine, including repetitions. The inverse images of the opens cover $X_K$, and inverse image
   commutes with intersections. Apply the affine-triple tensor base-change theorem with
   $S=\operatorname{Spec}k$, $X_0=Y_0=X$, $f_0=\mathrm{id}_X$, $W_0=S$,
   $U_0=V_0=U_J=\operatorname{Spec}A_J$, $B=C=A_J$, $\phi=\mathrm{id}_{A_J}$, and
   $T=\operatorname{Spec}K$: it identifies $j^{-1}U_J$ with $\operatorname{Spec}(K\otimes_k
   A_J)$, hence makes every target tuple affine. The structure sheaf is locally the module
   associated to the section ring itself, so it is quasi-coherent. Affine module vanishing
   applies on both schemes. For each affine intersection $U_J$, restriction of an ambient module
   injective resolution to $U_J$ is an injective resolution, by the module open-restriction
   lemma. Thus ambient derived evaluation at $U_J$ equals module cohomology of the scheme $U_J$.
   Apply the module/abelian comparison on that scheme. By the Zariski open-restriction lemma,
   restriction of an ambient abelian injective resolution is also an injective resolution, with
   exactly the same section complex at $U_J$. Consequently the resulting abelian vanishing on
   the scheme $U_J$ is precisely ambient abelian object-cohomology vanishing; apply the etale
   object-vanishing theorem with the unit quasi-coherent module to obtain etale vanishing. Thus
   the acyclic-edge hypotheses of Step 2 hold for all three cohomology theories on both schemes.
2. Use the common section complex $C^r=\prod_J\mathcal O_X(U_J)$ with alternating restriction
   differential, and denote its canonical edges by $e_{et},e_{ab},e_{mod}$. The Zariski-to-etale
   inclusion is continuous, preserves the final object and tuple fibre products, and defines the
   change-of-site morphism by the cited inclusion theorem. For the associated unit module its
   restriction has exactly the Zariski sections and restrictions, by the definition of the
   associated etale sheaf: for $v:V\to X$, its unit pullback $v^*\mathcal O_X=\mathcal
   O_V\otimes_{v^{-1}\mathcal O_X}v^{-1}\mathcal O_X$ identifies with $\mathcal O_V$ via
   $r\otimes s\mapsto r\,v^\sharp(s)$, with inverse $r\mapsto r\otimes1$. Apply the general
   change-of-site edge square with identity coefficient map on these sections, and then its
   module-forgetting square. This gives $H^q(\epsilon)e_{ab}=e_{et}$ and $\iota e_{mod}=e_{ab}$,
   where $\iota$ is the canonical module-to-abelian identification. Consequently the canonical
   composite $H^q(\epsilon)\iota$ sends $e_{mod}[z]$ to $e_{et}[z]$, and its inverse sends
   $e_{et}[z]$ to $e_{mod}[z]$. This is $c_X^q$ by the specified etale-to-Zariski
   characterization in the statement; we do not infer canonicity from the existence-only
   statement of the quasi-coherent comparison theorem. All edges are isomorphisms by Step 1 and
   the acyclic-edge lemma. Apply these same two squares on $X_K$ with its base-changed cover to
   obtain $c_{X_K}^q e_{et,K}=e_{mod,K}$.
3. On each section ring, $p\cdot1=0$ by its structural $k$-algebra map (also for the zero ring),
   so the binomial coefficients $\binom pi$ vanish for $0<i<p$, so $(s+t)^p=s^p+t^p$ and
   $(-s)^p=-s^p$ (also for $p=2$). Restrictions are ring maps, so the componentwise map
   $T(s_J)=(s_J^p)$ is additive and commutes with the alternating differential. Thus it acts on
   cycles modulo boundaries. Since $T(a z)=a^pT(z)$, its map on Cech cohomology is
   $p$-semilinear. Natural additive edge maps for the coefficient Frobenius identify
   $e_{et}[Tz]=H^q(\mathrm{Fr}_X)e_{et}[z]$ and $e_{ab}[Tz]=H^q(\mathrm{Fr}_{X,Zar})e_{ab}[z]$.
   Step 2 then identifies the transported Zariski Frobenius with $e_{mod}[z]\mapsto
   e_{mod}[Tz]$. Apply module-edge naturality to the $\mathcal O_X$-linear endomorphism given by
   multiplication by $a\in k$: its section and cohomology actions are scalar multiplication, so
   the module edge is $k$-linear, so this proves additivity, $F_X^q(av)=a^pF_X^q(v)$, and
   $c_X^qH^q(\mathrm{Fr}_X)=F_X^qc_X^q$. No module-linearity of Frobenius has been assumed.
4. The etale base-change functor $W\mapsto W\times_X X_K$ preserves final objects and fibre
   products by the finite-limit theorem, and carries covers to covers by the continuity theorem.
   The algebraic-structures theorem supplies the set-theoretic inverse image, its finite-limit
   preservation and its adjunction to direct image. A left adjoint preserves colimits, so this
   defines a morphism of sites; the same theorem identifies its abelian inverse image and unit
   with the specified ones. On each tuple, the adjoint of $u$ is the structural ring map
   $j_J^\#: \mathcal O_X(U_J)\to\mathcal O_{X_K}(j^{-1}U_J)$. The general change-of-site edge
   square therefore computes precisely the unit-and-coefficient pullback of the cohomology-
   pullback definition: $P_j^q(e_{et}[z])=e_{et,K}[(j_J^\#z_J)_J]$. This uses the adjoint
   additive coefficient map, without identifying $j^{-1}G_X$ with $G_{X_K}$.
5. A field extension is flat: choose a $k$-basis of $K$, so tensoring with $K$ is a direct sum
   of copies of the identity on vector spaces and is exact. On Zariski sites the inverse-image-
   of-opens functor takes $U_J$ to $j^{-1}U_J$, preserving the final object, coverings and
   intersections. Apply the general change-of-site edge square to the underlying abelian
   structural map $\mathcal O_X\to j_*\mathcal O_{X_K}$, and use the module-forgetting square on
   each scheme. It gives $j_{coh}^q(e_{mod}[z])=e_{mod,K}[(j_J^\#z_J)_J]$ for the canonical
   additive coherent pullback. To identify the Ext presentation used by the flat-comparison
   definition with these derived module groups, use the explicitly constructed
   moduleCohomologyExtResolutionEquiv, not an unspecified natural equivalence. Its coefficient
   naturality and its direct-image edge formula identify the map for the structural module
   morphism $\varphi:\mathcal O_X\to j_*\mathcal O_{X_K}$: first apply $H^q(\varphi)$ on $X$,
   then the identity-coefficient direct-image edge. In the Ext presentation this is exactly
   inverse image with the constant-integer-sheaf comparison followed by the coefficient map, as
   specified in the flat-comparison definition. The definition of module cohomology fmap uses
   the same resolution diagram for that composite; the canonical module/abelian identification
   is obtained by forgetting this resolution and comparing its acyclic section complex. Thus the
   additive map $j_{coh}^q$ above is the map extended by the specific flat comparison, so
   $b_q(v\otimes a)=a\,j_{coh}^q(v)$ (its tensor order is exchanged from $K\otimes_k E_X^q$).
   Apply module-edge naturality on $X_K$ to multiplication by $a\in K$, which is $\mathcal
   O_{X_K}$-linear. Thus $e_{mod,K}$ is $K$-linear, hence $b_q(e_{mod}[z]\otimes
   a)=e_{mod,K}[(a\,j_J^\#z_J)_J]$. The specific flat separated-cohomology theorem supplies
   invertibility of this very map: $X$ is compact (quasi-compact) by finite type, its structure
   morphism is separated, and the unit module is quasi-coherent. Taking $a=1$, Step 4 and the
   two canonical edge identities in Step 2 give $c_{X_K}^q(P_j^q(x))=b_q(c_X^q(x)\otimes1)$ for
   every $x$.
6. For every tuple $J$, the ring-map property and commutativity give
   $(j_J^\#(z_J)a)^p=j_J^\#(z_J^p)a^p$. Therefore, if $v=e_{mod}[z]$, Step 3 on $X_K$ and Step 5
   imply $F_{X_K}^q(b_q(v\otimes a))=e_{mod,K}[(j_J^\#(z_J^p)a^p)_J]=b_q(F_X^q(v)\otimes a^p)$.
   Every cohomology class has a Cech cycle representative by Step 1, so the identity holds for
   every $v$ and $a$. The tensor relation is respected: replacing $(\lambda v)\otimes a$ by
   $v\otimes\lambda a$ gives $F_X(v)\otimes\lambda^pa^p$ on both sides. Thus the formula does
   not require $k$ or $K$ to be perfect.
-/
theorem coherent_frobenius_comparison
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (g : Y ⟶ Spec (.of K)) (j : Y ⟶ X)
    (h : IsPullback j g f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ)
    (FrZ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X) ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X))
    (FrZK : (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y) ⟶
      (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj (unit Y))
    (hFrZ : ∀ (U : X.Opensᵒᵖ) (s : Γ(X, U.unop)), FrZ.hom.app U s = s ^ p)
    (hFrZK : ∀ (U : Y.Opensᵒᵖ) (s : Γ(Y, U.unop)), FrZK.hom.app U s = s ^ p)
    (FrE : structureTensorEtaleSheaf X ⟶ structureTensorEtaleSheaf X)
    (hFrE : ∀ (U : X.Etaleᵒᵖ) (s : (structureTensorEtaleSheaf X).obj.obj U),
      (tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ (FrE.hom.app U s).down =
        (@id Γ(U.unop.left, ⊤)
          ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ s.down)) ^ p)
    (u : (Etale.upperStar AddCommGrpCat.{u + 1} j).obj
      (structureTensorEtaleSheaf X) ⟶ structureTensorEtaleSheaf Y)
    (hu : ∀ (U : X.Etale) (s : (structureTensorEtaleSheaf X).obj.obj (op U)),
      (tensorPullbackObjUnitToUnit
          ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U).hom).app ⊤
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv
          (structureTensorEtaleSheaf X) (structureTensorEtaleSheaf Y) u).hom.app
            (op U) s).down =
        (pullback.fst U.hom j).appTop
          ((tensorPullbackObjUnitToUnit U.hom).app ⊤ s.down))
    (b : (K ⊗[k] scalarCohomology f (unit X) q) ≃ₗ[K]
      scalarCohomology g (unit Y) q)
    (hb : ∀ v : scalarCohomology f (unit X) q,
      b ((1 : K) ⊗ₜ[k] v) =
        (moduleCohomologyFMap j
          (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q).hom v) :
    (∀ (a : k) (v : scalarCohomology f (unit X) q),
      structureCoherentFrobenius f q FrZ (a • v) =
        a ^ p • structureCoherentFrobenius f q FrZ v) ∧
    (∀ x : Sheaf.H (structureTensorEtaleSheaf X) q,
      structureCoherentEtaleComparison f q (Sheaf.H.map FrE q x) =
        structureCoherentFrobenius f q FrZ (structureCoherentEtaleComparison f q x)) ∧
    (∀ x : Sheaf.H (structureTensorEtaleSheaf X) q,
      structureCoherentEtaleComparisonOfPullback f g j
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) h q
          (Sheaf.H.map u q (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q x)) =
        b ((1 : K) ⊗ₜ[k] structureCoherentEtaleComparison f q x)) ∧
    ∀ (v : scalarCohomology f (unit X) q) (a : K),
      structureCoherentFrobenius g q FrZK (b (a ⊗ₜ[k] v)) =
        b ((a ^ p) ⊗ₜ[k] structureCoherentFrobenius f q FrZ v) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
