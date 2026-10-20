/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.CategoryTheory.Triangulated.GeneratingClassDetermination
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators

/-! # Constant coefficient tensor calculus for the exceptional adjoint

Source: Zheng, Theorem 2.18(2), Corollary 2.19, Construction 2.26 and Proposition 2.29(2)
(printed pp. 12, 14--16), specialized to schemes over an algebraically closed field
(blueprint: lem-pur-etale-exceptional-constant-tensor).

## Main definitions

- `exceptionalCoefficientTensor`: the existing tensor restricted to constant coefficients.
- `exceptionalConstantPullbackIso`: localization of the constant-sheaf pullback comparison.
- `exceptionalConstantProjectionMap`: the canonical compact-support projection composite.

## Main statements

- `exceptionalConstantTensor`: coefficient-uniform amplitude and the two canonical natural
  tensor isomorphisms for any fixed right adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Tensor by a termwise constant coefficient complex, as a bifunctor in the sheaf complex
and coefficient complex. This uses the existing constant-sheaf descent and derived tensor.
Source: Zheng, Theorem 2.18(2) and Proposition 2.29(2)
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalCoefficientTensor (C : Type (u + 1)) [CommRing C]
    (T : Scheme.{u}) :
    DerivedCategoryModule C T ⥤ DerivedCategory (ModuleCat.{u + 1} C) ⥤
      DerivedCategoryModule C T :=
  (derivedTensor (ModuleCat.{u + 1} C) T).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory

/-- The canonical pullback identification for termwise constant complexes. It is obtained
by descending the existing constant-sheaf pullback isomorphism through localization.
Source: Zheng, Theorem 2.18(2), constant-coefficient specialization
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalConstantPullbackIso (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} C) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Scheme.upperStarConstantSheafIso
      (ModuleCat.{u + 1} C) f)

/-- The actual compact-support projection map with the constant factor first. Compose the
signed symmetry, the existing compactification projection map, the canonical pullback of
constants, and the signed symmetry on the source. All factors are maps on derived categories.
Source: Zheng, Theorem 2.18(2), and Construction 2.26
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalConstantProjectionMap (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X) :
    ((exceptionalCoefficientTensor C Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).obj V ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj
        (((exceptionalCoefficientTensor C X).obj K).obj V) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).hom.app
      ((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app
      ((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
      (((derivedTensor (ModuleCat.{u + 1} C) X).obj K).map
          ((exceptionalConstantPullbackIso C f).hom.app V) ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V))

/-- For a separated finite-type morphism over an algebraically closed field, the ordinary finite-
coefficient exceptional adjoint has coefficient-uniform cohomological amplitude and canonical
natural constant-coefficient tensor isomorphisms for every fixed right adjunction. No
boundedness or perfectness of the coefficient complex is required. Source: Zheng, Theorem
2.18(2), Corollary 2.19, Construction 2.26 and Proposition 2.29(2), printed pp. 12, 14–16
(blueprint: lem-pur-etale-exceptional-constant-tensor).

Proof (the complete ten-step proof of the DAG node):

1. A field is Noetherian, so $X,Y,\overline X$ are Noetherian by finite type over a Noetherian
   base, and hence quasi-compact and quasi-separated. Here $\overline X$ is finite type over $k$:
   on a finite affine cover of $Y$, take finite affine covers of the inverse images under the
   finite-type map $p_f$; a finite list of $k$-algebra generators for each base algebra, together
   with the chosen algebra generators upstairs, generates the upstairs algebra over $k$. Thus this
   assertion follows directly from the definition of finite type. Choose $d\ge0$ bounding the
   dimensions of the scheme-theoretic fibres of $f$, using quasi-compactness of $Y$. Extension of
   the residue field to an algebraic closure preserves the dimension of each finite-type fibre, so
   the same $d$ bounds the geometric fibres. This choice depends only on $f$. If $X$ or $Y$ is
   empty choose $d=0$; all compact-support values on an empty source are zero. In the rest of the
   proof any geometric fibre bound $d$ is allowed, and $N_f=2d$.

   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-
   separated, lem-fin-finite-type-fibre-dimension-bound, lem-kun-dimension-extension, def-weil-
   finite-type-morphism.

2. The termwise $j_!$ is exact and left adjoint to $j^*$, so its functor on the unbounded derived
   category is exact and preserves arbitrary coproducts. The total derived $Rp_{f,*}$ is exact by
   the K-injective derived-functor theorem and preserves arbitrary coproducts by the proper
   coproduct theorem. Thus $F=Rp_{f,*}j_!$ is exact and preserves arbitrary coproducts. Module
   sheaves have enough injectives; a bounded-below object in $D^{\ge b}$ has a K-injective
   representative with zero terms below $b$. Applying the additive $p_{f,*}$ termwise to such a
   representative shows that $Rp_{f,*}$, and therefore $F$, preserves this lower bound. For a
   sheaf $H$ on $X$, the compact-support cohomological-dimension theorem applies: $C$ is finite
   and its additive exponent is invertible since $\ell\ne p$. It gives $F(H)\in D^{[0,2d]}$, for
   arbitrary $H$, with no constructibility assumption.

   Uses: lem-amb-etale-adjoint-locality, lem-sf-exact-functor-derived-triangulated, prop-weil-pbc-
   kinjective-resolutions-exist, lem-pc-right-derived-functor-triangulated, lem-amb-proper-
   coproducts, lem-weil-pbc-module-sheaves-enough-injectives, lem-weil-pbc-dplus-injective-
   representative, lem-dg-compact-support-amplitude.

3. Let $K\in D^{\le a}$. Replace it by a complex with zero terms in degrees $>a$, using good
   truncation. Its brutal lower subcomplexes $B_m=\sigma_{\ge a-m}K$, $m\ge0$, form an increasing
   sequence with termwise colimit $K$. Each $B_m$ has a finite filtration by its individual terms
   in their original degrees, so exactness of $F$ and the sheaf bound of step 2 give $F(B_m)\in
   D^{\le a+2d}$: at a filtration step the cohomology long exact sequence keeps the upper bound.
   The complex-colimit theorem identifies $K$ with the telescope of $(B_m)$, and the hocolimit-
   preservation theorem identifies $F(K)$ with a telescope of $(F(B_m))$. Coproducts are termwise
   in these derived categories, since module sheaves are Grothendieck abelian; their exactness
   means that a coproduct of objects in $D^{\le a+2d}$ is still in this subcategory. The telescope
   triangle and its long exact cohomology sequence therefore give $F(K)\in D^{\le a+2d}$. No
   convergence assertion for an unbounded spectral sequence is needed. Together with step 2, on
   bounded intervals this gives $F(D^{[r,s]})\subset D^{[r,s+2d]}$.

   Uses: def-sbc-standard-tstructure-derived-category, def-kun-truncations, lem-kun-complex-
   colimit-hocolim, lem-kun-functor-preserves-hocolim, lem-weil-pbc-module-sheaves-grothendieck-
   abelian, lem-kun-grothendieck-derived-coproducts.

4. For any $L\in D(Y_{\mathrm{et}},C)$ and $K\in D(X_{\mathrm{et}},C)$ compose the proper
   projection isomorphism and the open-immersion tensor isomorphism: $$L\otimes^L Rp_{f,*}j_!K\
   \cong\ Rp_{f,*}(p_f^*L\otimes^L j_!K)\ \cong\ Rp_{f,*}j_!(j^*p_f^*L\otimes^L K)=F(f^*L\otimes^L
   K).$$ Both cited statements apply on the ordinary etale sites to arbitrary unbounded complexes
   and the given finite commutative ring $C$. The pullbacks here are termwise exact inverse images
   for the constant coefficient ring. Their composite is $f^*$, and $f^*V_Y=V_X$ because inverse
   image carries the constant ring and constant-module sheafification to the same constant
   coefficients. The composite is the compact-support projection map: the proper map is the counit
   projection map with the indicated tensor symmetries, and the open map is the extension-by-zero
   tensor map. In particular taking $L=V_Y$ proves the first displayed isomorphism in the
   statement. We retain the stronger formula for arbitrary $L$ for use in the next step.

   Uses: lem-amb-proper-coproducts-projection, lem-pur-etale-open-derived-tensor, prop-weil-pbc-
   inverse-image-modules-exact, def-weil-pbc-constant-sheaf.

5. Apply the compact-generation lemma to $X$ and $Y$; its hypotheses require finite type over the
   algebraically closed field and invertibility of $\ell$, not separatedness of either scheme over
   $k$. Let $(E_s)$ be its family on $X$, and include all integer shifts in the indexing set. To
   show that $F(E_s)$ is compact, first its cohomology is bounded constructible: the constructible
   sheaf finiteness theorem applies to each of the finitely many constructible cohomology sheaves
   of $E_s$, and the successive good-truncation triangles give a finite Postnikov filtration, and
   exactness of $F$ gives constructibility of $F(E_s)$: the long exact cohomology sequence
   expresses each new cohomology sheaf as an extension of a kernel and a cokernel of maps between
   constructible sheaves, which are constructible. Suppose $E_s$ has Tor amplitude $[r,s']$. For
   every module sheaf $N$ on $Y$, $f^*N$ is a sheaf and step 4 gives $$F(E_s)\otimes^L N\ \cong\
   F(E_s\otimes^L f^*N).$$ The input on the right lies in $D^{[r,s']}$, so steps 2–3 place the
   output in $D^{[r,s'+2d]}$. Thus $F(E_s)$ has finite Tor amplitude, and compactness on $Y$
   follows from the compact-generation lemma. This argument allows nonregular finite rings $C$; no
   assertion that every finite $C$-module is perfect is used.

   Uses: lem-pur-etale-finite-ring-compact-generators, sbc-thm-finiteness-finite-type, def-kun-
   truncations, thm-constructible-serre.

6. The adjunction $F\dashv G$ is the fixed one in the item. The test family $(E_s[n])$ consists of
   compact objects, detects isomorphisms, and has compact images under $F$ by step 5. All
   categories have set-indexed coproducts and the required locally small Hom spaces. Apply the
   compact-test right-adjoint coproduct theorem to conclude that $G$ preserves arbitrary
   coproducts. Explicitly its comparison $\bigoplus_iGM_i\to G(\bigoplus_iM_i)$ induces, on
   testing with $E_s[n]$, the isomorphism $$\bigoplus_i\operatorname{Hom}(FE_s[n],M_i)\ \cong\
   \operatorname{Hom}(FE_s[n],\bigoplus_iM_i),$$ by adjunction and compactness of $FE_s[n]$.
   Detection makes the comparison an isomorphism.

   Uses: thm-amb-etale-exceptional-adjoint, lem-pur-etale-finite-ring-compact-generators, lem-sc-
   compact-tests-right-adjoint-coproducts.

7. Equip $G$ with the unique shift structure compatible with the exact functor $F$ and its fixed
   adjunction. The adjunction-shift theorem supplies it, with the counit equation
   $$\epsilon_{M[n]}=\epsilon_M[n]\circ c_{F,n,GM}\circ F(c_{G,n,M}).$$ The triangulated-right-
   adjoint theorem then makes $G$ exact with this structure. The constant-complex functor
   $V\mapsto V_T$ is exact and preserves coproducts: the constant presheaf functor does so
   sectionwise, and sheafification is exact and preserves all colimits. Passing to complexes
   preserves shifts and cones; termwise coproducts compute derived coproducts. For fixed $M$ it
   follows that $$A_M(V)=V_X\otimes^L GM,\qquad B_M(V)=G(V_Y\otimes^L M)$$ are exact functors of
   $V\in D(C\text{-}\mathrm{Mod})$ and preserve arbitrary coproducts, by the exactness and direct-
   sum properties of derived tensor and by step 6.

   Uses: lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint,
   lem-weil-pbc-site-r-module-presheaf-sheafification-exact, lem-sf-exact-functor-derived-
   triangulated, lem-kun-grothendieck-derived-coproducts, lem-kun-derived-tensor-triangulated,
   lem-kun-derived-tensor-direct-sums.

8. The projection isomorphism of step 4 is natural, unital and compatible with shifts in the
   coefficient variable $L$. For the proper factor this is the ringed-topos projection-mate
   exactness theorem. For the open factor use the canonical extension-by-zero tensor map of the
   cited open tensor theorem. The extension-by-zero stalk theorem identifies its stalk with the
   identity where the point lies in $X$ and with $0\to0$ outside $X$; the stalk-tensor theorem
   identifies the tensor factors. These are equalities on sheaf maps: exactness and conservativity
   of geometric stalks detect zero morphisms by applying the stalk functors to the image of their
   difference. Apply this degreewise to complexes. These maps commute with the tensor differential
   $d(x\otimes y)=dx\otimes y+(-1)^{\deg x}x\otimes dy$ and with the usual shift constraints. When
   factors are interchanged, the symmetry sends $x\otimes y$ to $(-1)^{\deg x\deg y}y\otimes x$,
   so the same coefficient-shift square still commutes. The tensor-unit map is the identity under
   the unit constraints. Composition preserves shift compatibility; thus, denoting step 4's
   coefficient projection map by $P$, the transformation $P^{-1}_{V,GM}$ commutes with coefficient
   shifts and has $P^{-1}_{C,GM}=1_{FGM}$ under tensor-unit identifications.

   Uses: lem-weil-pbc-ringed-projection-mate-exact, lem-pur-etale-open-derived-tensor, def-kun-
   derived-tensor, lem-kun-tensor-unit, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-
   pbc-extension-by-zero-stalks, lem-pod-etale-stalk-tensor-scalar, prop-weil-pbc-geometric-
   stalks-exact, lemma-weil-pbc-geometric-stalk-conservative.

9. Define $\alpha_{V,M}:A_M(V)\to B_M(V)$ by transposing $$F(V_X\otimes^L
   GM)\xrightarrow{P^{-1}_{V,GM}}V_Y\otimes^L FGM\xrightarrow{1\otimes\epsilon_M}V_Y\otimes^L M.$$
   Naturality of $P$, of $\epsilon$, and of the adjunction bijection proves naturality in $V,M$.
   For completeness the coefficient shift square for $\alpha$ is obtained by transposing its two
   sides under $F\dashv G$: after using the equation for $\epsilon$ in step 7, the two transposes
   are precisely the coefficient shift square for $P^{-1}$ from step 8 followed by
   $1\otimes\epsilon_M$. That square commutes, and the adjunction bijection is injective, so
   $\alpha$ is compatible with the specified shifts. Under $V=C$, step 8 identifies the transpose
   with $\epsilon_M$. The adjunction triangle identity says the transpose of $1_{GM}$ is
   $\epsilon_M$; hence $\alpha_{C,M}=1_{GM}$.

   Uses: thm-amb-etale-exceptional-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique,
   lem-kun-tensor-unit.

10. Fix $M$ and let $\mathcal L_M$ consist of the coefficient complexes $V$ for which
   $\alpha_{V,M}$ is invertible. It contains $C$ by step 9. Exactness of both functors and the
   proved shift compatibility imply that it is closed under shifts, distinguished triangles and
   retracts by the generating-class invertibility theorem. It is also closed under arbitrary
   coproducts: under the coproduct comparisons for $A_M$ and $B_M$, naturality along every
   coprojection identifies $\alpha_{\oplus V_i,M}$ with $\oplus\alpha_{V_i,M}$, which is
   invertible if each summand is. The derived-module free-generation theorem therefore gives
   $\mathcal L_M=D(C\text{-}\mathrm{Mod})$. Thus the second displayed map in the item is an
   isomorphism for every unbounded $V$ and $M$. Both maps are constructed from functors, natural
   maps and the fixed adjunction on the derived categories; changing resolutions computes these
   same maps, rather than defining a new comparison. This follows for the first map from its
   proper projection and open tensor construction in step 4, and for the second from the
   bijectivity of transposition. The argument uses generation only to propagate invertibility,
   never to infer equality of transformations from their values on generators, and asserts no
   tensor formula for $G$ with a nonconstant sheaf complex.

   Uses: lem-sf-generating-class-determination, lem-pc-derived-module-free-generation, lem-amb-
   proper-coproducts-projection, lem-pur-etale-open-derived-tensor, thm-amb-etale-exceptional-
   adjoint.
-/
theorem exceptionalConstantTensor
    (k : Type u) [Field k] [IsAlgClosed k] (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    [CharP k p] (hne : ell ≠ p)
    {X Y : Scheme.{u}} (xk : X ⟶ Spec (.of k)) (yk : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType xk] [LocallyOfFiniteType yk]
    [QuasiCompact xk] [QuasiCompact yk]
    (f : X ⟶ Y) (hf : f ≫ yk = xk)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ Nf : ℕ, ∀ (c : Compactification f)
      (C : Type (u + 1)) [CommRing C] [Finite C],
      (∃ n : ℕ, ∀ z : C, (ell : C) ^ n * z = 0) →
      (∀ (a : ℤ) (K : DerivedCategoryModule C X),
        _root_.DerivedCategory.IsLE K a →
          _root_.DerivedCategory.IsLE
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
            (a + Nf)) ∧
      (∀ (d : ℕ),
        (∀ y : Y, topologicalKrullDim
          (pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
              (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y)) ≤
            (d : ℕ∞)) →
        ∀ (a : ℤ) (K : DerivedCategoryModule C X),
          _root_.DerivedCategory.IsLE K a →
            _root_.DerivedCategory.IsLE
              ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
              (a + 2 * (d : ℤ))) ∧
      (∀ (G : DerivedCategoryModule C Y ⥤ DerivedCategoryModule C X)
        (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ G),
        ∃ P :
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⋙
              exceptionalCoefficientTensor C Y ≅
            exceptionalCoefficientTensor C X ⋙
              (Functor.whiskeringRight _ _ _).obj
                (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c),
          (∀ (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X),
            (P.hom.app K).app V = exceptionalConstantProjectionMap C c V K) ∧
          ∃ A : G ⋙ exceptionalCoefficientTensor C X ≅
              exceptionalCoefficientTensor C Y ⋙ (Functor.whiskeringRight _ _ _).obj G,
            ∀ (V : DerivedCategory (ModuleCat.{u + 1} C)) (M : DerivedCategoryModule C Y),
              (A.hom.app M).app V = adj.homEquiv _ _
                ((P.inv.app (G.obj M)).app V ≫
                  ((derivedTensor (ModuleCat.{u + 1} C) Y).obj
                    ((constantSheaf Y.smallEtaleTopology
                      (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)).map
                    (adj.counit.app M))) := by
  sorry

end AlgebraicGeometry.Etale
