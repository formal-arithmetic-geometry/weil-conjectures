/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.GDelta.Basic
import Sheaf.AlgebraicGeometry.MultipointedCurveModification
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ChowProjectiveClosedImmersions
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.AlgebraicGeometry.FlatProperComponentCountLowerSemicontinuous
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.AdmissibleFiniteQuotientSeparated
import Sheaf.AlgebraicGeometry.ProjectiveGaloisAlterationEnvelope

/-!
# Equivariant marked nodal alteration

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IX, Theorem 1.2 and
section 1.4, printed pp. 131--133
(blueprint: lem-per-equivariant-marked-nodal-alteration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Equivariant marked nodal alteration with proper birational scheme quotients.
Source: ILO, Expose IX, Theorem 1.2(i)--(vi) and section 1.4, pp. 131--133
(blueprint: lem-per-equivariant-marked-nodal-alteration).

Proof plan, exactly the sixteen steps of the node:
1. The scheme $P$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since $f$ is proper
   over the Noetherian scheme $Y$. Apply [lem-weil-pbc-chow-noetherian] to $P\to Y$ and then [det-
   chow-projective-closed-immersions]. Take the reduced closure of the inverse image of the dense
   isomorphism open in the Chow scheme. Call it $P_0$, with $p:P_0\to P$. It is integral,
   projective over $Y$, and proper birational over $P$. On the generic fibre, $p_\eta$ is a proper
   birational map of integral curves: its source has dimension one by [lem-sc-closed-irreducible-
   dimension-trdeg], since its function field is unchanged. The smooth target $P_\eta$ is normal
   by [lem-sc-smooth-normal]. Thus [lem-trf-proper-birational-normal-curve-iso] makes $p_\eta$ an
   isomorphism.
2. Let $H_0$ be the schematic closure in $P_0$ of the inverse image of $E_\eta$ under the generic
   isomorphism. Its generic fibre is finite etale, including the empty case. Apply [lem-trf-
   flatification-horizontal-curve-pair] to $(P_0,H_0)\to Y$. It gives a projective-bundle
   birational blowup $v:S\to Y$ and strict transforms $(X,H)$ with $X$ integral, projective flat
   finitely presented of pure relative dimension one and $H$ finite flat finitely presented. The
   generic pair is still $(P_\eta,E_\eta)$; $S$ is excellent integral Noetherian. On the affine
   scheme $Y$, $\mathcal O_Y$ is ample: its principal affine opens are the nonvanishing loci of
   its sections, by [def-weil-pbc-ample-invertible-module]. Hence [lem-trf-projective-bundle-to-h-
   projective] makes $v$ projective in the required finite-projective-space convention.
3. The flat pair $(X,H)/S$ now satisfies [lem-per-separable-stable-modification-flat-pair]: the
   generic curve is smooth geometrically integral and the generic marking is etale. Obtain a
   separable alteration $r:S_1\to S$ and a projective-bundle stable modification $(Z,J)$ of
   $(X,H)\times_S S_1$. Apply [lem-per-projective-galois-alteration-envelope] to $r$. It supplies
   a normal integral excellent Noetherian scheme $Y'$, a projective Galois alteration $c:Y'\to S$,
   a map $t:Y'\to S_1$, and $G=\operatorname{Aut}_{k(S)}L$ with $L=k(Y')$. Define
   $(C,D)=(Z,J)\times_{S_1}Y'$. The normal-base-change clause of the stable-modification node
   supplies integrality, excellence, Noetherianity, and a stable modification
   $m:(C,D)\to(X,H)\times_S Y'$. Its generic pair is $(P_\eta,E_\eta)\times_{k(Y)}L$.
4. Set $W=X\times_S Y'$. The maps $X\to S$ and $v:S\to Y$ are H-projective, so $S$ is H-projective
   over the affine scheme $Y$ and has an ample invertible sheaf by [lem-weil-pbc-projective-ample-
   invertible]. The envelope map $c:Y'\to S$ is projective in the projective-bundle sense, hence
   H-projective by [lem-trf-projective-bundle-to-h-projective]. By [lem-pc-projective-base-change]
   and [lem-trf-h-projective-composition], both $W$ and $Y'$ are H-projective over the affine
   scheme $Y$. The scheme $W$ therefore has an ample invertible sheaf by [lem-weil-pbc-projective-
   ample-invertible]. Apply [lem-trf-projective-bundle-to-h-projective] to the projective-bundle
   curve map $m:C\to W$, and compose: $f':C\to Y'$ and $C\to Y$ are H-projective. Put $b=vc$, and
   let $a:C\to P$ be the composite through $W\to X\to P_0\to P$. This gives $fa=bf'$ by the
   defining maps of the pairs and fibre products.
5. The map $a$ is H-projective as well. Choose a closed immersion $i:C\hookrightarrow\mathbf
   P^n_Y$. Since $P\to Y$ is separated, the graph of $a$ in $P\times_Y C$ is the pullback of its
   closed diagonal. Composing this graph with the base change of $i$ gives a closed immersion
   $C\hookrightarrow P\times_Y\mathbf P^n_Y=\mathbf P^n_P$ whose projection is $a$. This is
   exactly projectivity [def-kun-projective]; the graph and the composition are closed immersions
   since their defining ideal sheaves pull back and add. The same projective structures show that
   $C,Y'$ are separated and proper over $Y$ by [lem-pc-projective-proper].
6. For $g\in G$, pull $m$ back by the automorphism $g:Y'\to Y'$ and identify its target with $W$
   using the action on the second factor. The result is another stable modification of
   $(X,H)\times_S Y'$: on geometric fibres the condition forbidding a contracted rational
   component with at most two special points is unchanged, by [def-trf-multipointed-curve-
   modification]. Apply [lem-trf-stable-modification-uniqueness-normal] over the normal integral
   qcqs scheme $Y'$. It supplies the unique isomorphism from this conjugate pair to $(C,D)$ over
   $W$. These isomorphisms give semilinear automorphisms $\rho_g$ of $(C,D)$ covering $g$. Both
   $\rho_g\rho_h$ and $\rho_{gh}$ are the unique isomorphism covering $gh$ and compatible with
   $m$, so they agree; similarly $\rho_1=1$. Thus they form a $G$-action, preserve the closed
   marking, and make $f'$ equivariant. The composite $a$ is invariant because $G$ acts trivially
   on $X,S,P_0,P,Y$.
7. By the stable-modification statement, $f'$ is flat finitely presented of pure relative
   dimension one with nodal geometric fibres. Its generic curve is $P_\eta\times_{k(Y)}L$, smooth
   by [lem-pc-proper-base-change](2) and geometrically integral by [def-pc-geometrically-
   irreducible]. The image of proper $f'$ is closed and contains the generic point of $Y'$, so
   $f'$ is surjective. Every geometric fibre is therefore nonempty. By [lem-weil-pbc-flat-proper-
   component-count-lower-semicontinuous], the number $n(y)$ of geometric connected components is
   lower semicontinuous. If $n(y)>1$, an open neighbourhood of $y$ has $n>1$ and contains the
   generic point, contradicting the integral generic fibre. Hence all geometric fibres are
   connected.
8. The marking $D$ is closed in $C$ and etale over $Y'$ by [lem-per-separable-stable-modification-
   flat-pair]. Thus it is proper by [lem-weil-pbc-proper-fp-permanence](a),(c). Etaleness gives
   flatness, unramifiedness and local finite presentation by [def-weil-etale-morphism]; [lem-weil-
   pbc-unramified-quasi-finite-at-points] gives local quasi-finiteness. Apply [pqf-lem-proper-lqf-
   finite] to obtain finiteness. The relative smooth locus $U\subset C$ is open by [lem-trf-nodal-
   family-fitting-singular] and contains $D$. On $U/Y'$, a smooth relative curve, [lem-pc-cartier-
   criterion](3) makes $D$ a relative effective Cartier divisor. On $C\setminus D$ its ideal is
   the unit ideal. These two opens cover $C$, so $D$ is an effective Cartier divisor on $C$,
   including when empty.
9. The generic fibre of $C\to P$ over the generic point of $P$ is $\operatorname{Spec}(F\otimes_K
   L)$, where $K=k(Y)$ and $F=k(P)$. This tensor is a domain by the geometric integrality of
   $P_\eta$ [def-pc-geometrically-irreducible], and finite dimensional over $F$, so is a field. It
   is finite etale over $F$, since $L/K$ is finite separable by [lem-weil-pbc-finite-separable-
   extension-etale] and etaleness is preserved by base change [lem-weil-pbc-etale-base-change-
   finite-limits](1). The generic fibre of $b$ is likewise $\operatorname{Spec}L$. Thus $a,b$ are
   dominant with finite generic fibres. They are proper by projectivity; [lem-weil-pbc-generic-
   finite-morphism-open-neighborhood] makes each finite over a dense open. Properness makes their
   dense images closed, hence surjective. This proves precisely the alteration convention of the
   statement.
10. For completeness, the generic etaleness just found holds on dense opens of the targets. On an
   affine open $\operatorname{Spec}A$ where either alteration is finite, its inverse image is
   affine and of finite presentation because $A$ is Noetherian. By [lem-weil-pbc-local-ring-spec-
   limit-affine-neighbourhoods] (1)--(3), the affine open neighbourhoods of the generic point
   $\xi$ of $\operatorname{Spec}A$ form a directed inverse system of quasi-compact quasi-separated
   schemes with affine transition maps, whose limit is $\operatorname{Spec}\mathcal
   O_{\operatorname{Spec}A,\xi}=\operatorname{Spec}\operatorname{Frac}A$. The base change of the
   finite map to this limit is its generic fibre, etale by Step 9. Apply [lem-weil-pbc-descend-
   etale] with $S_0=Y_0=\operatorname{Spec}A$ and $X_0$ the inverse image: the map is etale over
   some affine open neighbourhood of $\xi$, which is a dense open. In particular both $a$ and $b$
   are generically etale. No degree-prime-to-anything assertion is used.
11. By [lem-trf-nodal-family-fitting-singular], the nonsmooth locus of $f'$ is closed. Its image
   $T_{\mathrm{sing}}$ under proper $f'$ is closed and omits the generic point, because the
   generic curve is smooth. Put $A=a^{-1}|E|$. This is closed in the Noetherian scheme $C$, so has
   finitely many irreducible components by [lem-weil-pbc-noetherian-finitely-many-components]. On
   the generic fibre $A$ is exactly $|D|$, by the generic isomorphism of marked pairs. Each
   component of $A$ dominating $Y'$ has its generic point in this fibre, hence in closed $|D|$,
   and lies entirely in $|D|$. Let $V$ be the union of its other components. Then
   $T_{\mathrm{vert}}=f'(V)$ is closed by properness and excludes the generic point. Consequently
   $A\subset |D|\cup(f')^{-1}T_{\mathrm{vert}}$.
12. The envelope node supplies a dense open $U_S\subset S$ on which $c$ is a finite etale
   $G$-torsor; in particular its action is free there. Its complement pulls back to a closed
   nowhere dense set $T_{\mathrm{free}}$ in $Y'$. Let $T'$ be the union of all $G$-translates of
   $T_{\mathrm{free}}\cup T_{\mathrm{sing}}\cup T_{\mathrm{vert}}$. This finite union is closed,
   $G$-stable, and omits the generic point of integral $Y'$, hence is nowhere dense. It contains
   the three original bad sets, so $f'$ is smooth off $T'$, the action on $Y'\setminus T'$ is
   free, and $a^{-1}|E|\subset |D|\cup(f')^{-1}T'$.
13. The schemes $C,Y'$ are integral excellent Noetherian by Step 3. Step 5 proves that their
   morphisms to $Y$ are proper, hence separated and of finite type by [def-weil-proper-morphism].
   Thus separatedness holds over the very base $S=Y$ required in [lem-per-admissible-quotient-
   generic-degree]. Both are projective over the affine excellent Noetherian scheme $Y$, and their
   actions are over $Y$. Apply [lem-per-admissible-quotient-generic-degree]: its projective-over-
   affine clause makes both actions admissible. They are generically free, since the action on the
   dense open $Y'\setminus T'$ is free and $f'$ is equivariant and surjective. The same node now
   gives finite surjective scheme quotients $q_C:C\to Q=C/G$ and $q_Y:Y'\to B=Y'/G$, with
   invariant structure sheaves and orbit-space topology; $Q,B$ are integral excellent Noetherian
   of finite type over $Y$. Invariance of $a,b$ gives morphisms $\alpha:Q\to P$ and $\beta:B\to
   Y$.
14. Apply [lem-per-admissible-finite-quotient-separated] over $Y$ to the two finite quotients: $Q$
   and $B$ are separated over $Y$. For any base change $Y_0\to Y$, a closed subset of $Q\times_Y
   Y_0$ has closed inverse image in $C\times_Y Y_0$; its image in $Y_0$ is closed because $C\to Y$
   is proper, and is the same image because the finite surjection stays surjective after base
   change. Thus $Q\to Y$ is universally closed, and similarly $B\to Y$. Together with finite type
   and separatedness this is properness by [def-weil-proper-morphism]. For $\alpha:Q\to P$, the
   graph is closed since $P/Y$ is separated; its projection to $P$ is a base change of proper
   $Q\to Y$. Hence $\alpha$ is proper by [lem-weil-pbc-proper-fp-permanence](a)--(c), as is
   $\beta$.
15. The quotient theorem [lem-per-admissible-quotient-generic-degree] identifies the function
   fields of $Q,B$ with the invariant fields in $k(C),L$. On the generic marked pair the lifted
   action is the canonical one on the $L$ factor, by uniqueness in Step 6. The algebra $F\otimes_K
   L$ of Step 9 is already a field, so equals $k(C)$. Apply [lem-weil-pbc-tensor-field-extension-
   galois-invariants] with $A=F$, $M=L$: its invariant algebra is exactly $F$. Likewise $L^G=K$ by
   the envelope node. Thus $k(Q)=F=k(P)$ and $k(B)=K=k(Y)$ under $\alpha,\beta$. They are dominant
   proper maps with one-point generic fibres, so [lem-weil-pbc-generic-finite-morphism-open-
   neighborhood] makes them finite over dense opens.
16. Finally a finite dominant map of integral schemes inducing equality of function fields is an
   isomorphism after shrinking the target. Indeed take a nonempty affine open in the finite locus,
   with coordinate domain $A_0$; its preimage has coordinate domain $B_0$, finite over $A_0$, and
   both sit in the same fraction field. Choose finitely many $A_0$-module generators $b_i$ of
   $B_0$ and write each as $u_i/v_i$ with $u_i,v_i\in A_0$, $v_i\ne0$. After inverting $s=\prod_i
   v_i$, one has $(B_0)_s=(A_0)_s$. The corresponding nonempty principal open is the required
   dense isomorphism open. Apply this to $\alpha$ and $\beta$ of Step 15. They are proper
   birational in exactly the statement's convention. This concludes all clauses with the same
   $G,C,Y',D,T',a,b,f'$.

Freeness is tested on geometric points, rather than underlying scheme points. The quotient
predicate includes admissibility, orbit-space topology and the invariant structure sheaf.
-/
theorem exists_equivariantMarkedNodalAlteration
    {P Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y] [IsNoetherian Y]
    [IsIntegral P] (f : P ⟶ Y) [IsProper f] [IsDominant f]
    (hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hP : ∀ U : P.affineOpens, IsExcellent Γ(P, U))
    (η : Y) (hη : IsGenericPoint η Set.univ)
    [Smooth (f.fiberToSpecResidueField η)]
    [GeometricallyIntegral (f.fiberToSpecResidueField η)]
    (hdim : topologicalKrullDim (f.fiber η) = 1)
    (E : P.IdealSheafData) (hE : E.IsInvertible)
    [IsFinite ((E.subschemeι ≫ f).fiberToSpecResidueField η)]
    [Etale ((E.subschemeι ≫ f).fiberToSpecResidueField η)] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G)
      (C Y' : Scheme.{u}) (a : C ⟶ P) (b : Y' ⟶ Y) (f' : C ⟶ Y')
      (aC : G →* Aut C) (aY' : G →* Aut Y'),
      IsIntegral C ∧ IsIntegral Y' ∧ IsNoetherian C ∧ IsNoetherian Y' ∧
      C.IsSeparated ∧ Y'.IsSeparated ∧
      (∀ U : C.affineOpens, IsExcellent Γ(C, U)) ∧
      (∀ U : Y'.affineOpens, IsExcellent Γ(Y', U)) ∧
      a ≫ f = f' ≫ b ∧
      IsHProjective a ∧ IsProper a ∧ Surjective a ∧
      (∃ U : P.Opens, Dense (U : Set P) ∧ IsFinite (a ∣_ U) ∧ Etale (a ∣_ U)) ∧
      IsHProjective b ∧ IsProper b ∧ Surjective b ∧
      (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b ∣_ U) ∧ Etale (b ∣_ U)) ∧
      (∀ g : G, (aC g).hom ≫ a = a) ∧
      (∀ g : G, (aY' g).hom ≫ b = b) ∧
      (∀ g : G, (aC g).hom ≫ f' = f' ≫ (aY' g).hom) ∧
      IsHProjective f' ∧ Flat f' ∧
      ∃ hfp : LocallyOfFinitePresentation f',
        @HasNodalGeometricFibres _ _ f' hfp ∧
        (∃ (T' : Set Y') (hT' : IsClosed T') (D : C.IdealSheafData),
          IsNowhereDense T' ∧
          (∀ (g : G) (y : Y'), y ∈ T' → (aY' g).hom y ∈ T') ∧
          D.IsInvertible ∧ (∀ g : G, D.comap (aC g).hom = D) ∧
          Smooth (f' ∣_ (⟨T'ᶜ, hT'.isOpen_compl⟩ : Y'.Opens)) ∧
          IsFinite (D.subschemeι ≫ f') ∧ Etale (D.subschemeι ≫ f') ∧
          (∀ c : C, c ∈ D.support → c ∈ f'.smoothLocus) ∧
          a ⁻¹' (E.support : Set P) ⊆ (D.support : Set C) ∪ f' ⁻¹' T' ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (x : Spec (.of Ω) ⟶
              Scheme.Opens.toScheme (⟨T'ᶜ, hT'.isOpen_compl⟩ : Y'.Opens))
            (g : G),
            x ≫ Scheme.Opens.ι (⟨T'ᶜ, hT'.isOpen_compl⟩ : Y'.Opens) ≫ (aY' g).hom =
              x ≫ Scheme.Opens.ι (⟨T'ᶜ, hT'.isOpen_compl⟩ : Y'.Opens) → g = 1) ∧
        (∃ (Q B : Scheme.{u}) (qC : C ⟶ Q) (qY' : Y' ⟶ B)
          (α : Q ⟶ P) (β : B ⟶ Y),
          IsAdmissibleFiniteSchemeQuotient aC qC ∧
          IsAdmissibleFiniteSchemeQuotient aY' qY' ∧
          IsIntegral Q ∧ IsIntegral B ∧ IsNoetherian Q ∧ IsNoetherian B ∧
          (∀ U : Q.affineOpens, IsExcellent Γ(Q, U)) ∧
          (∀ U : B.affineOpens, IsExcellent Γ(B, U)) ∧
          qC ≫ α = a ∧ qY' ≫ β = b ∧ IsProper α ∧ IsProper β ∧
          (∃ U : P.Opens, Dense (U : Set P) ∧ IsIso (α ∣_ U)) ∧
          (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsIso (β ∣_ U))) ∧
        ∃ η' : Y', IsGenericPoint η' Set.univ ∧
          Smooth (f'.fiberToSpecResidueField η') ∧
          GeometricallyIntegral (f'.fiberToSpecResidueField η') := by
  sorry

end AlgebraicGeometry
