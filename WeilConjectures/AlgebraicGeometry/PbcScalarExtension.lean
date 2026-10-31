/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.AlgebraicGeometry.PbcUniformCompleteTriangulated
public import WeilConjectures.AlgebraicGeometry.IntegralTStructure
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.PbcActualScalarPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.PbcScalarRestriction
import all WeilConjectures.AlgebraicGeometry.PbcScalarRestriction
import all WeilConjectures.AlgebraicGeometry.PbcScalarOperationComp
import all WeilConjectures.AlgebraicGeometry.PbcScalarOperationShift
import all WeilConjectures.AlgebraicGeometry.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.PbcScalarAmbientShift
import all WeilConjectures.AlgebraicGeometry.PbcScalarComposition
import all WeilConjectures.AlgebraicGeometry.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.PbcScalarTriangulation
import all WeilConjectures.AlgebraicGeometry.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.PbcScalarOperationIdentity

/-! # Finite scalar extension on the actual proper-base-change categories

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1307,
Milne, Lectures on Etale Cohomology, Section 19.
(blueprint: prop-weil-pbc-scalar-extension)

Coefficient maps are specified on all finite reductions. Integral extension is the
existing universal derived tensor functor. Rational extension is its balanced map
on the actual localized Hom modules, without adjoining retracts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

variable {Z : Scheme.{u}} (h : Z ⟶ X)


section
attribute [local irreducible] pbcActualCompletedPull pbcActualCompletion
  reductionDerivedChange completedAdicDerivedChange

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedComparison_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dE : AdicCoefficientDatum A) (dF : AdicCoefficientDatum B)
    (CY : PbcCompletedDerived Y dE ⥤ PbcCompletedDerived Y dF)
    (CX : PbcCompletedDerived X dE ⥤ PbcCompletedDerived X dF)
    (CZ : PbcCompletedDerived Z dE ⥤ PbcCompletedDerived Z dF)
    (θg : CY ⋙ pbcActualDerivedPull g dF ≅ pbcActualDerivedPull g dE ⋙ CX)
    (θh : CX ⋙ pbcActualDerivedPull h dF ≅ pbcActualDerivedPull h dE ⋙ CZ)
    (θhg : CY ⋙ pbcActualDerivedPull (h ≫ g) dF ≅
      pbcActualDerivedPull (h ≫ g) dE ⋙ CZ)
    (γg : CY ⋙ pbcActualCompletedPull g dF ≅ pbcActualCompletedPull g dE ⋙ CX)
    (γh : CX ⋙ pbcActualCompletedPull h dF ≅ pbcActualCompletedPull h dE ⋙ CZ)
    (γhg : CY ⋙ pbcActualCompletedPull (h ≫ g) dF ≅
      pbcActualCompletedPull (h ≫ g) dE ⋙ CZ)
    (hCY : ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y dE),
      PbcIsIntrinsicallyComplete Y dF (CY.obj K.obj))
    (hCZ : ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Z dE),
      PbcIsIntrinsicallyComplete Z dF (CZ.obj K.obj))
    (hg : ∀ K, (pbcActualCompletedPullUnit g dF).app (CY.obj K) ≫ γg.hom.app K =
      θg.hom.app K ≫ CX.map ((pbcActualCompletedPullUnit g dE).app K))
    (hh : ∀ K, (pbcActualCompletedPullUnit h dF).app (CX.obj K) ≫ γh.hom.app K =
      θh.hom.app K ≫ CZ.map ((pbcActualCompletedPullUnit h dE).app K))
    (hhg : ∀ K, (pbcActualCompletedPullUnit (h ≫ g) dF).app (CY.obj K) ≫ γhg.hom.app K =
      θhg.hom.app K ≫ CZ.map ((pbcActualCompletedPullUnit (h ≫ g) dE).app K))
    (ho : ∀ K, (pbcActualDerivedPull h dF).map (θg.hom.app K) ≫
      θh.hom.app ((pbcActualDerivedPull g dE).obj K) =
      (pbcActualDerivedPullCompIso h g dF).inv.app (CY.obj K) ≫
        θhg.hom.app K ≫ CZ.map ((pbcActualDerivedPullCompIso h g dE).hom.app K))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y dE)) :
    (pbcActualCompletedPull h dF).map (γg.hom.app K.obj) ≫
      γh.hom.app ((pbcActualCompletedPull g dE).obj K.obj) =
    (pbcActualCompletedPullCompIso h g dF).hom.app ⟨CY.obj K.obj, hCY K⟩ ≫
      γhg.hom.app K.obj ≫ CZ.map ((pbcActualCompletedPullCompIso h g dE).inv.app K) := by
  let LEg := pbcActualDerivedPull g dE
  let LFh := pbcActualDerivedPull h dF
  let PEg := pbcActualCompletedPull g dE
  let PEh := pbcActualCompletedPull h dE
  let PFg := pbcActualCompletedPull g dF
  let PFh := pbcActualCompletedPull h dF
  let eE := pbcActualCompletedPullCompIso h g dE
  let eF := pbcActualCompletedPullCompIso h g dF
  let cE := pbcActualDerivedPullCompIso h g dE
  let cF := pbcActualDerivedPullCompIso h g dF
  let ηEg := pbcActualCompletedPullUnit g dE
  let ηEh := pbcActualCompletedPullUnit h dE
  let ηFg := pbcActualCompletedPullUnit g dF
  let ηFh := pbcActualCompletedPullUnit h dF
  apply scalarCompletedComp_ext g h dF
    ⟨CY.obj K.obj, hCY K⟩ _
    (hCZ ⟨_,
      pbcActualCompletedPull_isComplete h dE (PEg.obj K.obj)⟩)
  let KF : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y dF) :=
    ⟨CY.obj K.obj, hCY K⟩
  have huE : cE.hom.app K.obj ≫
      (pbcActualDerivedPull h dE).map (ηEg.app K.obj) ≫
        ηEh.app (PEg.obj K.obj) =
      (pbcActualCompletedPullUnit (h ≫ g) dE).app K.obj ≫ eE.inv.app K :=
    scalarCompletedComp_unit_left g h dE K
  have huF : LFh.map (ηFg.app (CY.obj K.obj)) ≫
      ηFh.app (PFg.obj (CY.obj K.obj)) ≫ eF.hom.app KF =
      cF.inv.app (CY.obj K.obj) ≫
        (pbcActualCompletedPullUnit (h ≫ g) dF).app (CY.obj K.obj) :=
    scalarCompletedComp_unit_right g h dF KF
  have hn₂ : LFh.map (CX.map (ηEg.app K.obj)) ≫ θh.hom.app (PEg.obj K.obj) =
      θh.hom.app (LEg.obj K.obj) ≫
        CZ.map ((pbcActualDerivedPull h dE).map (ηEg.app K.obj)) :=
    θh.hom.naturality (ηEg.app K.obj)
  have hg := hg K.obj
  have hh := hh (PEg.obj K.obj)
  have hhg := hhg K.obj
  have ho := ho K.obj
  change LFh.map (ηFg.app (CY.obj K.obj)) ≫
      ηFh.app (PFg.obj (CY.obj K.obj)) ≫
        (PFh.map (γg.hom.app K.obj) ≫ γh.hom.app (PEg.obj K.obj)) =
    LFh.map (ηFg.app (CY.obj K.obj)) ≫
      ηFh.app (PFg.obj (CY.obj K.obj)) ≫
        (eF.hom.app KF ≫ γhg.hom.app K.obj ≫ CZ.map (eE.inv.app K))
  exact scalarCompletedPasting LFh PFh ηFh CZ hg hh hn₂ ho huE hhg.symm huF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed pullback comparison respects composition with its actual unit pasting.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-scalar-extension).
Proof: the ordinary composition equation holds on resolving tensor models.
Each completed comparison preserves the actual quotient unit. Both resulting
composites therefore extend the same ordinary map into the same complete object.
The reflection property identifies them, with the specified composition comparisons. -/
theorem pbcScalarCompletedPull_comp
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) :
    (pbcActualCompletedPull h (pbcIntegralDatum l F)).map
        ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj) ≫
      (pbcScalarCompletedPullIso l E F i h).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj) =
    (pbcActualCompletedPullCompIso h g (pbcIntegralDatum l F)).hom.app
        ⟨(pbcEmbeddingAmbientTensor l E F i Y).obj K.obj,
          pbcScalarPreservesComplete l E F i Y K⟩ ≫
      (pbcScalarCompletedPullIso l E F i (h ≫ g)).hom.app K.obj ≫
      (pbcEmbeddingAmbientTensor l E F i Z).map
        ((pbcActualCompletedPullCompIso h g (pbcIntegralDatum l E)).inv.app K) := by
  exact scalarCompletedComparison_comp g h (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcEmbeddingAmbientTensor l E F i Y) (pbcEmbeddingAmbientTensor l E F i X)
    (pbcEmbeddingAmbientTensor l E F i Z)
    (pbcScalarOrdinaryPullIso l E F i g) (pbcScalarOrdinaryPullIso l E F i h)
    (pbcScalarOrdinaryPullIso l E F i (h ≫ g))
    (pbcScalarCompletedPullIso l E F i g) (pbcScalarCompletedPullIso l E F i h)
    (pbcScalarCompletedPullIso l E F i (h ≫ g))
    (pbcScalarPreservesComplete l E F i Y) (pbcScalarPreservesComplete l E F i Z)
    (scalarCompletedPull_unit l E F i g) (scalarCompletedPull_unit l E F i h)
    (scalarCompletedPull_unit l E F i (h ≫ g))
    (pbcScalarOrdinaryPull_comp l E F i g h) K

end

end AmbientOperations
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

attribute [local irreducible] pbcStageTransition

/-- Finite coefficient extension on the actual raw rational categories has the
specified exact coherent tensor structure. The ambient, completion, conditional
restriction, and exchange clauses are stated by the companion declarations in
this module, with their actual canonical constructions above.
Source: blueprint order 1307; Milne, Lectures on Etale Cohomology, Section 19
(blueprint: prop-weil-pbc-scalar-extension).

Complete natural-language proof (all eight steps of the node):

1. Put $A=\mathcal O_E$, $B=\mathcal O_{E'}$, $t=\varpi_E$, $v=\varpi_{E'}$, $R_T=\widehat A_T$,
$S_T=\widehat B_T$. By [lem-weil-finite-free-completed-scalar-comparison], $S_T$ is a finite free
$R_T$-module and, for derived $t$-complete $K$, $K\otimes^L_{R_T}S_T$ is derived $v$-complete and
is canonically the completed integral scalar extension. The local-completeness and intrinsic
Koszul-completeness conventions agree by [lem-weil-pbc-constant-completion-equivalence]. Apply
[lem-weil-pbc-integral-stratified-perfect-characterization] to $K\in\Dbc(T,\mathcal O_E)$: on a
finite stratification it has local models $R_T\otimes_A^LP$ with $P$ bounded finite projective
over $A$. For each stratum inclusion and each pro-etale localization, the completed coefficient
sheaves restrict to the corresponding coefficient sheaves: for the scheme inclusion use
[lem-weil-pbc-profinite-coefficient-inverse-image], and for a slice localization restriction
commutes with the defining limits. Tensoring a model with $S_T$ gives $S_T\otimes_B^L(B\otimes_A
P)$. Each term of $B\otimes_A P$ is finite projective, since a splitting $P^i\oplus Q^i=A^{r_i}$
remains a splitting after tensoring. The same finite stratification and local termwise bounds
therefore give condition (ii) of that characterization over $B$. Its implication (ii) to (i)
supplies all the uniform tower and compatible etale-witness requirements of the PBC category. This
proves membership without identifying the PBC category with a different coefficient formalism.

2. The ordinary ring-sheaf change of rings $K\mapsto K\otimes^L_{R_T}S_T$ is exact by
[lem-pur-derived-change-of-rings]. By [lem-weil-pbc-uniform-complete-triangulated] the source and
target PBC integral categories have exactly the inherited triangles. Step 1 shows that the exact
ambient functor restricts to them. On integral morphisms its $A$-linearity is the identity
$(af)\otimes1=a(f\otimes1)$ on tensor representatives. Define the rational functor on morphisms by
$f/t^n\mapsto F(f)/t^n$. This is well-defined under the balancing and localization relations in
[def-weil-linear-scalar-localization]. The image of $t$ is invertible in the target rational
category: by [lem-weil-l-adic-extension-integers-dvr], the nonzero nonunit $t\in B$ is $uv^e$ for
a unit $u$ and $e\geq1$. Localization at $t$ and at $v$ gives the same morphism modules because
$v^{-1}=uv^{e-1}t^{-1}$ and $t^{-1}=u^{-1}v^{-e}$. By
[lem-weil-linear-scalar-localization-triangulated], every rational distinguished triangle is
isomorphic to a localized integral triangle; its image is consequently distinguished. This proves
exactness of the displayed functor on the raw rationalizations.

3. For three nested coefficient rings $R\to S\to U$, choose a K-flat resolution $P$ with flat
terms by [lem-pc-kflat-resolution]. Such representatives compute derived change of rings by
[lem-pur-derived-change-of-rings]; $P\otimes_R S$ is again K-flat with flat terms by
[lem-pur-kflat-change-of-rings]. Define the associator by $((p\otimes s)\otimes u)\mapsto p\otimes
su$, with inverse $p\otimes u\mapsto(p\otimes1)\otimes u$. These maps respect balancing,
restrictions and differentials. They are mutually inverse and commute with every chain map of
representatives. They hence descend through the derived localizations, and through scalar
localization by the formula of step 2. Comparison with completed scalar extension is the natural
comparison of step 1; choose these balanced maps as the specified associators for that
realization. Replace the identity-extension functor by the literal identity via multiplication
$p\otimes r\mapsto rp$. When any two adjacent fields coincide define the associator through this
unit identification.

4. For four coefficient rings $R\to S\to U\to V$, every route around the associativity pentagon
sends $(((p\otimes s)\otimes u)\otimes v)$ to $p\otimes(suv)$. Associativity of ring
multiplication makes the results equal; the universal balancing relations give equality of sheaf
maps and then of complex maps. With an identity extension, multiplication by $1$ gives the two
unit equations. Use the shift comparison which is the identity on $P^{q+1}\otimes_RS$: both
differentials are $-d_P\otimes1$. Thus the associator is the same multiplication map in both
shifted complexes, proving shift compatibility. Tensoring the cone $Q^q\oplus P^{q+1}$ gives the
cone of the tensor map, with the same differential matrix, so these comparisons are comparisons of
exact functors. Equalities of these maps persist in the two localizations of step 2.

5. For any scheme morphism $f$, [lem-weil-pbc-profinite-coefficient-inverse-image] identifies
$f^{-1}R_Y=R_X$ and $f^{-1}S_Y=S_X$, naturally in the finite coefficient quotients and their ring
maps. Define the direct-image comparison by the projection mate with coefficient object $S_Y$. By
[lemma-weil-pbc-perfect-projection-formula] it is an isomorphism after restricting to
$R_Y$-modules, because $S_Y$ is finite free by step 1. This is the required $S_Y$-module arrow,
not just an arbitrary restricted isomorphism: its adjunct is the counit on $K$ tensored with
$1_{S_X}$, so multiplication by any section of $S_Y$ commutes with it. To identify the target
direct image after restricting scalars, use the module adjunction
[lem-weil-pbc-ringed-topoi-module-adjunction] for the identity topos with ring map $R_X\to S_X$.
If $J$ is K-injective over $S_X$, maps from an acyclic $R_X$-complex $C$ to its restriction
identify with maps from $C\otimes_{R_X}S_X$ to $J$. The latter complex is acyclic since $S_X$ is
finite free. Such maps are null-homotopic by [def-pur-kinjective-complex]. Thus restriction
preserves K-injectives in this case, and the underived equality
$f_*\operatorname{Res}J=\operatorname{Res}f_*J$ computes the derived equality. Restriction detects
quasi-isomorphisms, as the underlying abelian sheaves are unchanged. The projection mate is
consequently an isomorphism in the $S_Y$-derived category itself. If $K$ is derived complete,
[prop-weil-pbc-direct-image-limits] makes $Rf_*K$ derived complete, for either coefficient ring.
Together with step 1 this puts both endpoints in the claimed ambient derived-complete categories.

6. Ordinary pullback commutes with coefficient extension by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the coefficient inverse-image
identifications of step 5. Now complete this comparison. The completed pullback of
[def-weil-pbc-completed-pullback] is ordinary pullback followed by its canonical completion unit.
Finite-free tensor commutes with the Koszul completion construction: a basis of $S_{T'}$ over
$R_{T'}$ identifies it with a finite sum, finite sums commute with products, and the matrix $1-s$
in the strict-tower Roos triangle commutes with that finite sum. The canonical map, defined before
choosing the basis, is therefore an isomorphism and respects the completion units. The Roos
realization is [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. Completion with respect to $t$
and $v$ in $S_{T'}$ is the same reflector: $t=uv^e$ implies $S[1/t]=S[1/v]$ with the same
localization map from $S$. The extended Cech complexes for these single generators are
consequently the identical augmented complex $[S\to S[1/v]]$. By
[lem-weil-pbc-extended-cech-completion-model], derived Hom from this augmented complex realizes
both completion reflectors and their units. By [lem-weil-pbc-ringed-koszul-completion-reflector],
the Koszul completion constructions are also these reflectors, so their canonical isomorphism is
uniquely fixed by the units. This gives the claimed completed-pullback comparison without claiming
that ordinary pullback of an arbitrary complete object is complete.

7. The comparisons just constructed are coherent. For coefficient towers, take successively
tensor-product bases of the finite-free extensions. The projection comparison of step 5, after
restriction of scalars, is the direct sum of identity maps $Rf_*K\to Rf_*K$ indexed by a basis.
This follows from its counit-tensor definition and the tensor-unit case of
[lem-weil-pbc-ringed-projection-mate-exact]. Iterating two comparisons or using their associator
in step 3 gives the same identities indexed by pairs of basis elements. Changing a basis
conjugates both routes by the same scalar matrix, so the resulting equality is independent of the
bases. For composed scheme morphisms the counit of the composite adjunction is the composite of
the two counits; tensoring these with $1$ gives the same direct sums of identities. For pullback
these equations are the balanced formula of step 3 on the canonical compositions of inverse
images. For completed pullback they persist because the completion isomorphisms in step 6 are
uniquely fixed by the completion units. The same equations with a single basis element $1$ give
identity coherence. Shift coherence follows from the counit-tensor shift equation in
[lem-weil-pbc-ringed-projection-mate-exact] and the explicit shift formula in step 4.

8. Set $Q=S_Y$ in [lem-weil-pbc-ringed-exchange-tensor-coherence]. Its two equal composites say
exactly that tensoring the ambient $R$-exchange and then using the direct-image and pullback
comparisons gives the ambient exchange after coefficient extension. The $S$-actions are those of
step 5: the exchange is the mate of the same inverse-image commutation square, with counits
transported by scalar extension, so the equality is an equality of $S$-module arrows. For the
completed exchange, apply the completion functor to this equality and use step 6. The canonical
identification of completed $Rf'_*Lg'^*K$ with $Rf'_*Lg'^*_{\mathrm{comp}}K$ is computed by
$R\lim$ of the projection-formula maps for finite reductions, followed by the
direct-image/derived-limit isomorphism of [prop-weil-pbc-direct-image-limits]. For coefficient
change, compute completion on both sides with the image of $t$. Use the Koszul towers
$[R\xrightarrow{t^n}R]$ and $[S\xrightarrow{t^n}S]$: tensoring the first with $S$ gives the
second, including transition maps (multiplication by $t$ in degree $-1$, identity in degree zero)
and units. These are bounded finite-free coefficient complexes, so the projection arrows and their
exchange square apply to them. Their derived limits compute completion by step 6. The
$t$-completion of $S$ is identified with its $v$-completion by the unit-compatible reflector
comparison of that step; no equality of $t^n$- and $v^n$-reductions is used. By
[lemma-weil-pbc-projection-formula-base-change-naturality], the ambient equality commutes with
each of these specified projection maps. To obtain an equality of tower arrows, apply the same
ringed projection/exchange coherence on the diagram sites of
[lem-weil-pbc-diagram-site-realization], with $J=\mathbf N_{\geq1}^{\mathrm{op}}$. On each product
site use the completed ring sheaf constant in the $J$ direction, exactly as in that realization
statement; the quotient coefficient towers are module objects over this ring sheaf through its
quotient maps. Thus no assertion about a varying ring sheaf is required. These sites are small;
their module categories are exactly the strict diagram categories, by its additive exact
equivalence. Thus the projection mate and exchange mate calculation holds for the actual diagram
arrows, not merely at their evaluations. The derived strict-tower limit is an actual functor by
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], so applying it preserves this equality; no
faithfulness of levelwise derived evaluations is used. This is compatibility with the completion
of the specified ambient mate, including its prescribed direct-image/completion comparison, rather
than compatibility with some isomorphism between its endpoints. Finally all arrows restrict when
the operations preserve the integral constructible categories, and rationalization extends those
specified transformations by [prop-weil-pbc-rational-transport]. The denominator formula of step 2
shows that the integral equality remains the same equality for every rational morphism. This
proves the last assertion.
-/
theorem pbcCoherentScalarExtension
    {E F G H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H) :
    (pbcStageTransition l Ω T h).Additive ∧
    (pbcStageTransition l Ω T h).IsTriangulated ∧
    (pbcStageTransition l Ω T (le_refl E) = 𝟭 _) ∧
    HEq (pbcStageAssociator l Ω T (le_refl E) h)
      (Functor.leftUnitor (pbcStageTransition l Ω T h)) ∧
    HEq (pbcStageAssociator l Ω T h (le_refl F))
      (Functor.rightUnitor (pbcStageTransition l Ω T h)) ∧
    (∀ K : pbcCoefficientStage l Ω T E,
      (pbcStageTransition l Ω T h'').map ((pbcStageAssociator l Ω T h h').hom.app K) ≫
          (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
        (pbcStageAssociator l Ω T h' h'').hom.app ((pbcStageTransition l Ω T h).obj K) ≫
          (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K) ∧
    NatTrans.CommShift (pbcStageAssociator l Ω T h h').hom ℤ := by
  have hLaws := pbcStageAssociator_laws l Ω T
  exact ⟨(pbcStageExact l Ω T h).1, (pbcStageExact l Ω T h).2,
    hLaws.2.1 E, (hLaws.2.2 h).1, (hLaws.2.2 h).2, hLaws.1 h h' h'',
    pbcStageAssociatorShift l Ω T h h'⟩

end AlgebraicGeometry.Scheme
