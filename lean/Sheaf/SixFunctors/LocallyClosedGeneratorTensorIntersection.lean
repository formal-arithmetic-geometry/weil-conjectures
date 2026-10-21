/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

import Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.CondensedFiniteFreeTensorExact
import Sheaf.Paper.FlatSingleScalarConventions
import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-! # Tensor of locally closed lisse generators

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field/
sk-thm-sf-pf-field-tensor.proof.md,
Proof (1) (blueprint: lem-sfb-locally-closed-generator-tensor-intersection).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Both orders of open/closed factorization, using Mathlib's factorization data without a new
factorization notion. Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
abbrev GeneratorFactorization {S X : Scheme.{u}} (a : S ⟶ X) :=
  MorphismProperty.MapFactorizationData @IsClosedImmersion @IsOpenImmersion a ⊕
    MorphismProperty.MapFactorizationData @IsOpenImmersion @IsClosedImmersion a

/-- The actual module extension `j_! i_*`, or `i_* j_!`, for the given factorization.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  match A with
  | .inl A =>
    letI : IsOpenImmersion A.p := A.hp
    lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p
  | .inr A =>
    letI : IsOpenImmersion A.i := A.hi
    openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p

/-- Restriction normalization: inverse open unit and closed counit in factorization order,
with the canonical inverse-image composition. Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) :
    generatorExtension Λ A ⋙ upperStar Λ a ⟶ 𝟭 _ :=
  match A with
  | .inl A =>
    letI : IsOpenImmersion A.p := A.hp
    (Functor.associator (lowerStar Λ A.i) (openImmersionLowerShriek Λ A.p)
      (upperStar Λ a)).hom ≫
      Functor.whiskerLeft (lowerStar Λ A.i)
        (Functor.whiskerLeft (openImmersionLowerShriek Λ A.p)
          ((eqToIso (congrArg (upperStar Λ) A.fac.symm) ≪≫
            upperStarComp Λ A.i A.p).hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (asIso (openImmersionLowerShriekUpperStarAdjunction Λ A.p).unit).inv
            (upperStar Λ A.i) ≫
          (Functor.leftUnitor _).hom) ≫
      (upperStarLowerStarAdjunction Λ A.i).counit
  | .inr A =>
    letI : IsOpenImmersion A.i := A.hi
    (Functor.associator (openImmersionLowerShriek Λ A.i) (lowerStar Λ A.p)
      (upperStar Λ a)).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek Λ A.i)
        (Functor.whiskerLeft (lowerStar Λ A.p)
          ((eqToIso (congrArg (upperStar Λ) A.fac.symm) ≪≫
            upperStarComp Λ A.i A.p).hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (upperStarLowerStarAdjunction Λ A.p).counit
            (upperStar Λ A.i) ≫
          (Functor.leftUnitor _).hom) ≫
      (asIso (openImmersionLowerShriekUpperStarAdjunction Λ A.i).unit).inv

/-- Source bifunctor on the full categories of lisse modules, in degree zero.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorTensorSource
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} {a : S ⟶ X} {b : T ⟶ X}
    (A : GeneratorFactorization a) (B : GeneratorFactorization b) :=
  (((Functor.whiskeringLeft₂ _).obj
    ((ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S))) ⋙
      generatorExtension Λ A ⋙ DerivedCategory.singleFunctor _ 0)).obj
    ((ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T))) ⋙
      generatorExtension Λ B ⋙ DerivedCategory.singleFunctor _ 0)).obj (derivedTensor Λ X)

/-- Ordinary relative tensor after the two actual fibre-product projections.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorIntersectionModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} (a : S ⟶ X) (b : T ⟶ X) :=
  (((Functor.whiskeringLeft₂ _).obj (upperStar Λ (pullback.fst a b))).obj
    (upperStar Λ (pullback.snd a b))).obj (MonoidalCategory.curriedTensor _)

/-- Target bifunctor: extend the underived relative tensor from the actual fibre product.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorTensorTarget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} (a : S ⟶ X) (b : T ⟶ X)
    (C : GeneratorFactorization (pullback.fst a b ≫ a)) :=
  (Functor.postcompose₂.obj (generatorExtension Λ C ⋙ DerivedCategory.singleFunctor _ 0)).obj
    ((((Functor.whiskeringLeft₂ _).obj
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)))).obj
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)))).obj
      (generatorIntersectionModule Λ a b))

/-- Tensor-intersection isomorphisms, natural in both lisse modules and independent of
both orders of open/closed factorization under normalized extension comparisons.
Source: blueprint main-20261015, sk-thm-sf-pf-field-tensor.proof.md, Proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection).

Proof, following the node step by step:

1. Choose closed-then-open factorizations of $a,b$. Base change of their closed and open factors
shows that $r,s$ are locally closed immersions and, by composition of immersions (clause (e) of
the permanence lemma), that their composites with $a,b$ are the same immersion $c:W\hookrightarrow
X$. In particular this is the actual fibre product $S\times_XT$, rather than a chosen reduced
intersection. Every intermediate open is Noetherian; every intermediate closed subscheme is
Noetherian, since a closed immersion is finite type. Apply the same observation to the
base-changed factors to see that $S,T,W$ are Noetherian. The underlying space of each has
descending chains of closed subsets stabilizing; hence all its subsets are quasi-compact.
Consequently the opens in these factorizations and all complementary opens are quasi-compact as
morphisms (test on any affine open). All hypotheses of the open/closed projection formulas and the
extension-coherence and base-change lemmas below therefore hold.
Uses: def-weil-closed-immersion, lem-weil-pbc-open-immersion-base-change,
lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-noetherian-open-subscheme-noetherian,
lem-weil-pbc-closed-immersion-proper, lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, lem-sfb-noetherian-space-compact-subsets,
lem-weil-pbc-proper-fp-permanence.

2. The coefficient isomorphism $h^{-1}R_Z\cong R_Y$ holds for every morphism $h:Y\to Z$, for
arbitrary condensed $\Lambda$, by the alpha-isomorphism lemma. Thus the inverse-image coefficient
convention in extension coherence is the one in the statement. Pull back the trivializing
pro-etale covers for $L,M$ to $W$ and refine them by their pairwise fibre products. On this common
cover, exact monoidal inverse image identifies $r^*L$ with $R_W^m$ and $s^*M$ with $R_W^n$.
Distributing the ordinary tensor over these finite sums gives the basis $e_i\otimes f_j$, indexed
by $(i,j)$; the maps $e_i\otimes f_j\leftrightarrow e_{(i,j)}$ are mutually inverse. Hence
$P=r^*L\otimes_{R_W}s^*M$ is lisse of rank $mn$ on this cover, including $m=0$ or $n=0$.
Uses: lem-sfb-alpha-iso, def-sfb-lisse-coefficient-module,
def-sfb-condensed-pullback-tensor-comparison.

3. Apply finite-free tensor exactness to $r^*L$ and $s^*M$. Each is flat as an internal
$R_W$-module, with no restriction on $\Lambda$. The flat-single lemma makes their degree-zero
complexes K-flat in the relative tensor convention. Computing derived tensor on these
representatives therefore gives the natural comparison $r^*L[0]\otimes^{\mathbf
L}_{R_W}s^*M[0]\cong P[0]$: its total complex has only the $(0,0)$ summand, so every differential
is zero. This also fixes the underived identification used below.
Uses: lem-weil-pbc-condensed-finite-free-tensor-exact, lem-sfb-flat-single-scalar-conventions,
sk-def-sfb-derived-tensor-hom.

4. For any of the locally closed immersions $h:D\hookrightarrow Z$ occurring here, factor $h=v i$
with $i:D\hookrightarrow V$ closed and $v:V\hookrightarrow Z$ open. The support projection
formulas give, naturally in $A\in D(R_D)$ and $B\in D(R_Z)$, $$ (v_!i_*A)\otimes^{\mathbf L}B\cong
v_!\bigl(i_*A\otimes^{\mathbf L}v^*B\bigr)\cong v_!i_*\bigl(A\otimes^{\mathbf L}i^*v^*B\bigr). $$
Use the normalized extension comparison $h_!\cong v_!i_*$ and inverse-image composition to obtain
$h_!A\otimes^{\mathbf L}B\cong h_!(A\otimes^{\mathbf L}h^*B)$. These formulas apply to arbitrary
unbounded inputs. Step 1 supplies the quasi-compact complementary opens; step 2 identifies
supportPullback with the specified coefficient-compatible inverse image. The projection maps are
the unit/counit-induced ones, so their restrictions to $D$ are the canonical tensor comparisons
and restriction isomorphisms.
Uses: lem-sfb-condensed-support-projection-formula, lem-sfb-locally-closed-extension-coherence,
def-sfb-condensed-pullback-tensor-comparison, def-sfb-open-closed-internal-hom-comparisons.

5. Factor $b=v\circ i$ with $i:T\hookrightarrow V$ closed and $v:V\hookrightarrow X$ open, let
$k:Z\hookrightarrow X$ be a closed immersion with image $X\setminus V$ and
$u:V^\circ\hookrightarrow V$ the open complement of $i(T)$; both opens are quasi-compact and
$X,V,S,S_V=S\times_XV$ are Noetherian, hence qcqs, by step 1. Base change of $v$ and $i$ along $a$
gives the open $v':S_V\hookrightarrow S$, the projection $a_V:S_V\to V$, the closed
$i':W\hookrightarrow S_V$ with $r=v'i'$, and $s:W\to T$. Apply the base-change mates for the ring
sheaf $R_X$ twice: $\alpha$ for the pair $(k,v)$ along $g=a$ gives $a^*v_!\cong v'_!a_V^*$, and
$\beta$ for the pair $(i,u)$ along $g=a_V$ gives $a_V^*i_*\cong i'_*s^*$. The coefficient rings
there are inverse images of $R_X$, identified with the pulled-back coefficients by step 2. With
the normalized comparisons $b_!\cong v_!i_*$ and $r_!\cong v'_!i'_*$ this gives $a^*b_!M\cong
r_!s^*M$. Its restriction along $r^*$ is the identity of $s^*M$ after the restriction isomorphisms
and inverse-image composition comparisons: the adjoint of $\alpha^{-1}$ is $a_V^*$ of the open
unit followed by the coefficient square comparison, so $v'^*\alpha$ is the canonical
identification, and the adjoint of $\beta$ is the square comparison followed by $s^*$ of the
closed counit, so $i'^*\beta$ is the canonical identification. All functors here are exact and
applied to degree-zero objects, so this is also the corresponding derived identification. Apply
step 4 first with $h=a$, then with $h=r$, using symmetry of tensor for the second application. The
result is the chain $$ a_!L[0]\otimes^{\mathbf L}b_!M[0]\cong a_!\bigl(L[0]\otimes^{\mathbf
L}r_!s^*M[0]\bigr)\cong a_!r_!\bigl(r^*L[0]\otimes^{\mathbf L}s^*M[0]\bigr)\cong c_!P[0]. $$ The
last arrow uses $\gamma_{a,r}:a_!r_!\cong c_!$ and step 3. This proves the displayed isomorphism
by two projection calculations and one base-change input; it does not assume tensor
constructibility.
Uses: lem-sf-ring-sheaf-base-change-mates, def-sf-proetale-ring-sheaf-operations,
lem-weil-pbc-closed-subset-closed-subscheme, lem-sfb-locally-closed-extension-coherence,
sk-def-sfb-derived-tensor-hom.

6. Each constituent of the chain in step 5 is natural in $L,M$. Changing open/closed
factorizations and inserting the normalized extension comparisons gives a second map with the same
source and target. The first isomorphism identifies that source with $c_!P[0]$, so their ratio is
an endomorphism of $c_!P[0]$. After $c^*$, both maps are the ordinary tensor map on $r^*L,s^*M$:
this follows from the unit/counit normalization of the projection maps, the identity normalization
of the base-change isomorphism of step 5, and the identity normalization of $\gamma$. The tensor
symmetries occur twice and cancel on $x\otimes y$. Hence this ratio restricts to the identity. The
bijection on Hom sets induced by $c^*$ for two objects in the image of $c_!$ implies that the
ratio is the identity. This proves independence of factorization in exactly the normalized sense
asserted.
Uses: lem-sfb-locally-closed-extension-coherence, lem-sf-ring-sheaf-base-change-mates,
def-sfb-open-closed-internal-hom-comparisons, def-sfb-condensed-pullback-tensor-comparison.

7. Exactness of $c_!$ implies $\mathcal H^q(c_!P[0])=0$ for $q\ne0$ and $\mathcal
H^0(c_!P[0])=c_!P$. Choose a closed-then-open factorization $c=v i$, with $v:V\hookrightarrow X$.
Partition $X$ into the image of $W$, the open subset $V\setminus i(W)$, and the closed subset
$X\setminus V$, giving the last one its reduced induced closed subscheme structure. These are
disjoint locally closed strata; since $W$ is constructible by intersection of the two
constructible immersion images, all three strata are constructible. Keep the given scheme $W$ as
the first stratum. On it, $c^*c_!P=P$ by extension coherence. On the closed stratum $k':X\setminus
V\hookrightarrow X$, the mate $\alpha$ for $v$ along $k'$ gives $k'^*v_!i_*P\cong v''_!(\cdots)$
with $v''$ the open immersion of the empty scheme $V\times_X(X\setminus V)$, hence zero. On the
open stratum $u':V\setminus i(W)\hookrightarrow X$, factor $u'=vu_0$; then $u'^*c_!P\cong
u_0^*v^*v_!i_*P\cong u_0^*i_*P$ by the restriction isomorphism, and the mate $\beta$ for $i$ along
$u_0$ is extension from the empty fibre product, hence zero. By step 2, on the first stratum $P$
has the finite constant scalar model $R^{mn}=R\otimes_{\Lambda(*)}\Lambda(*)^{mn}$, and elsewhere
the model is zero. This finite stratification verifies the constructibility definition for every
condensed $\Lambda$. If $W$ is empty, all these restrictions are zero; the same formulas cover
zero ranks and the zero ring.
Uses: lem-sfb-locally-closed-extension-coherence, lem-sp-exact-functor-preserves-homology,
lem-weil-pbc-closed-subset-closed-subscheme, def-constructible-stratification,
lem-sf-ring-sheaf-base-change-mates, sk-def-sfb-constructible. -/
theorem locallyClosedGeneratorTensorIntersection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X S T : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b] :
    (∃ e : ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b)
        (C : GeneratorFactorization (pullback.fst a b ≫ a)),
        generatorTensorSource Λ A B ≅ generatorTensorTarget Λ a b C,
      ∀ (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
        (C C' : GeneratorFactorization (pullback.fst a b ≫ a))
        (α : generatorExtension Λ A ≅ generatorExtension Λ A')
        (β : generatorExtension Λ B ≅ generatorExtension Λ B')
        (γ : generatorExtension Λ C ≅ generatorExtension Λ C'),
        Functor.whiskerRight α.hom (upperStar Λ a) ≫ generatorRestriction Λ A' =
          generatorRestriction Λ A →
        Functor.whiskerRight β.hom (upperStar Λ b) ≫ generatorRestriction Λ B' =
          generatorRestriction Λ B →
        Functor.whiskerRight γ.hom (upperStar Λ (pullback.fst a b ≫ a)) ≫
          generatorRestriction Λ C' = generatorRestriction Λ C →
        ∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
          (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
          ((derivedTensor Λ X).map
            ((DerivedCategory.singleFunctor _ 0).map (α.hom.app L.obj))).app
              ((DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ B).obj M.obj)) ≫
            ((derivedTensor Λ X).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((generatorExtension Λ A').obj L.obj))).map
                ((DerivedCategory.singleFunctor _ 0).map (β.hom.app M.obj)) ≫
            ((e A' B' C').hom.app L).app M =
          ((e A B C).hom.app L).app M ≫
            (DerivedCategory.singleFunctor _ 0).map
              (γ.hom.app (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj))) ∧
    (∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
      (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
      (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (pullback a b),
        ∃ m n : U.I₀ → ℕ, ∀ k : U.I₀,
          Nonempty ((upperStar Λ (U.f k ≫ pullback.fst a b)).obj L.obj ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k)) ∧
          Nonempty ((upperStar Λ (U.f k ≫ pullback.snd a b)).obj M.obj ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (n k)) ∧
          Nonempty ((upperStar Λ (U.f k)).obj
            (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj) ≅
              Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k * n k))) ∧
      ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b),
        (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (((generatorTensorSource Λ A B).obj L).obj M))) ∧
        IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ 0).obj
          (((generatorTensorSource Λ A B).obj L).obj M)) ∧
        Nonempty ((upperStar Λ (pullback.fst a b ≫ a)).obj
          ((DerivedCategory.homologyFunctor _ 0).obj
            (((generatorTensorSource Λ A B).obj L).obj M)) ≅
          (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj)) ∧
        ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
          Disjoint (Set.range g) (Set.range (pullback.fst a b ≫ a)) →
          IsZero ((upperStar Λ g).obj ((DerivedCategory.homologyFunctor _ 0).obj
            (((generatorTensorSource Λ A B).obj L).obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
