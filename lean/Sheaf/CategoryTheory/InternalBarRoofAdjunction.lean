/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift

/-! # Internal bar roofs and the normalized derived adjunction

Source: main-20261015 blueprint, direct-image stability proof, paragraph (3), internal
bar normalization; the agent-formulated expansion and its thirteen proof steps are in
`lem-sfb-internal-bar-roof-adjunction`.
(blueprint: lem-sfb-internal-bar-roof-adjunction).

`Normalization` specifies actual chain maps by their components and generator formulas.
The only existence assertion is `normalized_roofs`; no definition chooses data from it.
The compatible bar model, invariant inclusion and finite total are the landed ones.

## Main definitions

* `complex` is the homogeneous bar resolution in nonpositive cochain degrees.
* `phi` and `roof` are the canonical derived transpose and localized cocycle roof.
* `Normalization` gives the component formulas and both signed comparisons.

## Main statements

* `normalized_roofs` asserts these formulas for every compatible internal bar model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (trivial)
namespace CategoryTheory.CondensedBarRoof
variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [HasDerivedCategory.{u + 2} (Equivariant A G)] [HasDerivedCategory.{u + 2} (Modules A)]

/-- The existing single complex, with its category universe explicit.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
abbrev single {C : Type v} [Category.{w} C] [HasZeroObject C] [HasZeroMorphisms C]
    (n : ℤ) (X : C) := (HomologicalComplex.single C (.up ℤ) n).obj X

/-- The homogeneous bar chain complex with the recorded deletion differential.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def chain (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) :
    ChainComplex (Equivariant A G) ℕ :=
  ChainComplex.of R.objects R.boundary R.boundary_boundary

/-- The bar cochain complex: P^(-n) = P_n, extended by zero in positive degrees.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def complex (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) :
    CochainComplex (Equivariant A G) ℤ :=
  (chain R).extend ComplexShape.embeddingDownNat

/-- The canonical degree identification for the extension by zero, with no sign change.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def termIso (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) (n : ℕ) :
    (complex R).X (-(n : ℤ)) ≅ R.objects n :=
  (chain R).extendXIso ComplexShape.embeddingDownNat rfl

/-- The canonical shift identification N in degree -q with N[0][q].
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def shiftedSingle {C : Type v} [Category.{w} C] [Preadditive C] [HasZeroObject C]
    (X : C) (q : ℤ) : single (-q) X ≅ (single 0 X)⟦q⟧ :=
  ((CochainComplex.singleFunctors C).shiftIso q (-q) 0 (add_neg_cancel q)).symm.app X

section Transpose
variable {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{u₁} C] [HasDerivedCategory.{u₂} D]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- Exact localization followed by the termwise single comparison. Its specialization
is the canonical identification of trivial inflation of A[0] with the trivial A[0].
Source: blueprint paragraph (3) (blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def inflatedUnitIso (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] (B : C) :
    L.mapDerivedCategory.obj (DerivedCategory.Q.{u₁}.obj (single 0 B)) ≅
      DerivedCategory.Q.{u₂}.obj (single 0 (L.obj B)) :=
  L.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.{u₂}.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app B)

/-- The canonical derived adjunction followed by the canonical shift identification.
Moving the shift to the source before transposing gives the same normalization as
transposing first and then using the canonical shift compatibility. Specialize the
adjunction to trivial inflation and the normalized invariant inclusion.
Source: blueprint paragraph (3) (blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def phi [Abelian.HasKInjectiveResolutions D] {F : D ⥤ C} [F.Additive]
    (adj : L ⊣ F) (B : C) (N : D) (q : ℕ)
    (ρ : DerivedCategory.Q.{u₂}.obj (single 0 (L.obj B)) ⟶
      (DerivedCategory.Q.{u₂}.obj (single 0 N))⟦(q : ℤ)⟧) :
    (DerivedCategory.Q.{u₁}.obj (single 0 B))⟦-(q : ℤ)⟧ ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.{u₂}.obj (single 0 N)) :=
  adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
    ((L.mapDerivedCategory.commShiftIso (-(q : ℤ))).hom.app
      (DerivedCategory.Q.{u₁}.obj (single 0 B)) ≫
      ((shiftEquiv' (DerivedCategory.{u₂} D) (-(q : ℤ)) (q : ℤ)
        (neg_add_cancel (q : ℤ))).toAdjunction.homEquiv _ _).symm
          ((inflatedUnitIso L B).hom ≫ ρ))
end Transpose

/-- The actual localized homogeneous cocycle roof, with the canonical target shift.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def roof {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory.{u} C] {P : CochainComplex C ℤ} {B : C}
    (e : P ⟶ single 0 B) [QuasiIso e]
    (N : C) (q : ℕ) (fbar : P ⟶ single (-(q : ℤ)) N) :
    DerivedCategory.Q.{u}.obj (single 0 B) ⟶
      (DerivedCategory.Q.{u}.obj (single 0 N))⟦(q : ℤ)⟧ :=
  inv (DerivedCategory.Q.{u}.map e) ≫ DerivedCategory.Q.{u}.map fbar ≫
    DerivedCategory.Q.{u}.map (shiftedSingle N (q : ℤ)).hom ≫
      (DerivedCategory.Q.{u}.commShiftIso (q : ℤ)).hom.app (single 0 N)

/-- The existing regular module, typed in the recorded internal-module category.
Source: the tensor unit in the internal-bar statement; Mathlib `Mod.regular`
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def coefficientUnit (A : Ring.{u}) : Modules A := Mod.regular A.toMon.X

/-- The type of homogeneous bar augmentations into the trivial regular module.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
abbrev RoofAugmentation (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) :=
  complex R ⟶ single 0
    ((trivial (R := A.toMon) (P := G)).obj (coefficientUnit A))

/-- The type of row-zero maps, for every equivariant injective resolution.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
abbrev RowFamily (M : Model A G) :=
  ∀ (N : Equivariant A G) (I : InjectiveResolution N),
    (cochains M.bar).obj N ⟶ (totalCochains M.bar).obj I.cocomplex

/-- The type of single-component homogeneous cocycle maps.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
abbrev HomogeneousFamily (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) :=
  ∀ (N : Equivariant A G) (q : ℕ)
    (f : R.objects q ⟶ N) (_hf : R.boundary q ≫ f = 0),
    complex R ⟶ single (-(q : ℤ)) N

/-- The type of inhomogeneous cocycle maps with the existing internal-Hom terms.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
abbrev InhomogeneousFamily (M : Model A G)
    (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) :=
  ∀ (N : Equivariant A G) (q : ℕ)
    (f : R.objects q ⟶ N) (_hf : R.boundary q ≫ f = 0),
    single (q : ℤ) (coefficientUnit A) ⟶ extend ((cochains M.bar).obj N)

/-- The degree-zero component of the augmentation is the recorded bar augmentation.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def augmentationEquation (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G)
    (augmentation : RoofAugmentation R) : Prop :=
  augmentation.f 0 = (termIso R 0).hom ≫ R.augmentation ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv

/-- Each row-zero map is induced by the fixed injective resolution inclusion.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def rowEquation (M : Model A G) (row : RowFamily M) : Prop :=
  ∀ (N : Equivariant A G) (I : InjectiveResolution N) (n : ℕ),
    (row N I).f n = ((cochains M.bar).map (I.ι.f 0)).f n ≫
      (doubleComplex M.bar I.cocomplex).ιTotal (.up ℕ) n 0 n (Nat.add_zero n)

/-- Each homogeneous cocycle map has its specified degree-minus-q component.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def homogeneousEquation (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G)
    (homogeneous : HomogeneousFamily R) : Prop :=
  ∀ (N : Equivariant A G) (q : ℕ)
    (f : R.objects q ⟶ N) (hf : R.boundary q ≫ f = 0),
    (homogeneous N q f hf).f (-(q : ℤ)) = (termIso R q).hom ≫ f ≫
      (HomologicalComplex.singleObjXSelf
        (.up ℤ) (-(q : ℤ)) N).inv

/-- The local homogeneous-to-inhomogeneous formula, on every profinite test object.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def coordinateEquation (M : Model A G)
    (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G)
    (inhomogeneous : InhomogeneousFamily M R) : Prop :=
  ∀ (N : Equivariant A G) (q : ℕ)
    (f : R.objects q ⟶ N) (hf : R.boundary q ≫ f = 0)
    (S : Profinite.{u}) (x : Fin (q + 1) → C(S, G)),
    Profinite.CondensedAction.InternalBar.onSections A.toMon f.val S
      (Profinite.CondensedAction.InternalBar.basis A.toMon G (q + 1)
        (R.objects q) (R.freeIso q) S x) =
    N.act S (x 0)
      ((M.functions.evaluate (power G q) S N.module
        (((HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ)
            (coefficientUnit A)).inv ≫
          (inhomogeneous N q f hf).f (q : ℤ) ≫
          (((cochains M.bar).obj N).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
          (M.bar.term N q).hom).hom.hom.app (op S)
            (Profinite.CondensedAction.InternalBar.regularOne A.toMon S))).val S (𝟙 S)
              (tupleMap (fun i ↦ (x i.castSucc)⁻¹ * x i.succ)))

/-- The signed comparison with the canonical derived adjunction and fixed finite total.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def comparisonEquation (M : Model A G)
    (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G)
    (augmentation : RoofAugmentation R) [QuasiIso augmentation]
    (row : RowFamily M) (homogeneous : HomogeneousFamily R)
    (inhomogeneous : InhomogeneousFamily M R) : Prop :=
  ∀ (N : Equivariant A G) (q : ℕ)
    (f : R.objects q ⟶ N) (hf : R.boundary q ≫ f = 0)
    (I : InjectiveResolution N),
    ((DerivedCategory.Q.{u + 2} (C := Modules A)).commShiftIso (-(q : ℤ))).inv.app
        (single 0 (coefficientUnit A)) ≫
      DerivedCategory.Q.{u + 2}.map
        (((CochainComplex.singleFunctors (Modules A)).shiftIso (-(q : ℤ)) (q : ℤ) 0
          (neg_add_cancel (q : ℤ))).hom.app (coefficientUnit A)) ≫
      DerivedCategory.Q.{u + 2}.map (inhomogeneous N q f hf) ≫
      DerivedCategory.Q.{u + 2}.map
        (HomologicalComplex.extendMap (row N I) ComplexShape.embeddingUpNat) =
    (-1 : ℤ) ^ (q * (q + 1) / 2) •
      (phi M.invariants.adjunction (coefficientUnit A) N q
        (roof augmentation N q (homogeneous N q f hf)) ≫
        M.invariants.functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}.map
          ((DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).inv.app N) ≫
        (M.computation.iso I).hom)

/-- The unique extension cocycle has the negative Mathlib canonical triangle boundary.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def extensionEquation (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G)
    (augmentation : RoofAugmentation R) [QuasiIso augmentation]
    (homogeneous : HomogeneousFamily R) : Prop :=
  ∀ (N E : Equivariant A G) (i : N ⟶ E)
    (p : E ⟶ (trivial (R := A.toMon) (P := G)).obj (coefficientUnit A))
    (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)
    (l : R.objects 0 ⟶ E) (_hl : l ≫ p = R.augmentation),
    ∃ (f : R.objects 1 ⟶ N) (hf : R.boundary 1 ≫ f = 0),
      f ≫ i = R.boundary 0 ≫ l ∧
      (∀ f' : R.objects 1 ⟶ N, f' ≫ i = R.boundary 0 ≫ l → f' = f) ∧
      roof augmentation N 1 (homogeneous N 1 f hf) =
        -DerivedCategory.triangleOfSESδ
          (hS.map_of_exact (HomologicalComplex.single (Equivariant A G) (.up ℤ) 0))

/-- The canonical maps with all six normalization conditions, using the recorded finite total.
The comparison quantifies over every nonnegative equivariant injective resolution.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction). -/
def Normalization (M : Model A G)
    (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) : Prop :=
  ∃ augmentation : RoofAugmentation R,
  ∃ hqi : QuasiIso augmentation,
  letI := hqi
  ∃ row : RowFamily M,
  ∃ homogeneous : HomogeneousFamily R,
  ∃ inhomogeneous : InhomogeneousFamily M R,
    augmentationEquation R augmentation ∧ rowEquation M row ∧
    homogeneousEquation R homogeneous ∧ coordinateEquation M R inhomogeneous ∧
    comparisonEquation M R augmentation row homogeneous inhomogeneous ∧
    extensionEquation R augmentation homogeneous

/-- Every normalized internal bar model has these cocycle roofs, their signed canonical
adjunction comparison, and the negative canonical short-exact-sequence boundary formula.
This retains arbitrary coefficients, profinite groups, cocycles and injective resolutions.
Source: blueprint direct-images proof, paragraph (3), internal bar normalization
(blueprint: lem-sfb-internal-bar-roof-adjunction).

Proof (the node's thirteen steps):
1. Write $\mathcal E$ for equivariant modules and $\mathcal M$ for internal modules. The
restriction-calculus statement makes $\mathcal E$ Grothendieck abelian, makes forgetting exact
and exactness-detecting, and gives the exact trivial-inflation adjunction. Enough injectives
therefore exists by [lem-sp-grothendieck-enough-injectives]. Embed $N$ into an injective $I^0$,
its cokernel into $I^1$, and successively each cokernel into the next injective; the composite
quotient-inclusion maps are the differentials. This gives the nonnegative resolution $a$ of
[def-sp-injective-resolutions]. The Grothendieck category also has K-injective resolutions for
every complex by [lem-sfb-grothendieck-k-injective], as required for the canonical unbounded
shift comparison used below. All profinite powers and module categories use the coefficient
universes in the statement.

2. For the model calculation identify internal modules with module sheaves using
[def-weil-pbc-internal-abelian-sheaf-module-equivalence]. The exact tensor comparison of
[lem-pe-internal-section-tensor-comparison] preserves the unit and relative tensor; closed Hom
is consequently identified by its adjunction, using [lem-pc-sheaf-modules-tensor-closed]. For a
profinite set $S$, the sheafification of $T\mapsto A(T)[C(T,S)]$ is $A[\underline S]$: a map out
is uniquely a natural assignment $s\mapsto m_s$, by the module-sheafification universal property
of [lem-pc-sites-module-sheafification-interface]. This is precisely the presheaf and
sheafification defining $j_{S!}A_S$ in [lem-pc-sites-modules-j-shriek-flat]. That node proves it
flat, including exactness of its tensor functor. Thus $A[\underline G^p]$ and $A[\underline G]$
are flat. This applies on the chosen small skeleton, replacing $S$ by its representative if
necessary.

3. The functor $\operatorname{Ind}(T)=A[\underline G]\otimes_A T$ with translation on the first
factor is left adjoint to forgetting $U$: an equivariant map is uniquely $[g]\otimes t\mapsto g
v(t)$ for $v:T\to UM$, with inverse evaluation at $[1]\otimes t$. These are internal formulas by
the free-module universal property of the bar-resolution statement and the closed tensor
adjunction. Its underlying tensor functor is exact by step 2, so the exactness-detection
assertion of the restriction calculus makes $\operatorname{Ind}$ exact. For equivariantly
injective $J$, extend a map $T\to UJ$ across a monomorphism $T\hookrightarrow T'$ by transposing
to $\operatorname{Ind}(T)\to J$ and using injectivity across the monomorphism
$\operatorname{Ind}(T)\hookrightarrow\operatorname{Ind}(T')$. Hence $UJ$ is injective. Exactness
of $U$ now makes $UN\to UI^\bullet$ a nonnegative injective resolution. Consequently each column
of $D$ computes its derived internal Hom, exactly with the meaning of derived internal Hom in
[lem-sfb-condensed-derived-invariant-bar].

4. Let $\underline{\operatorname{Hom}}_G(P_p,I^r)$ denote the subsheaf of equivariant maps: its
sections at $S$ are $\operatorname{Hom}_{\mathcal E}(A[\underline S]\otimes_A P_p,I^r)$, with
trivial action on the parameter module. The induced coordinates of
[lem-sfb-condensed-internal-bar-resolution], together with the tensor-Hom adjunction, identify
it with $D^{p,r}$. The inverse formula sends a function $c$ to $[g_0,\ldots,g_p]\mapsto
g_0c(g_0^{-1}g_1,\ldots,g_{p-1}^{-1}g_p)$ after every profinite base change. Deletion of
coordinate $0$ gives $g_1c(g_2,\ldots,g_{p+1})$; deletion of an interior coordinate replaces
$g_i,g_{i+1}$ by $g_ig_{i+1}$; deletion of the last drops $g_{p+1}$. Their alternating sum is
exactly $d_h$. Postcomposition with $d_I$ commutes with these faces because $d_I$ is
equivariant. In degree zero the horizontal differential is $m\mapsto(g\mapsto gm-m)$, with
kernel the fully fixed submodule.

5. Fix $r$ and $S$. The bar-resolution statement says $A[\underline S]\otimes_A P_\bullet\to
A[\underline S]$ is exact in $\mathcal E$. Applying $\operatorname{Hom}_{\mathcal E}(-,I^r)$
gives an exact augmented complex of abelian groups: kernel equalities are the quotient universal
property; a map out of an image extends to the ambient object by the extension property of the
injective $I^r$. Thus the augmented row $\Gamma_G I^r\to D^{\bullet,r}$ is exact on every $S$,
hence as sheaves. In particular its augmentation is the invariant inclusion, rather than an
arbitrary row comparison. The map $b$ is a double-complex map from $\Gamma_G I^\bullet$ in
horizontal degree zero.

6. Apply [lem-sc-first-quadrant-total-column-comparison] after interchanging the two indices to
the double-complex map in step 5. The row quasi-isomorphisms just proved are precisely its
column hypothesis. The interchanged total has differential $d_I+(-1)^r d_h$; multiplication by
$(-1)^{pr}$ in bidegree $(p,r)$ identifies it with the fixed total $d_h+(-1)^p d_I$, since the
horizontal ratio is $(-1)^r$ and the vertical ratio is $(-1)^p$. Thus $b$ is a quasi-isomorphism
in the fixed convention. Each diagonal has at most $n+1$ summands, so no infinite-total or
global-sections exactness assertion is involved. Step 3 and
[lem-sfb-condensed-derived-invariant-bar] identify this compatible derived bar total with the
one in the statement. The restriction calculus computes $R\Gamma_G N$ by $\Gamma_G I^\bullet$;
this proves that $Q(b)$ defines the stated augmentation isomorphism $\epsilon_N$. The map
induced by $a$ into row zero is $j_N$.

7. The bar resolution is exact augmented to $A$, hence $e:P\to A[0]$ is a quasi-isomorphism. The
single-component map $\bar f:P\to N[q]$ is a chain map: its only potentially nontrivial chain
condition is $f\partial_{q+1}=0$. Step 4 carries this equality to $d_hc_f=0$, giving the
required map $A[-q]\to V^\bullet(N)$. Both assertions hold also at $q=0$: the condition means
that $f$ factors through the augmentation, and its inhomogeneous value is invariant.

8. The shifted complex $I[q]$ is bounded below and termwise injective, so is K-injective by
[lem-weil-pbc-bounded-below-injectives-kinjective]. By [lem-sc-kinjective-quasi-iso-comparison],
the derived morphism $Q(a[q])\rho_f:A[0]\to Q(I[q])$ has a chain-map representative $h:A[0]\to
I[q]$. Moreover $he$ and $a[q]\bar f$ have the same derived image, and the same bijectivity for
source $P$ says that they are chain-homotopic. This argument allows the unbounded-to-the-left
source $P$; only the target is bounded below. It does not require the terms of $P$ to be
projective.

9. Transpose $h$ termwise under trivial inflation and invariants to $\widetilde
h:A[0]\to\Gamma_G I[q]$: its component is $h^0:A\to I^q$ with invariant image. The unit and
counit equations in [lem-trf-bounded-below-derived-adjunction] identify this termwise transpose,
after the canonical injective computation, with the canonical derived-adjunction image of
$Q(a[q])\rho_f$. Indeed the derived transpose is the derived right-adjoint image followed by its
unit; the stated unit equation substitutes the termwise unit, and its naturality moves $h$
through it. Exact trivial inflation and enough equivariant injectives, supplied in step 1, are
precisely that lemma's hypotheses. The canonical shift compatibility of
[lem-sp-canonical-right-derived-adjunction-shift] identifies its shift with $\Phi_q(\rho_f)$,
represented by the same component $A[-q]\to\Gamma_G I^\bullet$. No degree-dependent
renormalization of the adjunction is being chosen.

10. Perform the following calculation with morphism groups in $\mathcal E$. Put
$C^n=\prod_{p\geq0}\operatorname{Hom}_{\mathcal E}(P_p,I^{n-p})$; its nonzero factors have
$0\leq p\leq n$, so the product is finite, and it is zero for $n<0$. On a homogeneous family $x$
of degree $n$, define $\delta x=d_Ix-(-1)^nx\partial$. Expanding twice gives $\delta^2=0$. The
condition $\delta x=0$ is exactly the chain-map condition $P\to I[n]$. A chain homotopy $H$
between such maps has $u-v=(-1)^nd_IH+H\partial=(-1)^n\delta H$. Thus homotopic chain maps give
the same class modulo boundaries in $C^n$. This is a direct calculation of the cochain and shift
definitions, with no internal-Hom derived comparison theorem used.

11. By step 4 and the tensor unit adjunction, $\operatorname{Hom}_{\mathcal
E}(P_p,I^r)=\operatorname{Hom}_{\mathcal M}(A,D^{p,r})$. Identify these groups and define
$T:C^\bullet\to\operatorname{Hom}_{\mathcal M}(A,\operatorname{Tot}D)$ by multiplying bidegree
$(p,r)$ by $$t(p,r)=(-1)^{pr+p(p+1)/2}.$$ The vertical part of $\delta$ has coefficient $1$,
whereas its horizontal part on $(p,r)$ has coefficient $(-1)^{p+r+1}$. The identities
$t(p,r+1)=(-1)^pt(p,r)$ and $(-1)^{p+r+1}t(p+1,r)=t(p,r)$ therefore give
$T\delta=d_{\operatorname{Tot}}T$. Finite biproducts allow the displayed Hom into the total to
be calculated summandwise; no exactness of this Hom functor is used.

12. Apply steps 10 and 11 to the homotopy of step 8. The map $a[q]\bar f$ occupies only bidegree
$(q,0)$, so its image under $T$ is $(-1)^{q(q+1)/2}$ times the cocycle for $j_Nc_f$. The map
$he$ occupies only $(0,q)$ and $t(0,q)=1$, so its image under $T$ is the cocycle for
$b\widetilde h$. Their difference is a boundary in $\operatorname{Hom}_{\mathcal
M}(A,\operatorname{Tot}D)$. Such a boundary $d k$ is exactly a chain homotopy between the
corresponding maps $A[-q]\to\operatorname{Tot}D$, since the source has zero differential and a
homotopy has sole component $k:A\to(\operatorname{Tot}D)^{q-1}$. Localizing gives
$s_qj_NQ(c_f)=\epsilon_N\Phi_q(\rho_f)$. Multiplying by $s_q=s_q^{-1}$ proves the asserted
equation. For $q=0$ this is the invariant inclusion and $s_0=1$; for $q=1$ the factor is $-1$.
The calculation used no choice except the arbitrary resolution and representative $h$, so the
same signs work for every one of these choices.

13. For the extension clause, $p\ell\partial_1=e\partial_1=0$, so the kernel property of $i$
gives the unique equivariant $f$; and $if\partial_2=\ell\partial_1\partial_2=0$, so
$f\partial_2=0$ since $i$ is monic. Use the actual cone $C(i)$ of $N[0]\to E[0]$: it has $N$ in
degree $-1$, $E$ in degree $0$, and differential $i$. Its map $v:C(i)\to A[0]$ is $p$ in degree
zero. Its only cohomology is $\operatorname{coker}i=A$ in degree zero, so $v$ is a
quasi-isomorphism. The maps $\kappa^{-1}=f$, $\kappa^0=\ell$ and zero in other degrees define
$\kappa:P\to C(i)$, since $if=\ell\partial_1$ and $f\partial_2=0$. We have $v\kappa=e$ and
$\operatorname{pr}\kappa=\bar f$. These are the cone, projection and quasi-isomorphism of the
statement, so by the formula there (the boundary of [lem-weil-pbc-complex-ses-triangle] built
from the cone arrow $-\operatorname{pr}$ of [def-weil-abstract-derived-category])
$\delta=-Q(\operatorname{pr})Q(v)^{-1}$. Substituting $Q(v)Q(\kappa)=Q(e)$ gives $\delta=-Q(\bar
f)Q(e)^{-1}=-\rho_f$. This also specifies the alternative normalization $\delta^+=\rho_f$
without confusing it with the canonical triangle boundary.
-/
theorem normalized_roofs (M : Model A G)
    (R : Profinite.CondensedAction.InternalBar.Resolution A.toMon G) :
    Normalization M R := by
  sorry

end CategoryTheory.CondensedBarRoof
