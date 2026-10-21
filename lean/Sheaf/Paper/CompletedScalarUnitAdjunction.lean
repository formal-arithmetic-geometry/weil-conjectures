/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Sheaf.CategoryTheory.FlatScalarTowerLimitSquare
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.KoszulReconstruction
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector

/-! # Completion-unit-normalized scalar comparison of completed adjunctions

Source: main-20261015, sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-completed-exchange-coherence.proof.md, second paragraph;
strict coefficient supplement, completed scalar unit and adjunction comparison.
Stacks Tags 099M and 099N supply the completion context.
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction).

The small pro-etale model, strict reduction, scalar maps and pullback models are the
published constructions of StrictScalarBalancing. No ring, tower or completion is replaced.
Positive exponent n+1 is indexed by n. Operation choices below retain their ordinary
adjunctions, and the scalar direct comparison is their normalized mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme.CompletedScalar
open StrictScalarBalancing

variable {A : Type (u + 1)} [CommRing A]

/-- The existing local completeness predicate, not a new completion notion.
Source: Stacks 099M and Koszul reconstruction
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
abbrev complete (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  IsComplete (finiteMap (topology T) A d.ideal b 0)

/-- The full complete category with the published intrinsic completeness predicate.
Source: Stacks 099M (blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
abbrev Complete (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  ObjectProperty.FullSubcategory (complete T d b)

/-- Completion and scalar restriction facts which are conclusions, not assumptions,
of the scalar comparison. The quotient criterion fixes the actual completion unit.
Source: Stacks 099M, 099N and constant-completion-equivalence
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
structure CompletionFacts (d : AdicCoefficientDatum A) : Prop where
  criterion : ∀ (T : Scheme.{u}) (b : Bool) (L : D (ring T d b)),
    complete T d b L ↔ IsIso ((completionUnit (topology T) A d.ideal b).app L)
  closed : ∀ (T : Scheme.{u}) (b : Bool) (L : D (ring T d b)),
    complete T d b ((completion (topology T) A d.ideal b).obj L)
  restricts : ∀ (T : Scheme.{u}) (L : D (ring T d true)), complete T d true L →
    complete T d false ((dres (scalar T d)).obj L)

/-- Restriction on the full complete categories, using the actual scalar functor.
Source: Stacks 099I (blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def CompletionFacts.restriction {d : AdicCoefficientDatum A} (H : CompletionFacts d)
    (T : Scheme.{u}) : Complete T d true ⥤ Complete T d false :=
  ObjectProperty.lift (complete T d false)
    (ObjectProperty.ι (complete T d true) ⋙ dres (scalar T d))
    (fun L ↦ H.restricts T L.obj L.property)

/-- The compatible-family/K-injective normalization of the existing scalar-limit
comparison. All its maps are the recorded universal right-derived transformations.
Source: Stacks 0940, 0A07; flat-scalar-tower-limit-square
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def LimitNormalized (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (lambda : rlim (ring T d true) ⋙ dres (scalar T d) ≅
      tdres (scalar T d) ⋙ rlim (ring T d false)) : Prop :=
  ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (ring T d true)) ℤ,
    (dres (scalar T d)).map ((limitComparison (ring T d true)).app P) ≫
        lambda.hom.app ((TQ (ring T d true)).obj P) =
      (resFactors (scalar T d)).inv.app ((ordinaryLimit (ring T d true)).obj P) ≫
        (Q (ring T d false)).map ((limitRestriction (scalar T d)).hom.app P) ≫
        (limitComparison (ring T d false)).app
          (((tres (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (rlim (ring T d false)).map ((tresFactors (scalar T d)).hom.app P)

/-- The scalar completion comparison is the specified limit comparison followed by
strict balancing, including its strict transitions.
Source: strict coefficient supplement, proof Step 3
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def completionComparison (d : AdicCoefficientDatum A) (B : Balancing d)
    (T : Scheme.{u})
    (lambda : rlim (ring T d true) ⋙ dres (scalar T d) ≅
      tdres (scalar T d) ⋙ rlim (ring T d false)) :
    completion (topology T) A d.ideal true ⋙ dres (scalar T d) ≅
      dres (scalar T d) ⋙ completion (topology T) A d.ideal false :=
  (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft (reduction T d true) lambda ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (B.ρ T) (rlim (ring T d false)) ≪≫
    Functor.associator _ _ _

/-- The ordinary right adjoints and their normalized scalar mate, for the actual
pullbacks supplied by strict balancing. These are the operations stipulated by the node;
there is no completeness hypothesis on ordinary pullback or any ambient object.
Source: flat-ringed-diagram-restriction and pro-etale operations
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
structure Operations (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V) where
  pull : PullCompatibility f d (B.ρ V) (B.ρ U)
  rightA : D (ring U d true) ⥤ D (ring V d true)
  right0 : D (ring U d false) ⥤ D (ring V d false)
  adjA : pull.completed.ordinary ⊣ rightA
  adj0 : pull.constant.ordinary ⊣ right0
  χ : rightA ⋙ dres (scalar V d) ≅ dres (scalar U d) ⋙ right0
  χ_normalized : χ.hom =
    (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ pull.a.inv)).natTrans

/-- The appropriate ordinary pullback, without any completion.
Source: pro-etale operations
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.ordinary {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (b : Bool) :
    D (ring V d b) ⥤ D (ring U d b) :=
  match b with
  | false => O.pull.constant.ordinary
  | true => O.pull.completed.ordinary

/-- The appropriate strict-diagram pullback, retaining every transition.
Source: pro-etale operations and diagram-site realization
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.diagrams {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (b : Bool) :
    TD (ring V d b) ⥤ TD (ring U d b) :=
  match b with
  | false => O.pull.constant.diagrams
  | true => O.pull.completed.diagrams

/-- Ordinary pullback followed by the specified quotient completion, on complete inputs.
Source: completed pullback; Stacks 099N
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.completedPull {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (H : CompletionFacts d)
    (b : Bool) : Complete V d b ⥤ Complete U d b :=
  ObjectProperty.lift (complete U d b)
    (ObjectProperty.ι (complete V d b) ⋙ O.ordinary b ⋙
      completion (topology U) A d.ideal b)
    (fun L ↦ H.closed U b ((O.ordinary b).obj L.obj))

/-- The fixed reconstruction, namely derived limit of canonical strict reassociation.
Source: completed pullback; strict coefficient supplement, proof Step 4
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.reconstruction {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (b : Bool) :
    O.ordinary b ⋙ completion (topology U) A d.ideal b ≅
      reduction V d b ⋙ O.diagrams b ⋙ rlim (ring U d b) :=
  match b with
  | false => (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight O.pull.constantReassociation (rlim (ring U d false)) ≪≫
        Functor.associator _ _ _
  | true => (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight O.pull.τ (rlim (ring U d true)) ≪≫
        Functor.associator _ _ _

/-- The strict q comparison, before taking the derived limit.
Source: strict quotient scalar balancing, displayed pullback equation
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.quotientComparison {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) :
    (reduction V d true ⋙ O.pull.completed.diagrams) ⋙ tdres (scalar U d) ≅
      dres (scalar V d) ⋙ reduction V d false ⋙ O.pull.constant.diagrams :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reduction V d true) O.pull.p ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (B.ρ V) O.pull.constant.diagrams ≪≫
    Functor.associator _ _ _

/-- The component from the two published completed-pullback functors to constant modules.
Source: strict coefficient supplement, phi
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
abbrev Operations.ComparisonType {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) :=
  (ObjectProperty.ι (complete V d true) ⋙ O.ordinary true ⋙
    completion (topology U) A d.ideal true) ⋙ dres (scalar U d) ≅
      ObjectProperty.ι (complete V d true) ⋙ dres (scalar V d) ⋙
        O.ordinary false ⋙ completion (topology U) A d.ideal false

/-- The completion-unit normalization fixes phi uniquely on the full complete category.
Source: strict coefficient supplement, proof Step 5
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.UnitNormalized {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (φ : O.ComparisonType) : Prop :=
  ∀ L : Complete V d true,
    (dres (scalar U d)).map ((completionUnit (topology U) A d.ideal true).app
        (O.pull.completed.ordinary.obj L.obj)) ≫ φ.hom.app L =
      O.pull.a.hom.app L.obj ≫ (completionUnit (topology U) A d.ideal false).app
        (O.pull.constant.ordinary.obj ((dres (scalar V d)).obj L.obj))

/-- The complete adjunction comparison, including actual Hom bijections, units,
counits, strict reconstruction and arbitrary changes of the constant complete input.
Every completeness assertion here is an output of the theorem. The `mate` field
identifies the full adjunctions, and `conjugation` expresses preservation of all
adjunction conjugates, in particular the canonical direct-image composition and
identity maps, including composites of edges as the other adjunction.
Source: strict coefficient supplement, proof Steps 4--9; Stacks 099M, 099N
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
structure Comparison {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (H : CompletionFacts d)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false)) where
  pushA : ∀ N : D (ring U d true), complete U d true N →
    complete V d true (O.rightA.obj N)
  push0 : ∀ N : D (ring U d false), complete U d false N →
    complete V d false (O.right0.obj N)
  adjA : O.completedPull H true ⊣
    ObjectProperty.lift (complete V d true)
      (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
      (fun N ↦ pushA N.obj N.property)
  adj0 : O.completedPull H false ⊣
    ObjectProperty.lift (complete V d false)
      (ObjectProperty.ι (complete U d false) ⋙ O.right0)
      (fun N ↦ push0 N.obj N.property)
  homA : ∀ (L : Complete V d true) (N : Complete U d true)
    (t : (O.completedPull H true).obj L ⟶ N),
    (adjA.homEquiv L N t).hom = O.adjA.homEquiv L.obj N.obj
      ((completionUnit (topology U) A d.ideal true).app
        (O.pull.completed.ordinary.obj L.obj) ≫ t.hom)
  hom0 : ∀ (L : Complete V d false) (N : Complete U d false)
    (t : (O.completedPull H false).obj L ⟶ N),
    (adj0.homEquiv L N t).hom = O.adj0.homEquiv L.obj N.obj
      ((completionUnit (topology U) A d.ideal false).app
        (O.pull.constant.ordinary.obj L.obj) ≫ t.hom)
  φ : O.ComparisonType
  unit_normalized : O.UnitNormalized φ
  unique : ∀ ψ : O.ComparisonType, O.UnitNormalized ψ → ψ = φ
  reconstruction : ∀ L : Complete V d true,
    (dres (scalar U d)).map ((O.reconstruction true).hom.app L.obj) ≫
        lambda.hom.app ((O.pull.completed.diagrams).obj ((reduction V d true).obj L.obj)) ≫
        (rlim (ring U d false)).map (O.quotientComparison.hom.app L.obj) =
      φ.hom.app L ≫ (O.reconstruction false).hom.app ((dres (scalar V d)).obj L.obj)
  hom_comparison : ∀ (L : Complete V d true) (N : Complete U d true)
    (t : (O.completedPull H true).obj L ⟶ N),
    (adj0.homEquiv ((H.restriction V).obj L) ((H.restriction U).obj N)
      (ObjectProperty.homMk (φ.inv.app L ≫ (dres (scalar U d)).map t.hom))).hom =
        (dres (scalar V d)).map (adjA.homEquiv L N t).hom ≫ O.χ.hom.app N.obj
  unit : ∀ L : Complete V d true,
    (dres (scalar V d)).map (adjA.unit.app L).hom ≫
        O.χ.hom.app ((O.completedPull H true).obj L).obj ≫ O.right0.map (φ.hom.app L) =
      (adj0.unit.app ((H.restriction V).obj L)).hom
  counit : ∀ N : Complete U d true,
    φ.inv.app ⟨O.rightA.obj N.obj, pushA N.obj N.property⟩ ≫
        (dres (scalar U d)).map (adjA.counit.app N).hom =
      (O.ordinary false ⋙ completion (topology U) A d.ideal false).map
          (O.χ.hom.app N.obj) ≫ (adj0.counit.app ((H.restriction U).obj N)).hom
  φ_complete : O.completedPull H true ⋙ H.restriction U ≅
    H.restriction V ⋙ O.completedPull H false
  φ_complete_eq : ∀ L : Complete V d true, (φ_complete.hom.app L).hom = φ.hom.app L
  χ_complete :
    ObjectProperty.lift (complete V d true)
        (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
        (fun N ↦ pushA N.obj N.property) ⋙ H.restriction V ≅
      H.restriction U ⋙ ObjectProperty.lift (complete V d false)
        (ObjectProperty.ι (complete U d false) ⋙ O.right0)
        (fun N ↦ push0 N.obj N.property)
  χ_complete_eq : ∀ N : Complete U d true,
    (χ_complete.hom.app N).hom = O.χ.hom.app N.obj
  mate : (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φ_complete.inv)).natTrans =
    χ_complete.hom
  conjugation :
    ∀ (F : Complete V d true ⥤ Complete U d true)
      (R : Complete U d true ⥤ Complete V d true)
      (F₀ : Complete V d false ⥤ Complete U d false)
      (R₀ : Complete U d false ⥤ Complete V d false)
      (a : F ⊣ R) (a₀ : F₀ ⊣ R₀)
      (φ' : F ⋙ H.restriction U ≅ H.restriction V ⋙ F₀)
      (χ' : R ⋙ H.restriction V ≅ H.restriction U ⋙ R₀),
      (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ φ'.inv)).natTrans = χ'.hom →
      ∀ (α : ObjectProperty.lift (complete V d true)
          (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
          (fun N ↦ pushA N.obj N.property) ⟶ R)
        (β : ObjectProperty.lift (complete V d false)
          (ObjectProperty.ι (complete U d false) ⋙ O.right0)
          (fun N ↦ push0 N.obj N.property) ⟶ R₀),
        (∀ N : Complete U d true,
          (H.restriction V).map (α.app N) ≫ χ'.hom.app N =
            χ_complete.hom.app N ≫ β.app ((H.restriction U).obj N)) →
        ∀ L : Complete V d true,
          (H.restriction U).map (((conjugateEquiv adjA a).symm α).app L) ≫
              φ_complete.hom.app L =
            φ'.hom.app L ≫ ((conjugateEquiv adj0 a₀).symm β).app
              ((H.restriction V).obj L)
  change_input : ∀ (L : Complete V d true) (L₀ : Complete V d false)
    (h : (dres (scalar V d)).obj L.obj ⟶ L₀.obj),
    (dres (scalar U d)).map ((O.reconstruction true).hom.app L.obj) ≫
        lambda.hom.app ((O.pull.completed.diagrams).obj ((reduction V d true).obj L.obj)) ≫
        (rlim (ring U d false)).map (O.quotientComparison.hom.app L.obj) ≫
        (O.pull.constant.diagrams ⋙ rlim (ring U d false)).map
          ((reduction V d false).map h) =
      φ.hom.app L ≫ (O.ordinary false ⋙ completion (topology U) A d.ideal false).map h ≫
        (O.reconstruction false).hom.app L₀.obj

/-- Restriction identifies the actual quotient units on every ambient input, and the
unique completion-unit-normalized pullback comparison identifies the completed
adjunctions, their strict reconstruction and their Hom bijections. The operations in
`Operations` are the stipulated normalized ordinary operations, with arbitrary choices
of their universal derived presentations. In particular their direct images of complete
objects are complete, so they can themselves be substituted for the complete input.

Source: main-20261015, completed-exchange-coherence proof, second paragraph;
strict scalar supplement, Stacks Tags 099M and 099N
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction).

Proof plan:
1. Put $C_T^a=\mathcal L_T^a\mathcal R_T^a$ and $C_T^0=\mathcal L_T^0\mathcal R_T^0$, and denote
their quotient units by $c^a,c^0$. Choose finite generators of $I$. Apply the ringed Koszul
reflector to their images in $A_T$; the Koszul/quotient comparison identifies its unit with
$c^a$. Thus $C_T^aM$ is complete and precomposition with $c_M^a$ is a bijection into every
complete $A_T$-object, for every ambient $M$. The constant-coefficient completion adjunction
gives the identical assertion for $C_T^0,c^0$. The coefficient equivalence identifies these
local complete subcategories with those in the statement and says $A_T$ is flat over $\underline
A_T$. Hence the exact restriction functors, their preservation of K-injectives, and the
normalized scalar comparisons apply. No completeness of $M$ has been assumed.
Uses: lem-weil-pbc-ringed-koszul-completion-reflector, prop-weil-pbc-koszul-reconstruction, lem-
sp-completed-pullback-adjunction, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-
flat-ringed-diagram-restriction.
2. Write $e_T^a:M\to\mathcal L_T^a\Delta M$ and $e_T^0:r_TM\to\mathcal L_T^0\Delta r_TM$ for the
constant/limit maps used to construct the quotient units. The specified $\lambda$ satisfies
$\lambda_{\Delta M}r_T(e_T^a)=e_T^0$. Indeed, choose a complex representing $M$ and a
K-injective tower replacement $\Delta M\to H$. Restriction is exact and preserves K-injectives,
so $\Delta r_TM\to r_TH$ is an allowed replacement for the other side. The first map is the
compatible-family map $r_TM\to r_T\lim H$ followed by $r_T\lim H\to\lim r_TH$; the second is the
map into $\lim r_TH$ with those same component maps. These are equal by the defining universal
property of the ordinary limit. This computes the specified derived comparison, since its
normalization is precisely the ordinary comparison conjugated by the total-derived units. The
equality consequently holds on the derived categories, independently of the chosen replacement.
Uses: def-weil-pbc-completed-pullback, lem-weil-pbc-flat-ringed-diagram-restriction, lem-weil-
pbc-flat-scalar-tower-limit-square.
3. Let $h_M^a:\Delta M\to\mathcal R_T^aM$ and $h_{r_TM}^0:\Delta r_TM\to\mathcal R_T^0r_TM$ be
the strict quotient augmentations. Define $\beta_M=\mathcal L_T^0(\rho_M)\lambda_{\mathcal
R_T^aM}:r_TC_T^aM\xrightarrow{\sim}C_T^0r_TM$. Strict balancing says
$\rho_Mr_T(h_M^a)=h_{r_TM}^0$. Naturality of $\lambda$ and Step 2 therefore give
$$\beta_Mr_T(c_M^a)=\mathcal L_T^0(\rho_Mr_T(h_M^a))\lambda_{\Delta M}r_T(e_T^a)=\mathcal
L_T^0(h_{r_TM}^0)e_T^0=c_{r_TM}^0.$$ This proves the asserted identification of the actual
completion units on every ambient input, using equality of strict augmentation maps before
taking the limit.
Uses: lem-weil-pbc-strict-quotient-scalar-balancing, lem-weil-pbc-flat-scalar-tower-limit-
square.
4. Use the canonical pullback/tensor reassociation $\tau_{u,L}:\mathcal R_U^aL_u^aL\cong\mathscr
L_u^a\mathcal R_V^aL$ from strict balancing. In the quotient-completion model for
$F_u^a=C_U^aL_u^a$, its fixed reconstruction is $r_{u,L}=\mathcal L_U^a(\tau_{u,L})$; in any
canonically identified model the same equation includes that model identification. The analogous
constant reconstruction uses $\tau^0:\mathcal R_U^0G_u\cong G_u\mathcal R_V^0$. These
identifications respect the maps from ordinary pullback: applying either side to its quotient
augmentation sends a tensor $x$ to $x\otimes1$, at every quotient, with its quotient transition.
They are exactly the strict-tower maps used in the definition of $j^a,j^0$, not maps selected
from their evaluations. With the statement's convention suppressing $\tau^0$, naturality of
$\lambda$ and the balancing equation give $$\mathcal L_U^0(q_{u,L})\lambda_{\mathscr
L_u^a\mathcal R_V^aL}r_U(r_{u,L})=r^0_{u,r_VL}\,C_U^0(a_{u,L})\beta_{L_u^aL}.$$ Indeed, move
$\mathcal L_U^a(\tau_{u,L})$ across $\lambda$ by naturality and substitute
$q_{u,L}r_U(\tau_{u,L})=\mathcal R_U^0(a_{u,L})\rho_{L_u^aL}$, with $\tau^0$ restored on the
right when necessary.
Uses: def-weil-pbc-completed-pullback, lem-weil-pbc-strict-quotient-scalar-balancing, lem-weil-
pbc-flat-scalar-tower-limit-square.
5. Define $\phi_{u,L}=C_U^0(a_{u,L})\beta_{L_u^aL}$, using the quotient-completion models of
Step 4. Both factors are natural isomorphisms, so this is a natural isomorphism; Step 4 is
exactly its displayed reconstruction normalization in the statement. By Step 3 and naturality of
$c^0$, $$\phi_{u,L}r_U(j^a_{u,L})=C_U^0(a_{u,L})c^0_{r_UL_u^aL}=c^0_{G_ur_VL}a_{u,L}=j^0_{u,r_VL
}a_{u,L}.$$ For uniqueness, $\beta_{L_u^aL}$ identifies $r_U(j^a_{u,L})$ with the constant
completion unit. Since its target and $F_u^0r_VL$ are complete, precomposition with this unit is
injective by the constant completion adjunction. Any other comparison satisfying the required
equation equals $\phi_{u,L}$. This argument uses full faithfulness of restriction only on the
complete subcategories; it makes no full-faithfulness assertion about the ambient categories.
Uses: lem-sp-completed-pullback-adjunction, lem-weil-pbc-constant-completion-equivalence.
6. Let $L$ and $N$ be complete on $V$ and $U$, respectively. Direct image preserves
completeness, so the ordinary adjunction restricts after composing with the completion
reflector. Its Hom bijection sends $t:F_u^aL\to N$ first to $t j^a_{u,L}:L_u^aL\to N$, and then
to its ordinary adjunct $L\to R_u^aN$. The first operation is bijective by Step 1; the second is
the ordinary derived adjunction. This defines $F_u^a\dashv R_u^a$. On constant coefficients
these are precisely the two Hom bijections specifying $F_u^0\dashv R_u^0$. To compare them put
$t_0=r_U(t)\phi_{u,L}^{-1}$. The unit equation from Step 5 gives
$$t_0j^0_{u,r_VL}=r_U(tj^a_{u,L})a_{u,L}^{-1}.$$ The normalized scalar adjunction comparison
says that the ordinary adjunct of the right side is $\chi_{u,N}r_V((tj^a_{u,L})^\sharp)$. Hence
the two completed Hom bijections agree under restriction, $\phi$ and $\chi$. The coefficient
equivalences on complete subcategories supply the required bijections on both Hom sets.
Uses: prop-weil-pbc-direct-image-limits, def-weil-pbc-proetale-operations, lem-sp-completed-
pullback-adjunction, lem-weil-pbc-flat-ringed-diagram-restriction, lem-weil-pbc-constant-
completion-equivalence.
7. A unit is the adjunct of the identity on the left-adjoint value, and a counit is the inverse
adjunct of the identity on the right-adjoint value. Applying the equality of Hom bijections in
Step 6 to these identities proves their compatibility, including the indicated $\phi$ and $\chi$
components. For composition, the scalar inverse-image comparisons $a_u$ come from the identical
inverse image on underlying abelian sheaves, so the comparison for $uv$ equals the composite
comparisons for $u$ and $v$, and the identity comparison is the identity. The ordinary direct-
image composition maps are the adjunction conjugates of these inverse-image composition
identifications. Applying the adjunct compatibility of flat restriction to their defining
adjuncts shows that $\chi$ carries the completed-coefficient direct-image composition and
identity maps to the constant-coefficient ones: both have the same adjunct, hence are equal.
Finally the completed pullback composition and identity maps are, by definition, their
conjugates for the completed adjunctions. Step 6 identifies those adjunctions, so applying the
same Hom bijections to the defining conjugates identifies the completed pullback maps as well.
Bijectivity of conjugation rules out any additional automorphism in these identifications.
Uses: def-weil-pbc-adjunction-conjugate, lem-weil-pbc-flat-ringed-diagram-restriction, def-weil-
pbc-proetale-operations, lem-weil-pbc-profinite-coefficient-inverse-image.
8. All maps used in Step 4 are natural transformations in the derived strict-tower categories:
strict balancing supplies natural $\rho,q$, and the scalar limit square supplies natural
$\lambda$. Thus applying functoriality to any morphism of complete inputs gives the
reconstruction equality on that morphism. More explicitly, for an isomorphism
$h:r_VL\xrightarrow{\sim}L_0$ of constant complete objects, postcompose the equality by
$\mathcal L_U^0G_u(\mathcal R_V^0h)$. Naturality of $r^0$ gives $$\mathcal L_U^0G_u(\mathcal
R_V^0h)\mathcal L_U^0(q_{u,L})\lambda\,r_U(r_{u,L})=r^0_{u,L_0}F_u^0(h)\phi_{u,L}.$$ This is the
asserted normalization after changing the identification of the constant complete input, with
the induced strict reduction and completed-pullback maps. Invertibility of $h$ makes all
comparison maps isomorphisms; the same computation works for arbitrary morphisms.
Uses: lem-weil-pbc-strict-quotient-scalar-balancing, lem-weil-pbc-flat-scalar-tower-limit-
square, def-weil-pbc-completed-pullback.
9. For any morphism $f$ and any complete $K$, $R_f^aK$ is complete by direct-image preservation.
Substitute $L=R_f^aK$ in Steps 4–8. Every argument there is in the unbounded ambient or full
complete categories and uses only the stipulated coefficient datum. Consequently this
substitution imposes none of properness, boundedness, constructibility, or etale origin.
Uses: prop-weil-pbc-direct-image-limits.
-/
theorem completedScalarUnitAdjunction (d : AdicCoefficientDatum A) (B : Balancing d) :
    ∃ H : CompletionFacts d,
      (∀ T : Scheme.{u}, (H.restriction T).IsEquivalence) ∧
      ∃ lambda : ∀ T : Scheme.{u},
          rlim (ring T d true) ⋙ dres (scalar T d) ≅
            tdres (scalar T d) ⋙ rlim (ring T d false),
        (∀ T : Scheme.{u}, LimitNormalized T d (lambda T)) ∧
        (∀ (T : Scheme.{u}) (L : D (ring T d true)),
          (dres (scalar T d)).map ((completionUnit (topology T) A d.ideal true).app L) ≫
              (completionComparison d B T (lambda T)).hom.app L =
            (completionUnit (topology T) A d.ideal false).app
              ((dres (scalar T d)).obj L)) ∧
        (∀ (U V : Scheme.{u}) (f : U ⟶ V), Nonempty (Operations d B f)) ∧
        ∀ (U V : Scheme.{u}) (f : U ⟶ V) (O : Operations d B f),
          Nonempty (Comparison O H (lambda U)) := by
  sorry


end AlgebraicGeometry.Scheme.CompletedScalar
