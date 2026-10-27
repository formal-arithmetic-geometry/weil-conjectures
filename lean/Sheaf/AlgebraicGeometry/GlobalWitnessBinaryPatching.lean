/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent
import Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.ConePseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact

/-! # Binary patching relative to a supplied global coefficient witness

Source: agent-formulated prerequisite below the unnumbered Kiehl assertion following
Stacks Project, perfect.tex, Tag 0CSD, lemma-flat-proper-pseudo-coherent-direct-image-general.
The Stacks paragraph does not state this prerequisite; the primary Kiehl descente proof
is WANTED (blueprint: lem-sfb-global-witness-one-degree-binary-patching).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.CoefficientPatching

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The coefficient sheaf in degree zero, using restriction of scalars along the specified
ring map. Source: the definition of M_E in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def coefficient {E A : CommRingCat.{u}} (b : E ⟶ A) : schemeDerivedCategory (Spec E) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings (Spec E).toRingedSpace))
    0).obj (tilde ((ModuleCat.restrictScalars b.hom).obj (ModuleCat.of A A)))

/-- The ordinary scalar action on the structure sheaf. The affine part is the mate of
A → Γ(Spec A, O) under tilde/pullback/global sections, then pulled back along the given
A-structure. Source: the middle arrow defining theta in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def ordinaryAction {E A : CommRingCat.{u}} (b : E ⟶ A)
    {X : Scheme.{u}} (q : X ⟶ Spec A) :
    (Scheme.Modules.pullback (q ≫ Spec.map b)).obj
        (tilde ((ModuleCat.restrictScalars b.hom).obj (ModuleCat.of A A))) ⟶
      SheafOfModules.unit (moduleRings X.toRingedSpace) :=
  (Scheme.Modules.pullbackComp q (Spec.map b)).inv.app _ ≫
    (Scheme.Modules.pullback q).map
      (((Scheme.Modules.tildePullbackAdjunction b).homEquiv _ _).symm
        ((ModuleCat.restrictScalars b.hom).map
          ((tilde.adjunction (R := A)).unit.app (ModuleCat.of A A)))) ≫
    (Functor.Monoidal.εIso (Scheme.Modules.pullback q)).inv

/-- The structure sheaf in degree zero is the specified derived tensor unit.
Source: the unit normalization of the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def singleUnitToUnit (X : Scheme.{u}) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶
      𝟙_ (schemeDerivedCategory X) := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact (DerivedCategory.singleFunctorObjUnitIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).hom

/-- The adjunction pinned to the derived counits used in the canonical composition
comparison, as in schemeDerivedBaseChangeMap. Source: the normalization of theta
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def adjunction {X S : Scheme.{u}} (f : X ⟶ S) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))

/-- The canonical composition constraint fixed by the left-derived counits.
Source: the normalization of theta in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def composition {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) f g

/-- The normalized scalar-action adjoint in the node. The tensor constraint is the
unique canonical comparison of def-pc-derived-pullback-tensor-comparison, the
derived-to-ordinary map on M_E[0] is canonicalSinglePullbackMap, and the two transposes
use the pinned adjunction. All of them, and the composition constraint, are fixed by the
same shared left-derived counit. No flatness is required.
Source: the displayed definition of theta in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def theta {E A : CommRingCat.{u}} (b : E ⟶ A)
    {X Z : Scheme.{u}} (q : Z ⟶ Spec E) (p : X ⟶ Z) (a : X ⟶ Spec A)
    (h : p ≫ q = a ≫ Spec.map b) (G : schemeDerivedCategory Z)
    (K : schemeDerivedCategory X) (delta : G ⟶ (schemeDerivedDirectImage p).obj K) :
    (derivedPullback q).obj (coefficient b) ⊗ G ⟶
      (schemeDerivedDirectImage p).obj K :=
  let τ := Classical.choose (exists_canonicalPullbackTensorComparison p)
  let action := (composition p q).hom.app (coefficient b) ≫
    eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (coefficient b)) h) ≫
    Scheme.Modules.canonicalSinglePullbackMap (a ≫ Spec.map b)
      (tilde ((ModuleCat.restrictScalars b.hom).obj (ModuleCat.of A A))) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (ordinaryAction b a) ≫
    singleUnitToUnit X
  (adjunction p).homEquiv _ _
    (τ ((derivedPullback q).obj (coefficient b)) G ≫
      (action ⊗ₘ ((adjunction p).homEquiv G K).symm delta) ≫ (λ_ K).hom)

/-- Cone with quasi-coherent cohomology vanishing in every degree at or above m.
Existential cone triangles avoid making a noncanonical choice of a cone.
Source: the cone condition in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def ConeBound {X : Scheme.{u}} {P Q : schemeDerivedCategory X}
    (t : P ⟶ Q) (m : ℤ) : Prop :=
  ∃ (C : schemeDerivedCategory X) (v : Q ⟶ C) (z : C ⟶ P⟦(1 : ℤ)⟧),
    Pretriangulated.Triangle.mk t v z ∈ distTriang (schemeDerivedCategory X) ∧
      schemeDerivedQCohProperty X C ∧
      ∀ i : ℤ, m ≤ i → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj C)

/-- The coefficient change morphism W_A → W_E from the specified factorization D → E → A.
Source: the geometry defining A_m(W) in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def stageMap {D E A : CommRingCat.{u}} {W : Scheme.{u}} (f : W ⟶ Spec D)
    (d : D ⟶ E) (b : E ⟶ A) (c : D ⟶ A) (h : d ≫ b = c) :
    pullback f (Spec.map c) ⟶ pullback f (Spec.map d) :=
  pullback.map f (Spec.map c) f (Spec.map d) (𝟙 W) (Spec.map b) (𝟙 (Spec D))
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id _).trans
      ((congrArg (fun k ↦ Spec.map k) h.symm).trans (Spec.map_comp d b)))

/-- The assertion A_m(W): a finite type coefficient stage and a bounded coherent object
with the prescribed normalized map and cone bound. The ring map E → A is part of the
witness, and its compatibility with D → A is retained explicitly.
Source: the definition of A_m(W) in the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def HasApproximation {D A : CommRingCat.{u}} {W : Scheme.{u}}
    (f : W ⟶ Spec D) (c : D ⟶ A)
    (K : schemeDerivedCategory (pullback f (Spec.map c))) (m : ℤ) : Prop :=
  ∃ (E : CommRingCat.{u}) (d : D ⟶ E) (b : E ⟶ A) (h : d ≫ b = c),
    RingHom.FiniteType d.hom ∧
    ∃ G : schemeDerivedCategory (pullback f (Spec.map d)),
      (∃ lo hi : ℤ, ∀ i : ℤ, i < lo ∨ hi < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (moduleRings (pullback f (Spec.map d)).toRingedSpace)) i).obj G)) ∧
      (∀ i : ℤ, RingedSpace.IsCoherent (pullback f (Spec.map d)).toRingedSpace
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (moduleRings (pullback f (Spec.map d)).toRingedSpace)) i).obj G)) ∧
      ∃ delta : G ⟶ (schemeDerivedDirectImage (stageMap f d b c h)).obj K,
        ConeBound (theta b (pullback.snd f (Spec.map d)) (stageMap f d b c h)
          (pullback.snd f (Spec.map c)) (pullback.lift_snd _ _ _) G K delta) m

/-- The inclusion of the base change of an open in the base change of the scheme.
Source: K_W in the statement of the node
(blueprint: lem-sfb-global-witness-one-degree-binary-patching). -/
def openMap {D A : CommRingCat.{u}} {Y : Scheme.{u}} (f : Y ⟶ Spec D)
    (c : D ⟶ A) (U : Y.Opens) :
    pullback (U.ι ≫ f) (Spec.map c) ⟶ pullback f (Spec.map c) :=
  pullback.map (U.ι ≫ f) (Spec.map c) f (Spec.map c) U.ι (𝟙 _) (𝟙 _)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Binary patching of one degree of coefficient approximation, relative to the specified
bounded coherent global witness. Local coefficient algebras are independently existential;
no compatibility or output restriction is prescribed.
Source: agent-formulated obligation below the Kiehl paragraph after Stacks Tag 0CSD,
perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general. The paragraph does
not itself state this obligation; the primary Kiehl descente source is WANTED.
(blueprint: lem-sfb-global-witness-one-degree-binary-patching).

Proof plan from the DAG (all comparisons are derived):
1. If $Y=\varnothing$, take $E=D$, $G=0$, and $\gamma=0$. Every module sheaf and every cone on
this scheme is zero. Otherwise $Y$ is Noetherian, quasi-compact and quasi-separated, and it is
separated as a scheme because it is separated over an affine scheme. Its bounded-coherent object
$F$ is pseudo-coherent. Perfect approximation at cutoff $n$ gives a perfect $Q\to F$ whose cone
is zero in all degrees $i\ge n$. Dependencies: lem-weil-pbc-finite-type-over-noetherian, lem-
weil-pbc-qcqs-over-affine, lem-sc-separated-over-affine-scheme-separated, lem-pc-noetherian-
bounded-coherent-pseudo-coherent, lem-sfb-pseudocoherent-perfect-approximation.

2. Use the dg coefficient model $\mathcal B$ and let $T(P)=\Phi_D(P)=\mathcal B\otimes_{\mathcal
O_Y}^{\mathbf L}P$. The comparison lemma identifies the supplied normalized arrow with
$\nu_D(\gamma)$ on underlying complexes. Compose with $T(Q)\to T(F)$ and call the resulting dg-
linear arrow $t:T(Q)\to\widehat K$. Its cone $C$ is quasi-coherent. Tensor with $A$ over the
constant sheaf $D$ preserves an upper cohomological bound, so the cone of $T(Q)\to T(F)$ is zero
for $i\ge n$. The triangle of cones of the composite therefore gives $H^i(C)=0$ for $i>n$, using
the supplied bound for the original witness. This replacement does not assert flatness of $Y/D$.
Dependencies: def-sfb-dg-coefficient-realization, lem-sfb-dg-coefficient-realization-comparison,
lem-weil-pbc-ringed-tensor-cohomological-bounds, def-weil-triangulated-category, lem-sf-derived-
homology-long-exact.

3. Choose finitely many affine opens $T_j=\operatorname{Spec}S_j$ covering $Y$, each contained
in either $U$ or $V$. Their rings are finite type over $D$; choose
$Q_j=D[x_1,\ldots,x_{r_j}]\twoheadrightarrow S_j$. Restrict a witness for $\mathcal A_n(U)$ or
$\mathcal A_n(V)$ to $T_j$. Open restriction, affine direct image and the normalized comparison
give a finite type $D$-algebra $E_j$, a bounded-coherent module complex $L_j$ over $S_j\otimes_D
E_j$, and a map whose scalar-action cone is zero for $i\ge n$. Thus we retain genuine
restriction of the given local arrow; no common coefficient stage or overlap transition is
chosen. Dependencies: lem-pqf-finite-affine-cover-qc-open, lem-weil-pbc-lft-affine-pairs, lem-
pc-affine-qcoh-derived-equivalence, lem-pc-affine-pushforward-resolution-quasi-iso, lem-pc-
module-pushforward-open-restriction, lem-sfb-dg-coefficient-realization-comparison.

4. Set $Q_{j,E}=E_j[x_1,\ldots,x_{r_j}]$ and $Q_{j,A}=A[x_1,\ldots,x_{r_j}]$. The ring $Q_{j,E}$
is Noetherian and surjects onto $S_j\otimes_D E_j$. Hence $L_j$ has bounded finite cohomology
over $Q_{j,E}$ and admits a bounded-above finite-free representative over that ring. Its scalar
tensor is $Q_{j,A}\otimes_{Q_{j,E}}^{\mathbf L}L_j=A\otimes_{E_j}^{\mathbf L}L_j$: a bounded-
above free $Q_{j,E}$-resolution is also $E_j$-K-flat, since $Q_{j,E}$ is free over $E_j$. It
becomes a bounded-above finite-free $Q_{j,A}$-complex. The scalar-action map to $K_j$ is a
morphism in $D(Q_{j,A})$; forgetting to $Q_j$ gives precisely the normalized local arrow by the
affine pullback/tensor formula. Since its cone is zero for $i\ge n$, truncating the finite-free
source sufficiently far below $n$ proves that $K_j$, restricted to $Q_{j,A}$, is $n$-pseudo-
coherent. Dependencies: lem-weil-pbc-finite-type-algebra-noetherian, pqf-lem-coherent-ft-
locnoeth, lem-weil-pbc-quasi-coherent-finite-type-affine, lem-weil-pbc-noetherian-
pseudocoherent-cohomology-criterion, def-pc-ring-pseudo-coherent-complex, def-pc-ring-m-pseudo-
coherent, lem-pc-module-bounded-flat-kflat, lem-pc-affine-derived-pullback-tensor-tilde, lem-
sfb-dg-coefficient-realization-comparison.

5. The affine restriction of $Q$ has bounded finite cohomology over the Noetherian $S_j$ and
hence over its Noetherian polynomial source $Q_j$. The same finite-free resolution argument
shows that $T(Q)|_{T_j}$, with its $Q_{j,A}$-action, is pseudo-coherent. Use the comparison
node's polynomial restriction: $Q_j\otimes_D R_A\to Q_{j,A}$ is a quasi-isomorphism since
$Q_j/D$ is free, so its derived equivalence takes this dg-linear arrow and its cone to
$D(Q_{j,A})$. The cone criterion, with source parameter $n+1$ and target parameter $n$, makes
$C_j$ $n$-pseudo-coherent. Step 2 gives $H^i(C_j)=0$ for $i>n$, so top-cohomology finiteness
gives a finite $Q_{j,A}$-module $H^n(C_j)$. The dg action on $C$ makes this an $S_j\otimes_D
A$-module: it factors through $H^0(\mathcal B|_{T_j})=S_j\otimes_D A$. A generating list over
$Q_{j,A}$ is then also a generating list over this quotient. Dependencies: lem-weil-pbc-
noetherian-pseudocoherent-cohomology-criterion, lem-pc-ring-pseudo-coherent-iff-all-m, lem-sc-
cone-pseudo-coherent, lem-sc-finite-cohomology, def-sfb-dg-coefficient-realization, lem-sfb-dg-
coefficient-realization-comparison.

6. Take a termwise quasi-coherent complex representing the underlying $C$ on $Y$ and smart-
truncate it above $n$; its last term is the quasi-coherent sheaf of degree-$n$ cycles. On each
affine $T_j$, lift the finite generators of $H^n(C_j)$ from step 5 to sections of these cycles;
surjectivity on sections follows from the exact affine module equivalence. The $S_j$-submodule
generated by those finitely many cycles defines a finite-type quasi-coherent subsheaf on $T_j$.
Extend it as a finite-type quasi-coherent submodule of the global cycle sheaf, separately for
each $j$, and take the finite sum $N$. Since $Y$ is Noetherian, $N$ is coherent. Inclusion of
cycles gives $a_0:N[-n]\to UC$. The image of $H^n(a_0)$ generates $H^n(C)$ after multiplication
by $A$, as is checked on every $T_j$. Dependencies: lem-sfb-qc-separated-quasicoherent-complex-
model, lem-pc-affine-qcoh-derived-equivalence, lem-weil-pbc-module-finite-type-submodule-
extension, pqf-lem-coherent-ft-locnoeth.

7. The coherent object $N[-n]$ is pseudo-coherent on the Noetherian scheme $Y$. Perfect
approximation at cutoff $n$ supplies $P\to N[-n]$ with $P$ perfect, $H^i(P)=0$ for $i>n$, and
$H^n(P)\twoheadrightarrow N$. Compose with $a_0$ to get $a:P\to UC$. Extension--restriction
adjunction for $\mathcal O_Y\to\mathcal B$ gives $\widetilde a:T(P)\to C$. The coefficient
comparison includes this adjunction. Since $R_A$ is nonpositive and $D$-K-flat, $T(P)$ is zero
in degrees $>n$, and its top cohomology is $A\otimes_D H^n(P)$: in a nonpositive resolution the
top total degree is the cokernel of the two adjacent differentials, hence the ordinary tensor of
the two top cohomologies. The map on that cokernel sends $b\otimes x$ to $bH^n(a)(x)$. Step 6
therefore makes $H^n(\widetilde a)$ surjective. Thus $J=\operatorname{Cone}(\widetilde a)$ is
zero for $i\ge n$. Dependencies: lem-pc-noetherian-bounded-coherent-pseudo-coherent, lem-sfb-
pseudocoherent-perfect-approximation, lem-sfb-dg-coefficient-realization-comparison, def-sfb-dg-
coefficient-realization, lem-weil-pbc-ringed-tensor-cohomological-bounds.

8. Form the homotopy pullback $H=\widehat K\times_C^h T(P)$ in the dg category, using $\widehat
K\to C$ from step 2 and $\widetilde a$. Concretely $H=\operatorname{Cone}(\widehat K\oplus
T(P)\to C)[-1]$, where the map is the difference of those two arrows. The mapping-cone triangles
are $T(Q)\to H\to T(P)\to T(Q)[1]$ and $H\xrightarrow{u}\widehat K\to J\to H[1]$. Both $T(Q)$
and $T(P)$ are perfect over $\mathcal B$: their local finite perfect models are scalar
extensions of the ordinary ones. Closure under cones makes $H$ perfect. The second triangle and
step 7 show that $H^i(Uu)$ is an isomorphism for $i>n$ and is surjective for $i=n$. In
particular $H^i(Uu)$ is surjective for every $i\ge n$. This records the cohomological-
epimorphism hypothesis needed in the next step. Dependencies: def-sfb-dg-coefficient-
realization, def-weil-triangulated-category, lem-sfb-dg-coefficient-realization-comparison, lem-
sf-derived-homology-long-exact.

9. Apply finite coherent factorization of a cohomological epimorphism to $H,u$ and $m=n$, using
the surjectivity established in step 8. It supplies a finite type coefficient algebra $D\to E\to
A$, bounded-coherent $G$ on $Y_E$, an ordinary scheme-derived arrow $\delta:G\to R\pi_{E*}K$,
and $\sigma:H\to\Phi_E(G)$ such that $\nu_E(\delta)\sigma=u$ and $H^i(U\sigma)$ is surjective
for all $i\ge n$. Write $v=U\nu_E(\delta)$. For $i>n$, the composite
$H^i(v)H^i(U\sigma)=H^i(Uu)$ is an isomorphism and the first factor out of $H^i(UH)$ is
surjective; hence $H^i(U\sigma)$ is also injective and $H^i(v)$ is an isomorphism. In degree
$n$, surjectivity of the composite gives surjectivity of $H^n(v)$. The long exact cone sequence
now gives $H^i(\operatorname{Cone}(v))=0$ for every $i\ge n$. Quasi-coherence is part of the
comparison. No approximation of $H$ by an arrow pointing into $H$ is used. Dependencies: lem-
sfb-perfect-coefficient-arrow-finite-realization, lem-sfb-dg-coefficient-realization-comparison,
lem-sf-derived-homology-long-exact.

10. The comparison identifies the underlying $\nu_E(\delta)$ with
$Rp_{E*}\theta_{Y,E,G,\delta}$, for exactly the scalar-action adjoint specified in the
statement. The projection $p_E:Y_E\to Y$ is affine. Its derived direct image on quasi-coherent
complexes detects the cohomological bounds, so step 9 implies that the cone of
$\theta_{Y,E,G,\delta}$ is quasi-coherent and zero for every $i\ge n$ on $Y_E$ itself. Together
with the finite type algebra $E$, bounded-coherent $G$ and ordinary arrow $\delta$, this is
$\mathcal A_n(Y)$. All comparisons are derived. The argument does not impose a restriction of
$G$ on $U$ or $V$, and only used the existence of their two supplied local witnesses.
Dependencies: lem-sfb-dg-coefficient-realization-comparison, lem-sc-affine-derived-pushforward-
t-exact. -/
theorem globalWitness_oneDegree_binaryPatching
    {D A : CommRingCat.{u}} [IsNoetherianRing D] (c : D ⟶ A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec D) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U V : Y.Opens) (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set Y)) (hV : IsCompact (V : Set Y))
    (K : schemeDerivedCategory (pullback f (Spec.map c)))
    (hK : schemeDerivedQCohProperty (pullback f (Spec.map c)) K) (n : ℤ)
    (F : schemeDerivedCategory Y)
    (hbounded : ∃ lo hi : ℤ, ∀ i : ℤ, i < lo ∨ hi < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj F))
    (hcoherent : ∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj F))
    (gamma : F ⟶ (schemeDerivedDirectImage (pullback.fst f (Spec.map c))).obj K)
    (hglobal : ConeBound (theta c f (pullback.fst f (Spec.map c))
      (pullback.snd f (Spec.map c)) pullback.condition F K gamma) (n + 1))
    (hlocalU : HasApproximation (U.ι ≫ f) c
      ((derivedPullback (openMap f c U)).obj K) n)
    (hlocalV : HasApproximation (V.ι ≫ f) c
      ((derivedPullback (openMap f c V)).obj K) n) :
    HasApproximation f c K n := by
  sorry

end AlgebraicGeometry.CoefficientPatching
