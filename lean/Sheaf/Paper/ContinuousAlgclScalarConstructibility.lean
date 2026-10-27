/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.CategoryTheory.InternalModuleInverseImageComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.CategoryTheory.SiteCoveringsCommonRefinement
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.ModuleObjects.KernelStructure
import Sheaf.CategoryTheory.ModuleObjectCokernelAction
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.Paper.CoefficientHeartCommonStratification
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Continuous algebraic-closure scalar extension and constructibility

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
Remark 3.2, Definitions 3.3 and 3.5, and Theorem 4.13; the node's explicit
finite-free cohomology cycle-lifting argument
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility).

The coefficient sheaves contain all continuous functions for the norm topology.
Scalar modules are ordinary modules encoded internally in abelian groups, using
`scalarRingObj` from the recorded finite-constant-local-model interface. For a
field, `Mod.IsFree` is exactly finite dimensionality: its definition requires a
finite rank, including rank zero. Constant scalar complexes are formed termwise
before the ordinary unbounded derived extension of scalars. No completion of the
algebraic closure and no ambient-module flatness hypothesis occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ContinuousAlgclScalar

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (Ω : Type u) [NormedField Ω] [Algebra (Padic ℓ) Ω]
variable (E : IntermediateField (Padic ℓ) Ω)

/-- Postcomposition with the actual intermediate-field inclusion on continuous-map
condensed rings, using the recorded universe-polymorphic map. Source: HRS,
Example 3.1 and Remark 3.2
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
abbrev inclusion : Mon.mk (Profinite.continuousCoefficientRingObj E) ⟶
    Mon.mk (Profinite.continuousCoefficientRingObj Ω) :=
  @Mon.Hom.mk _ _ _ _ _
    (Profinite.continuousMapRingObjMapOfUniverse.{u, u} E.val.toRingHom continuous_subtype_val)
    (Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        E.val.toRingHom continuous_subtype_val))

/-- The same coefficient map after the monoidal inverse image from the point.
Source: HRS, Section 3, coefficient-change paragraph
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
abbrev coefficientInclusion (X : Scheme.{u}) :
    condensedRingObj (Profinite.continuousCoefficientRingObj E) X ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj Ω) X :=
  ((upperStarFromPoint X).mapMon.map (inclusion ℓ Ω E)).hom

/-- Ring-map compatibility inherited from the monoidal inverse image, with the
canonical structures on both pulled-back rings. Source: HRS, Section 3
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
instance coefficientInclusion_isMonHom (X : Scheme.{u}) :
    IsMonHom (coefficientInclusion ℓ Ω E X) :=
  ((upperStarFromPoint X).mapMon.map (inclusion ℓ Ω E)).isMonHom_hom

/-- The map on one-point scalar rings, hence precisely E → Ω under evaluation
of continuous functions on the point. Source: HRS, Remark 3.2
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
abbrev scalarInclusion : scalarRingObj (Profinite.continuousCoefficientRingObj E) ⟶
    scalarRingObj (Profinite.continuousCoefficientRingObj Ω) :=
  (scalarSections.mapMon.map (inclusion ℓ Ω E)).hom

/-- Evaluation of the specified condensed-ring map is a ring map, using the
recorded lax monoidal sections functor. Source: HRS, Remark 3.2
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
instance scalarInclusion_isMonHom : IsMonHom (scalarInclusion ℓ Ω E) :=
  (scalarSections.mapMon.map (inclusion ℓ Ω E)).isMonHom_hom

/-- The actual total left derived scalar extension, on ordinary unbounded
internal-module derived categories. Source: HRS, Section 3
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
abbrev scalarExtension (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientInclusion ℓ Ω E X)).leftDerivedFunctor

variable (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj A] [IsCommMonObj A]

/-- Constant scalar sheaves followed by inverse image preserve colimits, by the
composite of their existing adjunctions. This exposes the canonical structural
instance needed for termwise constant complexes. Source: HRS, Remark 3.2
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
instance constantPreservesColimits (W : Scheme.{u}) :
    PreservesColimitsOfSize.{0, 0} (scalarConstant W) :=
  ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).comp
      (pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ W)))).leftAdjoint_preservesColimits

/-- The constant scalar module functor is additive, using its existing finite
colimit preservation and the library's right-exact-implies-additive construction.
Source: HRS, Remark 3.2
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
instance constantModulesAdditive (W : Scheme.{u}) :
    ((scalarConstant W).mapMod (scalarRingObj A)).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ ((rightExactFunctor_iff _).mpr inferInstance)

/-- The displayed derived model A_W tensor over the discrete constant scalar
ring with the termwise constant complex P. The scalar action is the canonical
constant-section counit, not an arbitrary ring map. Source: HRS, Remark 3.2
and Definition 3.5
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility). -/
abbrev scalarModel (W : Scheme.{u})
    (P : CochainComplex (Mod Ab.{u + 1} (scalarRingObj A)) ℤ) :=
  (Mod.extendScalars (scalarCoefficientHom A W)).leftDerivedFunctor.obj
    (DerivedCategory.Q.obj
      ((((scalarConstant W).mapMod (scalarRingObj A)).mapHomologicalComplex (.up ℤ)).obj P))

/-- Continuous algebraic-closure scalar extension preserves bounded constructibility,
the specified cohomological interval, and simultaneous finite constant local models.
Source: HRS, Section 3, Remark 3.2, Definitions 3.3 and 3.5, and Theorem 4.13.
(blueprint: lem-sfb-continuous-algcl-scalar-constructibility).

Proof plan from the reviewed DAG node:
1. Work with section-ring module sheaves using [lem-pe-internal-section-tensor-comparison] and
[lem-sfb-internal-section-scalar-adjunction]. These statements give exact equivalences preserving
the underlying sheaves, finite sums, relative tensors, K-flat complexes and derived scalar
extension. Thus the cohomology and local quasi-isomorphism calculations below give precisely the
specified internal-module derived objects, rather than a different coefficient category. For
inverse image use [lem-sfb-internal-module-inverse-image-comparison] and
[lem-sfb-finite-upper-star-exact]. The coefficients are pulled back from the point, so
inverse-image composition identifies the pulled-back ring with the coefficient ring on the source,
naturally also for the map $A_E\to B$. Consequently geometric restriction here is exact on module
sheaves and commutes with cohomology. For a morphism $h$ the derived module pullback of
[sk-def-sfb-module-derived-pushpull] is
$L(\operatorname{Ext}_{\alpha_h}\circ\operatorname{mapMod}(h^*))$; here $\alpha_h$ is a ring
isomorphism [sk-def-sfb-coefficient-morphisms], so $\operatorname{Ext}_{\alpha_h}$ is an
equivalence, the composite is exact, and by the exact-functor clause of
[sk-def-sfb-derived-categories] the derived pullback is the termwise restriction. This applies to
strata and to arbitrary members of their pro-etale covers; those members need not be finite type.

2. For each of the finitely many $q\in[r,s]$, choose an adapted finite constructible locally
closed stratification for $H^q(M)$ using [sk-def-sfb-constructible]. Refine these simultaneously
using [lemma-constructible-common-refinement] repeatedly. Since a refinement is only a containment
of sets, use concretely the scheme fibre products $Z\times_TZ'$ of strata: the projection to $Z$
is an immersion by [lem-weil-pbc-immersion-base-change-lft] (1), its composite with $Z\to T$ is an
immersion by [lem-weil-pbc-proper-fp-permanence] (e), and its image is the intersection of the two
images. The finitely many intersections are disjoint, locally closed and cover $T$; they are
constructible since $T$ is Noetherian [lem-weil-pbc-finite-type-over-noetherian], as in
[sk-def-sfb-constructible]. Each refined stratum maps to the strata it came from, so restriction
to it factors through restriction to those strata, and base change of a pro-etale cover along it
is a pro-etale cover [def-weil-proetale-inverse-image]. The local model of a restricted cohomology
module pulls back to the same scalar model, since inverse image preserves the balanced tensor
presentation, or directly its finite constant-matrix presentation in
[det-def-sfb-constructible-local-model]. For each resulting stratum $T_a$, take a common
refinement of its finitely many trivializing pro-etale covers using
[lem-weil-pbc-site-coverings-common-refinement]. Each finitely presented scalar $E$-module is a
finite-dimensional vector space: a presentation makes it finitely generated, and a maximal
independent subset of finitely many generators is a basis. Thus on each cover member $V$ all
$H^q(M)|_V$ are finite free $A_{E,V}$-modules, say of ranks $n_q$.

3. Choose a complex $K$ representing $M|_V$ and put $Z^q=\ker(d_K^q)$ and
$H^q=Z^q/\operatorname{im}(d_K^{q-1})$. The underlying sheaf map $Z^q\to H^q$ is epic. In internal
notation this follows from the kernel and cokernel constructions [lem-sfb-modobj-kernels,
lem-sfb-modobj-cokernels]; the colimit hypothesis on tensor in the latter holds by
[sk-def-sfb-sheaf-tensor]. Apply [lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective] to each
of the finitely many sections of $H^q(V)$ given by the chosen bases, in the finitely many degrees
$[r,s]$. Refine their lifting covers simultaneously by
[lem-weil-pbc-site-coverings-common-refinement]. On every resulting member $W$ there are cycles
$z_{qj}\in Z^q(W)$ mapping to all those basis sections. Since $W$ is an object of the pro-etale
site of $T_a$, inverse image to $W_{\mathrm{pro\acute et}}$ is slice restriction on underlying
abelian sheaves [lem-sfb-proetale-object-inverse-image-restriction] (the pullback of
[def-sfb-finite-upper-star] is the same left Kan extension followed by sheafification), so
$z_{qj}$ are global cycles of $K|_W$ and $H^q(K|_W)=H^q(K)|_W$ has the restricted basis. This is
the basis-lifting proof of Stacks Tag 08FN (sites-cohomology.tex, lemma-local-lift-map), written
out here rather than assuming projectivity of a free sheaf as a global object.

4. On this $W$ let $P^q=E^{n_q}$ for $r\le q\le s$, put $P^q=0$ otherwise, and give $P$ zero
differential. Extend the assignment $e_j\mapsto z_{qj}$ $A_{E,W}$-linearly. Because each $z_{qj}$
is a cycle, these maps form a chain map $F\to K|_W$, where $F^q=A_{E,W}^{n_q}$ and $d_F=0$. On
$H^q$ its map is the chosen basis isomorphism for $q\in[r,s]$; outside this interval both sides
have zero cohomology by exact restriction and the hypothesis on $M$. Hence this chain map is a
quasi-isomorphism. This constructs the local derived model, including its degree interval, rather
than deducing a complex-level trivialization merely from trivial cohomology.

5. The complex $F$ is K-flat directly: for any acyclic complex $N$, the total tensor $N\otimes F$
is a finite direct sum, over $r\le q\le s$, of shifts of $N^{\oplus n_q}$, since $F$ has zero
differential. Each is acyclic and finite sums preserve the kernels and images computing
cohomology. This also proves the two-sided K-flat test by symmetry. The same argument applies to
$\underline P$ over $\underline E$, and to $\underline{\Omega\otimes_E P}$ over
$\underline\Omega$. Therefore [sk-def-sfb-derived-extension-of-scalars] computes
$A_{E,W}\otimes^L_{\underline E}\underline P$ by $F$, and computes $B_W\otimes^L_{A_{E,W}}F$ by
the zero-differential complex $(B_W^{n_q})_q$. Ordinary scalar extension of a free module is free
of the same rank: the balanced maps $b\otimes(a_j)_j\mapsto(ba_j)_j$ and $(b_j)_j\mapsto\sum_j
b_j\otimes e_j$ are inverse. Thus no tensor-exactness assertion about arbitrary $A_{E,W}$-modules
enters this computation.

6. Let $h:W\to T$ be the composite of the stratum inclusion and the refined cover map. Apply
[lem-sfb-internal-scalar-pullback-normalization] to the actual continuous coefficient map $A_E\to
B$. Its isomorphism $Lh_B^*D_{a,T}\cong D_{a,W}Lh_{A_E}^*$ has no flatness or boundedness
hypothesis. By the exact restriction established in step 1 these derived pullbacks are ordinary
restrictions. Together with steps 4--5 it gives $$(B_T\otimes^L_{A_{E,T}}M)|_W\cong
B_W\otimes^L_{A_{E,W}}F\cong(B_W^{n_q})_q.$$ The latter is also
$B_W\otimes^L_{\underline\Omega}\underline{(\Omega\otimes_E P)}$, by the K-flat computation of
step 5 and the basis $1\otimes e_j$ of $\Omega\otimes_E E^{n_q}$. The coordinate isomorphism sends
$b\otimes(\omega\otimes v)$ to $b\omega\otimes v$; its inverse sends $b\otimes v$ to
$b\otimes(1\otimes v)$. These formulas respect both scalar balancing relations. This proves both
requested derived isomorphisms for the same $P=P_{ai}$.

7. Write $L=B_T\otimes^L_{A_{E,T}}M$. Exact restriction and step 6 identify $H^q(L)|_W$ with
$B_W^{n_q}$ for $q\in[r,s]$ and with zero otherwise. Vanishing of a sheaf on a cover implies
vanishing: by [lem-sfb-proetale-object-inverse-image-restriction] its restriction to each member
$W$ is the slice restriction, so every section restricts to zero on that cover and the
separatedness clause of the sheaf condition makes the section zero. Thus on each stratum $H^q(L)$
has finite constant local models for every $q$, and vanishes outside $[r,s]$. For such an outside
degree, apply [new-det-lem-coefficient-heart-common-stratification-exactness] to $0\to H^q(L)$: on
every stratum it is epic, so it is epic globally and $H^q(L)=0$. Its hypothesis holds because $T$
is a finite-type scheme over a field, hence Noetherian by
[lem-weil-pbc-finite-type-over-noetherian] applied to $T\to\operatorname{Spec}k$ (the only ideals
of a field are zero and the whole field), and the stratification is finite locally closed. Finally
[sk-def-sfb-constructible] makes each $H^q(L)$ constructible and $L$ bounded constructible. Empty
strata can be omitted; if $T$ is empty the same detection statement applies to the empty family.
If $M=0$ all $n_q$ and all local complexes are zero; when $r=s$ the construction has a single
term. No completion of $\Omega$ or restriction on the images of continuous functions has been
used.
-/
theorem scalar_constructibility
    (hNorm : ∀ x : Padic ℓ, ‖algebraMap (Padic ℓ) Ω x‖ = ‖x‖)
    [IsAlgClosure (Padic ℓ) Ω] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)))
    (hM : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) T M)
    (r s : ℤ) (hrs : r ≤ s)
    (hAmplitude : ∀ q : ℤ, (q < r ∨ s < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj M)) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj Ω) T
        ((scalarExtension ℓ Ω E T).obj M) ∧
      (∀ q : ℤ, (q < r ∨ s < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((scalarExtension ℓ Ω E T).obj M))) ∧
      ∃ S : Scheme.FiniteLocallyClosedStratification T,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        (∃ D : ℤ → Scheme.FiniteLocallyClosedStratification T,
          (∀ (q : ℤ) (b : Fin (D q).n), Topology.IsConstructible ((D q).stratum b)) ∧
          (∀ (q : ℤ) (b : Fin (D q).n),
            HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj E)
              ((D q).domain b)
              ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
                ((D q).immersion b)).obj ((DerivedCategory.homologyFunctor _ q).obj M))) ∧
          ∀ (q : ℤ) (a : Fin S.n), ∃ b : Fin (D q).n,
            S.stratum a ⊆ (D q).stratum b) ∧
        ∀ a : Fin S.n,
          ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a),
            ∀ i : C.I₀,
              ∃ P : CochainComplex
                  (Mod Ab.{u + 1} (scalarRingObj (Profinite.continuousCoefficientRingObj E))) ℤ,
                (∀ q : ℤ, Mod.IsFree (scalarRingObj (Profinite.continuousCoefficientRingObj E))
                  (P.X q)) ∧
                (∀ q : ℤ, (q < r ∨ s < q) → IsZero (P.X q)) ∧
                Nonempty
                  ((CondensedRing.moduleObjectDerivedPullback
                    (Profinite.continuousCoefficientRingObj E)
                    (C.f i ≫ S.immersion a)).obj M ≅
                      scalarModel (Profinite.continuousCoefficientRingObj E) (C.X i) P) ∧
                Nonempty
                  ((CondensedRing.moduleObjectDerivedPullback
                    (Profinite.continuousCoefficientRingObj Ω)
                    (C.f i ≫ S.immersion a)).obj ((scalarExtension ℓ Ω E T).obj M) ≅
                      scalarModel (Profinite.continuousCoefficientRingObj Ω) (C.X i)
                        (((Mod.extendScalars (scalarInclusion ℓ Ω E)).mapHomologicalComplex
                          (.up ℤ)).obj P)) := by
  sorry

end AlgebraicGeometry.ProEtale.ContinuousAlgclScalar
