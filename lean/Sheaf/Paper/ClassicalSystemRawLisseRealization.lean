/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseCommonRestriction
public import Sheaf.Paper.ClassicalRawLisseCoherence
public import Sheaf.Paper.ClassicalRawLissePointFibres

import Sheaf.Paper.ClassicalRawLisseFiniteConstruction
import Sheaf.Paper.ClassicalRawLisseFiniteOperations
import Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback
import Sheaf.Paper.ClassicalRawLisseCommonDescent

/-! # Classical systems and raw lisse realization

Source: BS 6.8.4, 6.8.11, 6.8.14, Remark 6.8.15
(blueprint: lem-zl-classical-system-raw-lisse-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ClassicalRawLisse
attribute [local irreducible] rationalDerivedPullback sfRationalScalarExtension
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

private def modulesFullyFaithful
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : PerAdic.Base D.k) : (s.finite E W).modules.FullyFaithful := by
  let R := (s.raw E W).raw ⋙ (sfRationalHeartProperty l E W.scheme).ι ⋙
    (a.realization E (realizationBase D l hl W)).sheaf D l hl E
  have hR : Nonempty R.FullyFaithful :=
    (Functor.FullyFaithful.nonempty_iff_map_bijective R).2 (fun M N ↦
      ((a.realization E (realizationBase D l hl W)).fully_faithful _ _
        ((s.finite E W).lisse M) ((s.finite E W).lisse N)).comp
        (((sfRationalHeartProperty l E W.scheme).fullyFaithfulι.map_bijective _ _).comp
          ((s.raw E W).fullyFaithful.map_bijective M N)))
  exact hR.some.ofIso (s.finite E W).comparison

private def scalarCoherence
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b) (o : Operations D l hl a b s) :
    ScalarCoherence D l hl a b s o := by
  let ff (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : PerAdic.Base D.k) :=
    (s.raw A X).fullyFaithful.comp (sfRationalHeartProperty l A X.scheme).fullyFaithfulι
  let unit (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : PerAdic.Base D.k) :=
    (o.scalar A A X (AlgHom.id _ _)).comparison.symm ≪≫
      isoWhiskerLeft ((s.raw A X).raw ⋙ (sfRationalHeartProperty l A X.scheme).ι)
        (sfRationalScalarUnit l A X.scheme D.p hl)
  let assoc (A B C : Type u) [Field A] [Field B] [Field C]
      [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      [FiniteDimensional ℚ_[l] C] (X : PerAdic.Base D.k)
      (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) :=
    isoWhiskerLeft (o.scalar A B X i).raw (o.scalar B C X j).comparison.symm ≪≫
      isoWhiskerRight (o.scalar A B X i).comparison.symm
        (sfRationalScalarExtension l B X.scheme D.p hl C j) ≪≫
      isoWhiskerLeft ((s.raw A X).raw ⋙ (sfRationalHeartProperty l A X.scheme).ι)
        (sfRationalScalarComp l A B i X.scheme D.p hl C j) ≪≫
      (o.scalar A C X (j.comp i)).comparison
  exact {
    scalarId := fun A _ _ _ X ↦
      ((ff A X).whiskeringRight _).preimageIso (unit A X)
    scalarId_normalization := fun A _ _ _ X ↦
      heq_of_eq (((ff A X).whiskeringRight (Rational D l A X)).map_preimage
        (X := (o.scalar A A X (AlgHom.id _ _)).raw)
        (Y := 𝟭 (Rational D l A X)) (unit A X).hom)
    scalarComp := fun A B C _ _ _ _ _ _ _ _ _ X i j ↦
      ((ff C X).whiskeringRight _).preimageIso (assoc A B C X i j)
    scalarComp_normalization := fun A B C _ _ _ _ _ _ _ _ _ X i j ↦
      heq_of_eq (((ff C X).whiskeringRight (Rational D l A X)).map_preimage
        (X := (o.scalar A B X i).raw ⋙ (o.scalar B C X j).raw)
        (Y := (o.scalar A C X (j.comp i)).raw) (assoc A B C X i j).hom) }

private def restrictionCoherence
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b) (o : Operations D l hl a b s) :
    RestrictionCoherence D l hl a b s o := by
  let ff (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : PerAdic.Base D.k) := modulesFullyFaithful D l hl a b s A X
  let unit (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : PerAdic.Base D.k) :=
    (o.restriction A X X (𝟙 X.scheme)).ordinary.symm ≪≫
      isoWhiskerLeft (s.finite A X).modules
        (a.identity A (realizationBase D l hl X)).ordinary
  let assoc (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X Y Z : PerAdic.Base D.k) (f : Y.scheme ⟶ X.scheme)
      (g : Z.scheme ⟶ Y.scheme) [IsImmersion f] [IsImmersion g] :=
    isoWhiskerLeft (o.restriction A X Y f).raw (o.restriction A Y Z g).ordinary.symm ≪≫
      isoWhiskerRight (o.restriction A X Y f).ordinary.symm
        (LisseRealization.ordinaryPull l A g) ≪≫
      isoWhiskerLeft (s.finite A X).modules
        (a.composition A (X := realizationBase D l hl Y)
          (Y := realizationBase D l hl X) (Z := realizationBase D l hl Z) f g).ordinary.symm ≪≫
      (o.restriction A X Z (g ≫ f)).ordinary
  exact {
    restrictionId := fun A _ _ _ X ↦
      ((ff A X).whiskeringRight _).preimageIso (unit A X)
    restrictionId_normalization := fun A _ _ _ X ↦
      heq_of_eq (((ff A X).whiskeringRight (Rational D l A X)).map_preimage
        (X := (o.restriction A X X (𝟙 X.scheme)).raw)
        (Y := 𝟭 (Rational D l A X)) (unit A X).hom)
    restrictionComp := fun A _ _ _ X Y Z f g _ _ ↦
      ((ff A Z).whiskeringRight _).preimageIso (assoc A X Y Z f g)
    restrictionComp_normalization := fun A _ _ _ X Y Z f g _ _ ↦
      heq_of_eq (((ff A Z).whiskeringRight (Rational D l A X)).map_preimage
        (X := (o.restriction A X Y f).raw ⋙ (o.restriction A Y Z g).raw)
        (Y := (o.restriction A X Z (g ≫ f)).raw) (assoc A X Y Z f g).hom) }

private def mixedComparison
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b) (o : Operations D l hl a b s)
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
    (W V : PerAdic.Base D.k) (i : E →ₐ[ℚ_[l]] F)
    (f : V.scheme ⟶ W.scheme) [IsImmersion f] : Mixed D l hl E W F a b s o i V f := by
  let e :=
    isoWhiskerLeft (o.scalar E F W i).raw (o.restriction F W V f).ordinary.symm ≪≫
      isoWhiskerRight (o.scalar E F W i).ordinary.symm
        (LisseRealization.ordinaryPull l F f) ≪≫
      isoWhiskerLeft (s.finite E W).modules
        (a.mixed E F i (X := realizationBase D l hl V)
          (Y := realizationBase D l hl W) f).ordinary ≪≫
      isoWhiskerRight (o.restriction E W V f).ordinary
        (pbcExtend (a.fieldChange E F i (realizationBase D l hl V)).coefficient) ≪≫
      isoWhiskerLeft (o.restriction E W V f).raw (o.scalar E F V i).ordinary
  let ff := (modulesFullyFaithful D l hl a b s F V).whiskeringRight (Rational D l E W)
  exact {
    comparison := ff.preimageIso e
    normalization := heq_of_eq (ff.map_preimage
      (X := (o.scalar E F W i).raw ⋙ (o.restriction F W V f).raw)
      (Y := (o.restriction E W V f).raw ⋙ (o.scalar E F V i).raw) e.hom) }

/-- Normalized finite classical systems realize fully faithfully in the raw sf heart,
with the same ordinary-module realization on the sf and PBC sides.
Source: Bhatt--Scholze, Propositions 6.8.4(1),(3),(4), 6.8.11(3), 6.8.14(2),
Remark 6.8.15 (blueprint: lem-zl-classical-system-raw-lisse-realization).

1. The hypotheses needed by the coefficient comparisons hold on $W$: the field $k$ is Noetherian
   (its only ideals are zero and the unit ideal), so [lem-weil-pbc-finite-type-over-noetherian]
   makes the finite-type scheme $W$ Noetherian. Its dimension is finite by [lem-kun-dimension-
   finite-type]. The image of $\ell$ is a nonzero constant in $k$, so its inverse in $k$ maps
   to an inverse in every local ring of $W$. Separatedness is assumed. The same checks apply to
   every locally closed finite-type subscheme and to $s=\operatorname{Spec}k$.

2. Apply [lem-per-lisse-completed-system-comparison] to $W,E$. It identifies each actual quotient
   $L/\varpi^nL$ with the pro-etale image of a finite locally free etale sheaf $L_n$,
   identifies the transition with the quotient map, and identifies the inverse functor with
   $\varprojlim_n\nu_W^*L_n$. Thus the stated transition and reconstruction isomorphisms are
   the unit and counit of that equivalence, with their prescribed projections. Conversely every
   normalized finite locally free system has a lisse inverse limit. By [def-pod-lisse-l-adic-
   sheaves] its integral maps are precisely compatible families, so they correspond to the
   actual maps of inverse limits. This uses ordinary lattice quotients, not derived reductions
   of an arbitrary integral object.

3. On a lisse trivializing cover, $L[0]$ is $B_W\otimes_A A^r[0]$, with finite $r$ and the one-
   stratum stratification $W$. Condition (ii) of [lem-weil-pbc-integral-stratified-perfect-
   characterization] therefore holds: $A^r[0]$ is itself a bounded finite free complex.
   Condition (i) gives membership in the completed integral constructible category, including
   the compatible etale-origin witnesses. The last paragraph of that node identifies this with
   the sf integral category as well. Since $L[0]$ has no nonzero cohomology outside degree
   zero, its rationalization belongs to both standard classes by [def-weil-constructible-
   standard-tstructure], hence lies in the sf heart [def-weil-constructible-heart], and is
   lisse in the sense of [def-real-rational-lisse-heart], since the same cover trivializes its
   rationalization.

4. For a free-modelled system $M=(M_n)_n$, set $\widehat M=\varprojlim_n\nu_W^*M_n$ and
   $C_E(M\otimes E)=Q^{\mathrm{sf}}(\widehat M[0])$. Step 2 gives the inverse-limit functor on
   compatible families; step 3 gives its required integral membership. Extend a family $f$ to a
   rational map by $f\otimes a\mapsto aQ^{\mathrm{sf}}(\widehat f)$. Identities and composition
   hold because inverse limit is a functor and scalar multiplication is central; for example
   $(g\otimes b)(f\otimes a)$ maps to $abQ^{\mathrm{sf}}(\widehat g\widehat f)$. The localized
   map is well defined by the $A$-balanced tensor relation in the classical Hom definition
   [def-pod-lisse-l-adic-sheaves]. By [lem-tw-lisse-rational-realization], $\mathcal
   L_{W,E}C_E$ is $\widehat M[1/\varpi]$ and sends $f\otimes a$ to $a(1\otimes\widehat f)$. By
   [lem-fd-rational-coefficient-category-comparison], $J$ is literally the identity on the
   integral object and localized Hom; [lem-per-continuous-rational-derived-realization]
   therefore identifies $\mathcal RJC_E$ with that same module and that same map. These are
   natural comparisons on all compatible families and their scalar multiples.

5. By [lem-per-lisse-completed-system-comparison], the composite $\mathcal RJC_E$ of step 4
   induces a bijection on Hom groups, because it is exactly the fully faithful localization of
   the integral reduction equivalence. Both $J$ and $\mathcal R$ are equivalences by [lem-fd-
   rational-coefficient-category-comparison] and [lem-per-continuous-rational-derived-
   realization]. Their maps on Hom are bijective, so $C_E$ is fully faithful. For a specified
   module isomorphism between $\mathcal RJN$ and $\widehat M[1/\varpi]$, compose with the
   comparison of step 4 and orient it from $\mathcal RJC_E(M)$ to $\mathcal RJN$. Lift this map
   and its inverse by fullness of $\mathcal RJ$. Faithfulness shows that their two composites
   are identities. The lifts are maps of the sf heart, which is a full subcategory [def-weil-
   constructible-heart], and so give the requested raw heart isomorphism with exactly the
   specified module comparison.

6. For $E\subset F$ with ramification index $e$, the classical extension has level $m$ equal to
   $M_n\otimes_{A/\varpi_E^n}(\mathcal O_F/\varpi_F^m)$ with $n=\lceil m/e\rceil$ [def-pod-
   lisse-l-adic-sheaves]. Locally a basis of $M_n$ goes to a basis of that tensor product, so
   the new system is again finite locally free and hence free-modelled. The inverse-limit and
   quotient comparisons for this operation and for restriction are precisely those of [lem-per-
   lisse-completed-system-comparison]. For the raw realizations, use [lem-tw-lisse-rational-
   realization] and [lem-per-continuous-rational-derived-realization]: both identify the
   operations with ordinary module inverse image and balanced coefficient extension. The scalar
   comparison for $J$ is fixed by [lem-fd-rational-coefficient-category-comparison].
   Consequently the comparisons on $C_E$ are induced by those actual quotient and tensor maps.
   On each local basis vector the two composites for an identity or composite pullback give the
   same pulled-back vector; on a pure tensor $c\otimes(b\otimes v)$ the scalar associator gives
   $cb\otimes v$. The cited comparisons are natural in maps and already satisfy these
   equations, so they give the asserted restriction, identity, composition and scalar coherence
   on $C_E$. This applies in particular to locally closed restrictions.

7. Send $(E,M)$ to $(E,C_E(M))$. The scalar comparisons in step 6 identify the transition maps of
   the classical Hom system [def-pod-lisse-l-adic-sheaves] with those of the sf Hom system
   [def-weil-algebraically-closed-coefficients]. Thus a common-stage class $[F,u]$ maps to
   $[F,C_F(u)]$, with the endpoint scalar comparisons inserted. This is well defined: if
   representatives agree after extension to $F'$, naturality from step 6 makes their images
   agree there. Every target class lifts over its representing field by the finite-stage Hom
   bijection of step 5. If two lifted classes have equal images, their images agree over a
   larger common field; injectivity of the Hom bijection at that field gives equality of the
   lifted classes. This proves full faithfulness on the directed colimits. Identity and
   composition are checked at one common stage, where $C_F$ is a functor. Restriction and
   scalar coherence descend by the same representatives.

8. For $x:s=\operatorname{Spec}k\to W$, [lem-per-adic-heart-pullback-fibres] identifies the PBC
   adic fibre on this lisse system with $(\varprojlim_n(M_n)_{\bar x})\otimes_AE$, naturally in
   maps and finite coefficient extension. On the sf side [lem-tw-lisse-rational-realization]
   identifies the completed point fibre with sections at $s$ of the ordinary module pullback of
   $\widehat M[1/\varpi]$. These are the same module pullback as for the PBC realization by
   [lem-per-continuous-rational-derived-realization]. To see its lattice model explicitly,
   [lem-per-lisse-completed-system-comparison] identifies integral pullback with the inverse
   limit of the pulled-back finite levels. Evaluation of this limit at the final object $s$ is
   the limit of their evaluations (a section of a limit is a compatible family of sections);
   each finite-level evaluation is $(M_n)_{\bar x}$. Localizing then gives exactly the
   displayed $E$-space. Scalar extension to $\Omega$ is the fibre convention in [def-pod-lisse-
   l-adic-sheaves]. Thus the classical, sf and PBC fibre comparisons all use the same quotient
   projections and scalar maps.

9. For an automorphism $h:s\to s$, the point clause of [lem-tw-lisse-rational-realization] says
   explicitly that its point-fibre identification carries restriction followed by the inverse-
   image coprojection to that same map in the ordinary module model, and that it respects
   iterates. Step 8 identifies the classical and PBC fibres with this model by their actual
   inverse-limit projections. The naturality and pullback-composition equations of [lem-per-
   lisse-completed-system-comparison] identify the corresponding maps on each finite quotient,
   hence on their inverse limit and its localization. Therefore the fibre comparison
   intertwines transport for $h$, and composition gives the assertion for every finite iterate.
   If $i:S\hookrightarrow W$ is locally closed and $i^*N$ is identified with $C_E(M)$, apply
   [lem-per-adic-heart-pullback-fibres] to $i$ to identify the fibre of $N$ at a point of $S$
   with that of $i^*N$; apply the normalized pullback comparison of [lem-per-continuous-
   rational-derived-realization] and step 8 to the specified identification. This gives the
   same assertion for $N$, with naturality in its identified restriction. Every construction
   permits zero local rank and the empty scheme; no geometric point or positive rank was
   selected in constructing the functors.
-/
theorem classical_system_raw_lisse_realization :
    ∃ (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
      (s : Family D l hl a b) (o : Operations D l hl a b s)
      (h : Coherence D l hl a b s o)
      (c : ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (W : PerAdic.Base D.k), Common D l hl W Ω a b s o h.toScalarCoherence),
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f],
          Nonempty (CommonRestriction D l hl W Ω a b s o h.toScalarCoherence V f (c Ω W) (c Ω V))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (W : PerAdic.Base D.k), Nonempty (PointComparison D l hl E W a b s)) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f],
          Nonempty (RestrictedFibres D l hl E W a b s V f)) ∧
      (∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
        [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
        (W V : PerAdic.Base D.k) (i : E →ₐ[ℚ_[l]] F)
        (f : V.scheme ⟶ W.scheme) [IsImmersion f],
          Nonempty (Mixed D l hl E W F a b s o i V f)) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
        Nonempty (LisseRealization.PointNormalized D l hl E
          (a.realization E (LisseRealization.point D l hl)) (a.point E))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
        Nonempty (LisseRealization.PullNormalized D l hl E f
          (a.realization E X) (a.realization E Y) (a.along E f))) ∧
      (∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
        [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
        (i : E →ₐ[ℚ_[l]] F) (X : LisseRealization.Base D l hl),
        Nonempty (LisseRealization.FieldNormalized D l hl E F i X
          (a.realization E X) (a.realization F X) (a.fieldChange E F i X))) := by
  classical
  obtain ⟨a, _, hr, hf, hp, _⟩ := LisseRealization.lisse_rational_realization D l hl
  obtain ⟨b⟩ := ContinuousRational.continuous_rational_derived_realization.{u} l
  obtain ⟨s, hs⟩ := classical_raw_lisse_finite_construction D l hl a b hp hr
  obtain ⟨o⟩ := classical_raw_lisse_finite_operations D l hl a b s hr hf
  let h : Coherence D l hl a b s o := {
    toScalarCoherence := scalarCoherence D l hl a b s o
    toRestrictionCoherence := restrictionCoherence D l hl a b s o }
  have hm (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
      (W V : PerAdic.Base D.k) (i : E →ₐ[ℚ_[l]] F)
      (f : V.scheme ⟶ W.scheme) [IsImmersion f] :
      Nonempty (Mixed D l hl E W F a b s o i V f) :=
    ⟨mixedComparison D l hl a b s o E F W V i f⟩
  obtain ⟨c, hc⟩ := classical_raw_lisse_common_descent D l hl a b s o h hm
  refine ⟨a, b, s, o, h, c, hc, hs, ?_, hm, hp, hr, hf⟩
  intro E _ _ _ W V f _
  let completed (x : Spec (.of D.k) ⟶ V.scheme) :=
    (classical_raw_lisse_intrinsic_fibre_pullback D l hl E W V f x).some
  refine ⟨{
    completed := completed
    identified := fun x N M e ↦ (completed x).symm.app N.obj ≪≫
      (sfAdicRationalFiber l E V.scheme x).mapIso e ≪≫ (s.finite E V).fibre x M
    normalization := fun _ _ _ _ ↦ rfl }⟩

end WeilConjectures.ClassicalRawLisse
