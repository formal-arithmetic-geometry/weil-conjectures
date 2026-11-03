/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteGeometricInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteGeometricVerdierCore

/-!
# Finite-coefficient geometric Verdier comparison

Source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, opening locality/restriction step
(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Naturality of the canonical comparison follows from naturality of beta and pre. -/
private theorem geometric_comparison_natural
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.Monoidal] (W : C) (Wbar : D) (w : G.obj W ≅ Wbar)
    {K L : C} (f : L ⟶ K) :
    G.map ((MonoidalClosed.pre f).app W) ≫
        finiteFieldDualizingHomComparison G L W Wbar w =
      finiteFieldDualizingHomComparison G K W Wbar w ≫
        (MonoidalClosed.pre (G.map f)).app Wbar := by
  unfold finiteFieldDualizingHomComparison
  rw [← Category.assoc,
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app, Category.assoc]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) ((MonoidalClosed.pre (G.map f)).naturality w.hom).symm

/-- The evaluation equation uses the specified tensorator and the actual chosen w. -/
private theorem geometric_comparison_evaluation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.Monoidal] (K W : C) (Wbar : D) (w : G.obj W ≅ Wbar) :
    G.obj K ◁ finiteFieldDualizingHomComparison G K W Wbar w ≫
        (ihom.ev (G.obj K)).app Wbar =
      Functor.LaxMonoidal.μ G K _ ≫ G.map ((ihom.ev K).app W) ≫ w.hom := by
  unfold finiteFieldDualizingHomComparison
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, ihom.ev_naturality,
    ← Category.assoc, Functor.LaxMonoidal.ihomComparison_ev, Category.assoc]

/-- Finite-coefficient geometric pullback over an algebraic closure preserves the
constructible finite-Tor category, reflects isomorphisms, and carries the dualizing
object and its evaluation to the algebraically closed base change.

The compact-support comparison is the canonical mate composite for the chosen
compactification, and its invertibility and counit normalization are asserted.  The
internal-Hom comparison is the evaluation transpose followed by the map induced by
that dualizing-object isomorphism, and is natural contravariantly in its first argument.
No biduality or anti-equivalence assertion is included.

Proof source: latest blueprint,
`part-six-operations/sec-six-functors/sec-the-remaining-operations/`
`sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`,
opening locality/restriction paragraph and finite-coefficient tower argument.

Proof (the thirteen steps of the DAG node):
1. Identify finite-coefficient internal modules with ordinary constant-A modules,
then identify their bounded constructible finite-Tor categories with the etale ones.
The site and internal-module comparisons preserve pullbacks, support, tensor, Hom,
units, counits and evaluation, so they identify the specified canonical arrows.
2. Inverse image is exact. Pull back bounded flat constructible representatives;
constructibility and the Tor interval persist. The canonical derived tensorator is
invertible and satisfies the monoidal axioms. On homogeneous elements in degrees
 i,j both symmetry composites multiply by (-1)^(i*j), giving the Koszul symmetry.
3. Every field-extension projection is a surjective fpqc base change. Its etale
module inverse image is faithful and exact. Applied to the cohomology of a cone,
this detects isomorphisms; transfer this detection to the internal realization.
4. Compact-support base change is the open-extension comparison followed by the
proper direct-image mate. Coherent compactification comparison identifies its
base-changed compactification with any other chosen compactification.
5. Choose a separable closure inside kbar and its directed finite separable tower.
The finite-stage projections are finite etale, their limit is affine ind-etale.
Finite cohomological dimension at every stage and dimension zero at the separably
closed point provide the constructible exceptional adjoints and support stability.
6. At each finite etale stage, the sum functors are left adjoint to pullback and
agree with compact support. Support composition and these adjunctions identify
Hom(P,g_i^*W) with Hom(Ra_i!P,A_i), naturally in P. The representing objects
therefore give isomorphisms g_i^*W to W_i.
7. The etale-horizontal support mate identifies the sum counit in this bijection
with the inverse of the specified exchange. It gives the displayed counit
normalization. Exchange pasting makes these isomorphisms compatible up the tower.
8. Constructible finite-Tor object descent and Hom continuity pass these compatible
representing bijections to the separable closure. Apply continuity also on the
base point to the compact-support images, which remain constructible finite-Tor.
Descent of morphisms and equalities ensures independence and naturality.
9. The exceptional adjunction identifies the final Hom group with Hom(P,W_s).
Applying the natural representing bijection and its inverse to the identities
constructs the two inverse maps. At the original-stage presentation of W, its
identity corresponds to epsilon_a, proving the counit normalization at k_s.
10. The remaining purely inseparable extension induces universal homeomorphisms.
Topological invariance gives an etale topos equivalence. Descend locally closed
strata and their trivializing etale covers through this equivalence: it preserves
bounded constructibility both ways. Its monoidality matches all Tor tests, so it
also preserves finite Tor amplitude both ways.
11. Full faithfulness, essential surjectivity on the constructible finite-Tor
categories, compact-support exchange and the exceptional adjunction identify the
two representing Hom functors across the purely inseparable step. This yields
the normalized dualizing isomorphism there. Compose with step 9; exchange pasting
and naturality give exactly the asserted normalization over kbar.
12. Both alternatives for k make it perfect, so kbar/k is separable algebraic and
ind-etale. The geometric projection is weakly etale. The native weakly-etale
closed-comparison theorem applies directly to the actual internal-module derived
pullback and proves invertibility of its canonical evaluation-transpose beta.
13. Compose beta with Hom(1,w). Both factors are invertible. Naturality of the
closed adjunction gives contravariant naturality. Its transpose identity followed
by naturality of evaluation in the second argument is the displayed evaluation
equation. The fixed braiding converts the library's K tensor Hom convention into
Hom tensor K. Zero coefficients (including exponent zero), empty X and identity
algebraic closure are included, giving the unique zero or identity comparisons.

(blueprint: lem-sfb-finite-geometric-verdier-comparison).
-/
theorem finite_geometric_verdier_comparison_current
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a) :
    (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).IsTriangulated ∧
    Nonempty (FiniteFieldDualizingPullbackData
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
        DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X ⊓
        DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (cartesianFinitePointRing A)
        (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) ⊓
        DerivedCategory.finiteTorAmplitude _)
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (detSfDerivedPullback (cartesianFinitePointRing A)
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (leftDerivedUpperStarUnitIso (cartesianFinitePointRing A)
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (finiteFieldDerivedBraiding (CommMon.mk (cartesianFinitePointRing A)) X)
      (finiteFieldDerivedBraiding (CommMon.mk (cartesianFinitePointRing A))
        (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) )
      (detSfCompactSupport (cartesianFinitePointRing A) c)
      (detSfCompactSupport (cartesianFinitePointRing A)
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (detSfCompactSupportBaseChangeComposite (cartesianFinitePointRing A) a
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c
        (compactSupportOpenBaseChangeIso (cartesianFinitePointRing A) a
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c))) := by
  obtain ⟨core⟩ := finite_geometric_verdier_core_exists
    p ell hple k hk A hA kbar X a c
  refine ⟨inferInstance, ⟨{
    W := core.W
    Wbar := core.Wbar
    W_ctf := core.W_ctf
    Wbar_ctf := core.Wbar_ctf
    counit := core.counit
    counitBar := core.counitBar
    represents := core.represents
    representsBar := core.representsBar
    symmetry := core.symmetry
    preserves_ctf := core.preserves_ctf
    conservative := core.conservative
    exchange_iso := core.exchange_iso
    dualizingIso := core.dualizingIso
    counit_normalization := core.counit_normalization
    beta_iso := ?_
    comparison_iso := ?_
    comparison_natural := ?_
    evaluation := ?_ }⟩⟩
  · intro K
    exact finite_geometric_internalHom_comparison
      p ell hple k hk A hA kbar X a K ⟨core.W, core.W_ctf⟩
  · intro K
    have := finite_geometric_internalHom_comparison
      p ell hple k hk A hA kbar X a K ⟨core.W, core.W_ctf⟩
    unfold finiteFieldDualizingHomComparison
    infer_instance
  · intro K L f
    exact geometric_comparison_natural _ core.W core.Wbar core.dualizingIso f
  · intro K
    exact geometric_comparison_evaluation _ K.obj core.W core.Wbar core.dualizingIso

end AlgebraicGeometry.ProEtale.CondensedRing
