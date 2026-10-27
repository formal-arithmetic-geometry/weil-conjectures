/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Category.Grp.Colimits
import Sheaf.AlgebraicGeometry.NoetherianAffineAtlasRelation
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import WeilConjectures.AlgebraicGeometry.CoherentHomsOverOpen
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Morphisms over an open algebraic space

Source: Stacks Project, Spaces Cohomology, Tag 07UM, lemma-homs-over-open
(blueprint: lem-sfb-space-homs-over-open).

The open immersion is characterized on every etale test by the unit-ideal condition.
The monic maps `p n` specify the actual ideal-power subobjects of `G`: their images
on every test are the existing locally generated ideal-power section families.
These characterizations determine the open and the powers up to unique isomorphism.
The equations for `r` and `c` specify the inclusion transitions and canonical restriction,
so the asserted bijection is the map induced by restriction, with its extension clause.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction identifies Hom over the unit locus of an ideal with the filtered colimit
of Hom from its power multiples of a coherent module. The three space hypotheses mean
locally Noetherian, quasi-compact and absolutely quasi-separated. Coherence is precisely
quasi-coherence and coherence after restriction to each etale scheme chart.
Source: Stacks, Spaces Cohomology, Tag 07UM, lemma-homs-over-open
(blueprint: lem-sfb-space-homs-over-open).

Proof:
1. Choose an affine surjective etale atlas W -> X by
   lem-sfb-qc-space-affine-etale-atlas. By lem-sfb-noetherian-affine-atlas-relation,
   W and R = W x_X W are Noetherian schemes and both projections are etale;
   R need not be affine.
2. Restrict to W and R. The scheme Zariski/etale equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies these modules
   with Zariski modules. The comparison is exact and tensor pullback by
   lem-sfb-scheme-etale-module-exact-finiteness-comparison, so it identifies the
   images of tensor multiplication defining the powers and their inclusions.
   The affine chart calculus lem-sfb-space-qcoh-affine-chart-calculus gives their
   quasi-coherence. Restriction on localized sites preserves the local products
   directly. Their inclusions become isomorphisms on the unit locus of I.
3. Set D_n = Hom(I^n G,F). Precomposition with inclusions gives the transition maps.
   Restriction to U gives compatible homomorphisms c_n, hence the canonical map
   from their colimit (def-weil-pbc-category-colimit).
4. For a map on U, lem-weil-pbc-coherent-homs-over-open on W gives an extension
   from I^a G. On R its two pullbacks agree over U_R. Injectivity of the same scheme
   theorem and lem-weil-pbc-filtered-colimit-modules-elementwise give b >= a at
   which the pullbacks agree as actual maps. Precompose the extension to power b.
5. The morphism clause of lem-sfb-space-qcoh-groupoid-equivalence descends that map
   uniquely to X. Its restriction equals the original map: on each etale test of U,
   pull back the atlas and use separatedness of the sheaf F to check equality.
   This proves surjectivity and the extension clause.
6. For injectivity, represent a class in the kernel by a map I^a G -> F using
   lem-weil-pbc-filtered-colimit-modules-elementwise. On W, injectivity of the
   scheme theorem makes it zero at some later power b. Faithfulness of the same
   groupoid equivalence makes the map I^b G -> F zero on X. Thus the class is zero.
   The canonical homomorphism is therefore bijective. -/
theorem coherent_homs_over_open
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (V W : Over S) (a : yoneda.obj V ⟶ X.obj.obj)
      (b : yoneda.obj W ⟶ X.obj.obj), IsAffine V.left → IsAffine W.left →
        CompactSpace (Point (Limits.pullback a b)))
    (F G I : X.Modules) (hF : F.IsQuasicoherent) (hGqc : G.IsQuasicoherent)
    (hGcoh : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj G))
    (i : I ⟶ SheafOfModules.unit X.structureSheaf) [Mono i] (hI : I.IsQuasicoherent) :
    ∃ (U : AlgebraicSpace S) (j : U ⟶ X) (hj : IsEtale j.hom.hom),
      IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) j.hom.hom ∧
      (∀ T : X.EtaleSite,
        (∃ a : yoneda.obj T.obj.left ⟶ U.obj.obj, a ≫ j.hom.hom = T.obj.hom) ↔
          Function.Surjective (i.val.app (op T))) ∧
      ∃ (P : ℕ → X.Modules) (p : ∀ n : ℕ, P n ⟶ G),
        (∀ n : ℕ, Mono (p n)) ∧
        (∀ (n : ℕ) (T : X.EtaleSite), Set.range ((p n).val.app (op T)) =
          idealPowerSubsheafSections i G (fun _ ↦ Set.univ) n T) ∧
        (∀ n : ℕ, IsIso ((pullback j hj).map (p n))) ∧
        ∃ r : ∀ (n m : ℕ), n ≤ m → (P m ⟶ P n),
          (∀ (n m : ℕ) (h : n ≤ m), r n m h ≫ p n = p m) ∧
          (∃ (D : ℕ ⥤ AddCommGrpCat.{u+1})
            (e : ∀ n : ℕ, D.obj n ≅ AddCommGrpCat.of (P n ⟶ F))
            (c : D ⟶ (Functor.const ℕ).obj
              (AddCommGrpCat.of ((pullback j hj).obj G ⟶ (pullback j hj).obj F))),
            (∀ (n m : ℕ) (h : n ≤ m) (χ : P n ⟶ F),
              (e m).hom (D.map (homOfLE h) ((e n).inv χ)) = r n m h ≫ χ) ∧
            (∀ (n : ℕ) (χ : P n ⟶ F),
              (pullback j hj).map (p n) ≫ c.app n ((e n).inv χ) =
                (pullback j hj).map χ) ∧
            Function.Bijective (colimit.desc D ⟨_, c⟩)) ∧
          ∀ ψ : (pullback j hj).obj G ⟶ (pullback j hj).obj F,
            ∃ (n : ℕ) (χ : P n ⟶ F),
              (pullback j hj).map (p n) ≫ ψ = (pullback j hj).map χ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
