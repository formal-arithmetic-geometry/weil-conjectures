/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.CurveModuliGroupoids
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.NodalCurveStackSmooth

/-! # Stable genus and smooth-family open loci

Source: Stacks Project, moduli-curves.tex, Tags 0E76, 0E78 and 0DZZ;
curves.tex, Tag 0E8X (blueprint: lem-sfb-stable-and-smooth-family-open-loci).

The ambient category retains algebraic spaces. A comparison with a stable scheme
family preserves the structural map, and does not choose a projective embedding.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A presheaf family is an unpointed stable genus-`g` family when it is represented,
over its specified base, by an object of the recorded stable moduli category with
zero markings. Both the source isomorphism and its base isomorphism are retained.
This is a proposition, so an embedding is not part of the moduli object.
Source: Stacks, moduli-curves.tex, Tags 0E76 and 0E78, and the stable pointed convention
(blueprint: lem-sfb-stable-and-smooth-family-open-loci). -/
def IsStableGenusSpaceFamily {S : Scheme.{u}} (g : ℕ) (T : Over S)
    (F : (Over S)ᵒᵖ ⥤ Type u) (f : F ⟶ yoneda.obj T) : Prop :=
  ∃ Y : StablePointedModuli S g 0, ∃ b : Y.base ≅ T,
    ∃ e : F ≅ yoneda.obj (Over.mk (Y.projection ≫ Y.base.hom)),
      e.hom ≫ yoneda.map (Over.homMk Y.projection rfl) ≫ yoneda.map b.hom = f

/-- A specified presheaf family is a scheme over its base with a closed embedding
into a quotient projective bundle of a finite locally free module. The representing
isomorphism respects the family projection.
Source: Stacks, curves.tex, Tag 0E8X and the relative evaluation construction
(blueprint: lem-sfb-stable-and-smooth-family-open-loci). -/
def HasFiniteLocallyFreeProjectiveRealization {S : Scheme.{u}} (T : Over S)
    (F : (Over S)ᵒᵖ ⥤ Type u) (f : F ⟶ yoneda.obj T) : Prop :=
  ∃ (Y : Over S) (p : Y ⟶ T) (e : yoneda.obj Y ≅ F),
    e.hom ≫ f = yoneda.map p ∧
    ∃ (E : T.left.Modules) (hE : E.IsQuasicoherent), E.IsFiniteLocallyFree ∧
      ∃ i : Y.left ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData T.left E hE).relProj,
        IsClosedImmersion i ∧
        i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData T.left E hE).relProjHom = p.left

/-- Stable genus-`g` and smooth whole-family conditions are represented by opens in
the base of every proper flat finitely presented algebraic-space curve family.
The chosen opens commute with every cartesian arrow, and their universal properties
test every scheme base change. Over the stable open the source is a scheme with a
closed embedding into the projective bundle of a finite locally free module.
The stable full subcategory is an open substack contained in the nodal substack.

Source: Stacks, moduli-curves.tex, Tags 0E76, 0E78, 0DZZ and 0E86;
curves.tex, Tag 0E8X (blueprint: lem-sfb-stable-and-smooth-family-open-loci).

Proof plan:
1. By lem-sfb-nodal-curve-stack-smooth pull the nodal open back to the base. Apply
lem-sfb-curve-h0-genus-strata to impose scalar H0 and rank-g H1. Nodal fibres are
reduced by lem-sfb-nodal-relative-dualizing-line, so scalar H0 means geometric
connectedness. This gives a base-change-compatible prestable genus-g open P.
2. By lem-sfb-nodal-relative-dualizing-line take the canonical relative dualizing
line on P. The criterion lem-sfb-nodal-canonical-positivity-tricanonical identifies
its fibrewise ampleness with the zero-marking component inequalities in
IsStablePointedCurve, counting both branches of self-nodes on normalizations.
3. Apply lem-sfb-space-relative-ample-locus to that line. The resulting open A
commutes with arbitrary base change and its source is a scheme. Its fibres have
exactly the stable component inequalities and genus g.
4. The cube of the dualizing line is fibrewise very ample with vanishing H1 by
lem-sfb-nodal-canonical-positivity-tricanonical. Apply
lem-sfb-fibrewise-very-ample-evaluation to obtain a finite locally free pushforward
and a closed evaluation embedding into its quotient projective bundle. There is
no Noetherian or quasi-compact restriction on the base.
5. The preceding criteria prove both directions of the universal property for
stable families, using def-sfb-stable-pointed-moduli-groupoids and
def-sfb-stable-pointed-curve. The full subcategory retains all isomorphisms. Its
scheme tests are represented by A: the comparison to the given family in the
2-fibre product removes automorphisms. Thus it is an OpenModuliSubstack and its
objects have nonempty nodal geometric fibres.
6. By lem-sfb-flat-space-smooth-locus the source smooth locus W commutes with
arbitrary base change. Properness makes the image of its closed complement
closed. Take its complement in the base. A nonempty bad fibre remains nonempty
under a residue-field extension, so this complement commutes with every base
change and represents smoothness of the whole pulled-back family. This includes
empty fibres and uses no connectedness or genus condition for the smooth open.
-/
theorem stable_and_smooth_family_open_loci (k : Type u) [Field k]
    (g : ℕ) (hg : 2 ≤ g) :
    ∃ (stableOpen smoothOpen :
        (X : ProperCurveModuli (Spec (.of k))) → X.base.left.Opens),
      (∀ X : ProperCurveModuli (Spec (.of k)),
        (∀ (T : Over (Spec (.of k))) (h : T ⟶ X.base),
          ((∃ l : T.left ⟶ (stableOpen X).toScheme,
              l ≫ (stableOpen X).ι = h.left) ↔
            IsStableGenusSpaceFamily g T
              (Limits.pullback X.family.projection (yoneda.map h))
              (Limits.pullback.snd X.family.projection (yoneda.map h)))) ∧
        (∀ (T : Over (Spec (.of k))) (h : T ⟶ X.base),
          ((∃ l : T.left ⟶ (smoothOpen X).toScheme,
              l ≫ (smoothOpen X).ι = h.left) ↔
            ∀ (U : Over (Spec (.of k)))
              (a : yoneda.obj U ⟶ Limits.pullback X.family.projection (yoneda.map h)),
              AlgebraicSpace.IsEtale a →
                Smooth ((yoneda.preimage
                  (a ≫ Limits.pullback.snd X.family.projection (yoneda.map h))).left))) ∧
        (∀ (Y : ProperCurveModuli (Spec (.of k))) (a : Y ⟶ X),
          stableOpen Y = a.base.left ⁻¹ᵁ stableOpen X ∧
          smoothOpen Y = a.base.left ⁻¹ᵁ smoothOpen X) ∧
        HasFiniteLocallyFreeProjectiveRealization
          (Over.mk ((stableOpen X).ι ≫ X.base.hom))
          (Limits.pullback X.family.projection
            (yoneda.map (Over.homMk (stableOpen X).ι rfl :
              Over.mk ((stableOpen X).ι ≫ X.base.hom) ⟶ X.base)))
          (Limits.pullback.snd X.family.projection
            (yoneda.map (Over.homMk (stableOpen X).ι rfl :
              Over.mk ((stableOpen X).ι ≫ X.base.hom) ⟶ X.base)))) ∧
      ∃ A : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
        (∀ X : ProperCurveModuli (Spec (.of k)),
          A.property X ↔ IsStableGenusSpaceFamily g X.base
            X.family.space.obj.obj X.family.projection) ∧
        (∀ X : ProperCurveModuli (Spec (.of k)),
          A.property X → X.family.HasNonemptyNodalGeometricFibres) := by
  sorry

end AlgebraicGeometry
