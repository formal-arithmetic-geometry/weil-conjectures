/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-! # Local Frobenius equations on finite locally free modules -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Finite locally free modules admit natural scalar-compatible coordinates after an
étale test scheme is restricted to an affine neighbourhood of any given point.

Source: Stacks Project, More on Étale Cohomology, Tag 0GKU,
label lemma-frobenius-linear-on-vb, the choice of a basis on an affine trivializing open.
(blueprint: lem-weil-pbc-frobenius-vector-bundle-local-frames)

Proof: Pull E back to U. Local freeness supplies a finite free trivialization near x;
intersect with an affine neighbourhood to obtain A, and reindex the finite basis by Fin n.
Pull this basis to every étale V over A. The free-module section equivalence identifies
sections with tuples of functions on V. Compose with the inverse ULift equivalence.
These are additive and scalar compatible because pullback of modules and the free-module
coordinate maps are linear. Their naturality follows by applying tensor-pullback
composition to each basis vector. The unit-normalized tensor comparison and the
etaleTensorHomEvaluation_naturality lemma identify this comparison with the restriction
map used by etaleTensorSectionsSheaf. In rank zero all coordinate types are singletons;
on an empty U there is no point x to consider. -/
theorem frobenius_vectorBundle_local_frames
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree] :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ n : ℕ,
      let L := Etale.localizationRestriction AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (a : Γ(V.left, ⊤))
          (s : (L.obj G).obj.obj (op V)),
          e V (ULift.up ((@id Γ(((MorphismProperty.Over.map ⊤
              (inferInstance : Etale (A.ι ≫ U.hom))).obj V).left, ⊤) a) •
            (@id Γ((Modules.tensorPullback ((MorphismProperty.Over.map ⊤
              (inferInstance : Etale (A.ι ≫ U.hom))).obj V).hom).obj E, ⊤) s.down))) =
                a • e V s) := by
  sorry

end AlgebraicGeometry.Scheme
