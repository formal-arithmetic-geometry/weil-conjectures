/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.FpqcMorphismsDescend
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! Gluing the locally effective models and their projections. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Effective affine-open models give a global pullback projection, invariant locally.
Source: Stacks Project, Descent, Tag 02W3, general-base part of the proof, and
Schemes, Tag 01LH.
(blueprint: lem-galois-fpqc-affine-models-glue)

For each affine open U choose the effective model of E_U. For an inclusion of
an affine open B into U, pull back the U-model to B. The two effective models
over B have canonically isomorphic pullbacks to X_B, compatibly with transport:
the compatibility equation in hlocal identifies both transports with D after
projection to V. Full faithfulness of fpqc descent of morphisms (02W0) descends
this isomorphism uniquely. Uniqueness proves the identity and composition laws.
The resulting natural transformation from the diagram of models to the
locally directed affine open cover of S is equifibered. Relative gluing (01LH)
therefore constructs a scheme W over S. The local isomorphisms from the
restrictions of V to W times_S X agree on intersections by uniqueness of
morphism descent. Glue these isomorphisms and their inverses to obtain a global
pullback square. The local projections to W glue to q. On a test scheme mapping
to an affine open U, transport invariance of q
follows from effectivity of E_U and the displayed compatibility equation.
This is precisely the local invariance asserted below; global invariance is
a separate locality argument. All constructions
use open covers, so the argument includes empty bases and empty objects. -/
theorem fpqc_affine_effective_models_glue
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V)
    (hlocal : ∀ U : S.affineOpens,
      ∃ E : Over.DescentDatum (pullback.snd f U.1.ι)
          (Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
        E.IsEffective ∧
        ∀ {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
          (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
          (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
          (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
            (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
              ← Category.assoc, hab])
            (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
              (by simpa [Category.assoc, pullback.condition] using
                  congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left =
            (E.transport a b hab x).left ≫ pullback.fst V.hom (pullback.fst f U.1.ι)) :
    ∃ (W : Over S) (q : V.left ⟶ W.left), IsPullback q V.hom W.hom f ∧
      ∀ (U : S.affineOpens) {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
        (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
        (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
        (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
          (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
            ← Category.assoc, hab])
          (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
            (by simpa [Category.assoc, pullback.condition] using
              congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left ≫ q =
          x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι) ≫ q := by sorry

end AlgebraicGeometry
