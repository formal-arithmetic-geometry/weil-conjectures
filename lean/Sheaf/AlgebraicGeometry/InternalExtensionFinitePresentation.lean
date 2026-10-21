/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Scalar extension and finite presentations of internal sheaf modules

Source: main-20261015, `lem-sfb-extend-to-qlbar-constructible.proof.md`, final clause,
tensoring local finite presentations on strata
(blueprint: lem-sfb-internal-extension-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry.ProEtale

/-- Extension of scalars preserves finite presentations, with the canonical comparisons
on finite free modules and on their cokernels. The regular-module comparison is fixed by
its composite with the balanced-tensor quotient; the finite-free comparisons are fixed
by their composites with every coproduct injection. The cokernel comparison is fixed
by its composite with the image of the cokernel arrow.

Source: main-20261015, `lem-sfb-extend-to-qlbar-constructible.proof.md`, final clause
(blueprint: lem-sfb-internal-extension-finite-presentation).

Proof, following the node:
1. Abelian sheaves form an abelian category by `lem-sfb-grothendieck-sheafification`.
The sheaf tensor preserves colimits by `sk-def-sfb-sheaf-tensor`, hence is additive by
`lem-sfb-preserving-colimits-additive`. Thus `lem-sfb-modobj-abelian` applies to R and S.
The balanced-tensor functor of `def-sfb-modobj-extension` preserves finite colimits by
`lem-sfb-modobj-extension-right-exact` and therefore also preserves zero morphisms.
2. Give S its regular left action and right R-action through φ. Apply
`lem-sfb-mixed-bimodule-right-unitor` to obtain e₀ : E(R) ≅ S. Its forward map composed
with the quotient is S ◁ φ followed by multiplication. Its inverse is the ambient
right-unitor inverse, followed by S ◁ η[R] and the quotient.
3. Regard the finite biproducts in `def-sfb-finitely-presented-module` as coproducts.
Preservation of finite colimits gives e(k) by the equations on all injections, using
e₀ on each summand. Construct its inverse the same way using e₀.inv. The composites
are identities by coproduct uniqueness. This includes k = 0, the initial object.
4. For f : R^m ⟶ R^n, E sends its cokernel to a cokernel of E(f), since it preserves
finite colimits and zero maps. Conjugate by e(m), e(n). The map e(n).inv followed by
E(cokernel.π f) is a cokernel of e(m).inv ≫ E(f) ≫ e(n).hom. Cokernel uniqueness gives
the normalized comparison c. Compose E's image of a given presentation isomorphism
with c to obtain the displayed presentation of E(M).
5. Its ranks remain finite, so this witnesses `Mod.IsFinitelyPresented S (E.obj M)`.
Only right exactness was used; no flatness or preservation of kernels is required.
-/
theorem internalExtension_finitePresentation (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      Mod.IsFinitelyPresented R M →
        Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M)) ∧
    ∃ e₀ : (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S,
      Mod.extendπ φ (Mod.regular R) ≫ e₀.hom.hom = S ◁ φ ≫ μ[S] ∧
      ∃ e : ∀ k : ℕ,
          (Mod.extendScalars φ).obj (Mod.finiteFree R k) ≅ Mod.finiteFree S k,
        (∀ (k : ℕ) (i : Fin k),
          (Mod.extendScalars φ).map (biproduct.ι (fun _ : Fin k ↦ Mod.regular R) i) ≫
              (e k).hom = e₀.hom ≫ biproduct.ι (fun _ : Fin k ↦ Mod.regular S) i) ∧
        ∀ (m n : ℕ) (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n),
          ∃ c : (Mod.extendScalars φ).obj (cokernel f) ≅
              cokernel ((e m).inv ≫ (Mod.extendScalars φ).map f ≫ (e n).hom),
            (Mod.extendScalars φ).map (cokernel.π f) ≫ c.hom =
                (e n).hom ≫
                  cokernel.π ((e m).inv ≫ (Mod.extendScalars φ).map f ≫ (e n).hom) ∧
            ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
                (_p : M ≅ cokernel f),
              Nonempty ((Mod.extendScalars φ).obj M ≅
                cokernel ((e m).inv ≫ (Mod.extendScalars φ).map f ≫ (e n).hom)) := by
  sorry

end AlgebraicGeometry.ProEtale
