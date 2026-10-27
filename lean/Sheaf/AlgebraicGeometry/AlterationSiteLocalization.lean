/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Localization of the prime-to-ell alteration site

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Proposition 1.1.10,
§1.2.3, proof of Proposition 1.2.6, Definition 2.3.1 and Remark 2.3.2, printed pp.24--28
(blueprint: lem-per-alteration-site-localization).

The equivalence is specified over the category of schemes over `T`, using the existing
full-subcategory inclusion, `Over.post`, and `Over.iteratedSliceForward`. Thus its forward
functor is composition with `T → S`, preserving the underlying schemes and maps over `T`.
No choice of an unspecified functor is used to define any subsequent data.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- The alteration site over an object is the localized alteration site.

The first existential records the Noetherian property of `T`, a consequence of finite type,
so it is a conclusion rather than an extra hypothesis. The equality of functors specifies
composition on schemes and morphisms. The next two clauses give equality of the topologies
via their covering sieves and the explicit slice-sieve correspondence. The last clause is
the covering-family criterion at the terminal slice object, for an arbitrary index universe.

Source: ILO, Travaux de Gabber, II 1.1.10, 1.2.3, proof of 1.2.6, 2.3.1--2.3.2,
printed pp.24--28 (blueprint: lem-per-alteration-site-localization).

Proof:
1. By `lem-weil-pbc-finite-type-over-noetherian`, `T` is Noetherian. Composition preserves
   finite type by `lem-sfb-finite-type-composition-base-change`; it preserves maximal
   dominance and generic finiteness by composing the finite residue-field towers.
2. Conversely, `lem-per-alteration-arrow-properties` shows that an arrow to `T` in `alt/S`
   is finite type, maximally dominant and generically finite. These assignments preserve
   the underlying schemes and arrows and are inverse, giving the specified equivalence.
3. The generating presieves agree under this equivalence: etaleness and prime-to-ell
   residue lifts, as well as properness, surjectivity and maximal prime-to-ell finiteness,
   concern the very same scheme maps and points on both sides.
4. Apply `lem-per-alteration-generators-pullback` and `lem-per-generated-topology-slice`
   to identify the generated topology in the slice with the alteration topology over `T`.
   Only chosen-pullback stability of the raw generators is required, not composition.
5. `Sieve.overEquiv` identifies slice sieves with their underlying sieves. Factorizations
   through a family member automatically commute with the structure maps to `T`, so it
   also identifies generated family sieves. Evaluate at `Over.mk (𝟙 T)` to obtain the
   final criterion, including the empty family.
-/
theorem exists_alterationSiteLocalization (S : Scheme.{u}) [IsNoetherian S]
    (ell : ℕ) [Fact ell.Prime] (T : Alt S) :
    ∃ (hT : IsNoetherian T.obj.left),
      ∃ (e : @Alt T.obj.left hT ≌ Over T),
        e.functor ⋙ Over.post (ObjectProperty.ι _) ⋙ T.obj.iteratedSliceForward =
          ObjectProperty.ι _ ∧
        (∀ (X : @Alt T.obj.left hT) (R : Sieve (e.functor.obj X)),
          R.functorPullback e.functor ∈ @topology T.obj.left hT ell inferInstance X ↔
            R ∈ (topology S ell).over T (e.functor.obj X)) ∧
        (∀ (Y : Over T) (R : Sieve Y),
          R ∈ (topology S ell).over T Y ↔
            Sieve.overEquiv Y R ∈ topology S ell Y.left) ∧
        (∀ (I : Type w) (U : I → Over T),
          Sieve.ofArrows (fun i ↦ e.inverse.obj (U i))
              (fun i ↦ e.inverse.map
                (Over.homMk (U i).hom : U i ⟶ Over.mk (𝟙 T))) ∈
            @topology T.obj.left hT ell inferInstance (e.inverse.obj (Over.mk (𝟙 T))) ↔
          IsCoveringFamily ell (fun i ↦ (U i).left) (fun i ↦ (U i).hom)) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
