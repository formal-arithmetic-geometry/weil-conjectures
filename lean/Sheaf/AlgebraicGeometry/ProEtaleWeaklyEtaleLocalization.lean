/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Localization of the small pro-etale site at a weakly etale object

Source: Stacks Project, Tags 098K, 094T, 0951, 00XZ, 04IX and 09AE
(blueprint: lem-weil-proetale-weakly-etale-localization).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Localization at a weakly etale object identifies the small pro-etale sites, their
constant ring sheaves, and their module sheaves. The equivalence is oriented from the
slice to the site of `W.left`; its inverse is the assignment called `iota_j` in the node.
The object equalities fix the underlying schemes, and the heterogeneous equalities
specify the actual structure arrows and underlying maps without explicit transports.
The ring comparison
is uniquely specified by its composites with the constant-presheaf units. The final
functor equality specifies both the sectionwise action and the components of morphisms;
composing its functor with `SheafOfModules.overFunctor` gives ambient restriction.

Source: Stacks Project, Tags 098K, 094T, 0951, 00XZ, 04IX, 09AE, 01L7 and 01HI
(blueprint: lem-weil-proetale-weakly-etale-localization).

Proof plan:
1. Compose weakly etale maps using 094T. Conversely cancel the weakly etale structure
   map using 0951 (`WeaklyEtale.of_comp`). The two assignments leave schemes and arrows
   unchanged, giving mutually inverse concrete categories and an equivalence of skeleta
   (`def-weil-size-convention`, `lem-weil-pbc-weakly-etale-composition-base-change`,
   `lem-trf-weakly-etale-between-objects`).
2. The fpqc finite-affine-cover condition depends only on the arrows to the covered scheme,
   not on the base. Thus the coverings agree and precomposition identifies sheaves
   (`def-weil-pbc-proetale-site`, `def-pur-localized-ringed-site`).
3. Restrict the constant ring presheaf. Ring-valued sheafification commutes with localization
   (`Functor.pushforwardContinuousSheafificationCompatibility`, Tag 00XZ). Its unit identity
   identifies constant sections, and the sheafification universal property gives uniqueness
   (`def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`,
   `lem-pur-ring-presheaf-sheafification-localization`).
4. Restrict modules using `SheafOfModules.overFunctor`, then pull their actions back along
   the ring comparison. Naturality gives semilinearity; the inverse ring map reverses this
   operation. Both operations leave section groups and morphism components unchanged
   (`def-pur-localized-ringed-site`, `def-weil-sheaf-of-modules-category`).
5. For an open immersion use its monomorphism property (01L7) for uniqueness. A factorization
   has image in the open; conversely `IsOpenImmersion.lift` (01HI) supplies the factorization
   whenever this image containment holds (`def-weil-open-immersion`,
   `lem-weil-pbc-open-immersion-monomorphism`,
   `lem-weil-pbc-morphism-factors-through-open-subscheme`). -/
theorem weaklyEtale_localization (X : Scheme.{u}) (W : X.ProEt)
    (A : CommRingCat.{u + 1}) :
    (∀ V : W.left.ProEt, WeaklyEtale (V.hom ≫ W.hom)) ∧
    (∀ T : Over W, WeaklyEtale T.hom.left) ∧
    (∃ e : Over W ≌ W.left.ProEt,
      (∀ T : Over W, (e.functor.obj T).left = T.left.left) ∧
      (∀ T : Over W, HEq (e.functor.obj T).hom T.hom.left) ∧
      (∀ (T T' : Over W) (f : T ⟶ T'), HEq (e.functor.map f).left f.left.left) ∧
      (∀ V : W.left.ProEt, (e.inverse.obj V).left.left = V.left) ∧
      (∀ V : W.left.ProEt, HEq (e.inverse.obj V).hom.left V.hom) ∧
      (∀ (V V' : W.left.ProEt) (f : V ⟶ V'), HEq (e.inverse.map f).left.left f.left) ∧
      (∀ (V : W.left.ProEt) (S : Sieve V),
        S ∈ topology W.left V ↔
          S.functorPushforward e.inverse ∈ (topology X).over W (e.inverse.obj V)) ∧
      (∀ (D : Type v) [Category.{w} D],
        ∃ s : Sheaf ((topology X).over W) D ≌ Sheaf (topology W.left) D,
          s.functor ⋙ sheafToPresheaf _ D =
            sheafToPresheaf _ D ⋙ (Functor.whiskeringLeft _ _ D).obj e.inverse.op) ∧
      (∃ (R : Sheaf (topology W.left) RingCat.{u + 1})
          (hR : R.obj = e.inverse.op ⋙
            (((constantSheaf (topology X) RingCat.{u + 1}).obj (RingCat.of A)).over W).obj)
          (c : (constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A) ≅ R),
        (∀ V : W.left.ProEt,
          HEq ((toSheafify (topology W.left)
            ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of A))).app (op V) ≫
              c.hom.hom.app (op V))
            ((toSheafify (topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
                (op (e.inverse.obj V).left))) ∧
        (∀ f : (constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A) ⟶ R,
          (∀ V : W.left.ProEt,
            HEq ((toSheafify (topology W.left)
              ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of A))).app (op V) ≫
                f.hom.app (op V))
              ((toSheafify (topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
                  (op (e.inverse.obj V).left))) → f = c.hom) ∧
        (∃ q : ringedSiteModules.{u + 1}
            (((constantSheaf (topology X) RingCat.{u + 1}).obj (RingCat.of A)).over W) ≌
              ringedSiteModules.{u + 1}
                ((constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A)),
          q.functor ⋙ SheafOfModules.forget _ =
            SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward
              (F := e.inverse) (c.hom.hom ≫ eqToHom hR)))) ∧
    (IsOpenImmersion W.hom →
      Mono W.hom ∧
      (∀ V : X.ProEt, Subsingleton (V ⟶ W)) ∧
      (∀ V : X.ProEt,
        (Nonempty (V ⟶ W) ↔ ∃ a : V.left ⟶ W.left, a ≫ W.hom = V.hom) ∧
        (Nonempty (V ⟶ W) ↔ Set.range V.hom ⊆ Set.range W.hom))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
