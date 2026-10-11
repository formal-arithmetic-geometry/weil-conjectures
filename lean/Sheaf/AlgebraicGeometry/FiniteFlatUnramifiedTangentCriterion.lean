import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Tangent criterion for etaleness of a finite locally free morphism

Source: literature/stacks-project/varieties.tex, lemma-injective-tangent-spaces-unramified
(blueprint: lem-sc-finite-flat-unramified-tangent-criterion).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be a finite locally free morphism of schemes over a field `k`, and let
`x` and `y = f x` be `k`-rational points (`hκx`, `hκy`). Then `f` is etale at `x` (some open
neighbourhood `U` of `x` has `U.ι ≫ f` etale) if and only if the induced tangent map
`T_{X/k,x} → T_{Y/k,y}` is injective. The existential over `he` supplies the residue-field
identification `κ(y) ≅ κ(x)` that the canonical `schemeTangentMap` takes; rationality of
`x` and `y` already implies it.
Source: literature/stacks-project/varieties.tex, lemma-injective-tangent-spaces-unramified
(blueprint: lem-sc-finite-flat-unramified-tangent-criterion).

Proof: at the rational points `x` and `y` the tangent map is canonically dual to the induced
map on cotangent spaces (`lem-sc-rational-tangent-cotangent-duality`), so by linear duality
(`lem-sc-dual-map-injective-iff-surjective`) tangent injectivity is cotangent surjectivity.
By `lem-sc-rational-unramified-cotangent-criterion` this is equivalent to `f` being
unramified at `x`. Finite locally free means finite, flat and locally of finite presentation
(`def-pc-finite-locally-free`), so by `def-weil-etale-morphism` `f` is etale at `x` if and
only if it is unramified at `x`. -/
theorem finiteLocallyFree_etale_iff_tangentMap_injective
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [f.IsFiniteLocallyFree]
    (x : X)
    (hκx : Function.Bijective (pX.residueFieldMap x).hom)
    (hκy : Function.Bijective (pY.residueFieldMap (f x)).hom) :
    (∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) ↔
      ∃ he : Function.Bijective (f.residueFieldMap x).hom,
        Function.Injective (schemeTangentMap k X Y pX pY f hf x he) := by
  sorry

end AlgebraicGeometry
