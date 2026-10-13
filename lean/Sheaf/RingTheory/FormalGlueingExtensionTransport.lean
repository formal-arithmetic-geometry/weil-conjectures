/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.RingTheory.FormalGlueingData
import Sheaf.Paper.FormalGlueingCanonicalMaps

/-!
# Transport of glueing maps along a localized isomorphism

Source: Stacks Project, More on Algebra, Proposition 05ER.
(blueprint: lem-weil-pbc-formal-glueing-extension-transport).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- Transport the chart maps across localizations of an extension injection.
Source: Stacks Project, More on Algebra, Proposition 05ER, third paragraph.
(blueprint: lem-weil-pbc-formal-glueing-extension-transport).
Proof: identify the restricted canonical chart with the localized R-module by
module extensionality and algebraMap_smul. The bundled object equalities transport
the component maps, and the heterogeneous equalities identify the structural maps.
Define the prime map to be theta and each chart map to be psi.chart i
composed with the inverse of j localized at f i. The chart maps are bijective.
To check the prime compatibility, precompose with the localization of the scalar
extension of j. It is bijective because comparison identifies it with the scalar
extension of the bijective localized j. Naturality of comparison and the equation
theta composed with the scalar extension of j equals psi.prime reduce both sides
to psi's prime compatibility. For the overlap compatibility, precompose with j
localized first at f i and then at f k. Localization preserves inverses, so this
map is bijective. Naturality of interchange reduces both sides to psi's overlap
compatibility. These two equations define the required morphism. The prime map
is bijective by theta, and the chart maps are composites of bijections.
No condition on Can's morphism maps is used: only its canonical object maps enter.
For an empty chart set only the prime map and its bijectivity remain. -/
theorem exists_extension_transport {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (H E : ModuleCat.{max u v w} R) (X : Data.{u, v, max u v w} φ f)
    (ψ : Can.obj H ⟶ X) (j : H →ₗ[R] E)
    (θ : extend φ E ≃ₗ[S] X.M')
    (hj : ∀ i, Function.Bijective (localMap (f i) j))
    (hψ : ∀ i, Function.Bijective (ψ.chart i))
    (hθ : HEq (θ.toLinearMap.comp (extendMap φ j)) ψ.prime) :
    ∃ Φ : Can.obj E ⟶ X,
      Function.Bijective Φ.prime ∧ ∀ i, Function.Bijective (Φ.chart i) := by sorry

end FormalGlueing
