/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Exceptional Hom transport through fully faithful comparisons

Source: Stacks Project, categories.tex, Tags 0037, 07RB and 0DV0
(definition-adjoint, lemma-adjoint-fully-faithful, lemma-compose-counits), with the
explicit four-arrow Hom transport and comparison-unit normalization of
(blueprint: lem-sf-fully-faithful-exceptional-hom-transport).

The maps below are constructed from the specified adjunctions. The theorem concerns
objects in the image of the comparison functor on the source category.

## Main declarations

- `homMap`: the specified composite on Hom sets.
- `originMap`: the image of the first adjunction unit under the two functors.
- `fullyFaithful_transport`: bijectivity, naturality and counit normalization.
-/

@[expose] public section

set_option autoImplicit false

universe uXe vXe uTe vTe uXp vXp uTp vTp

namespace CategoryTheory.ExceptionalHomTransport

open CategoryTheory

variable {Xe : Type uXe} [Category.{vXe} Xe]
variable {Te : Type uTe} [Category.{vTe} Te]
variable {Xp : Type uXp} [Category.{vXp} Xp]
variable {Tp : Type uTp} [Category.{vTp} Tp]

/-- The specified four-arrow Hom transport: precompose by `b`, apply the two given
adjunction Hom bijections, and then apply `CZ` on morphisms.
Source: Stacks Project, categories.tex, Tags 0037 and 0DV0; explicit Hom chain
(blueprint: lem-sf-fully-faithful-exceptional-hom-transport). -/
def homMap (CZ : Xe ⥤ Xp) {CT : Te ⥤ Tp} {Fe : Xe ⥤ Te} {Ge : Te ⥤ Xe}
    {R : Tp ⥤ Te} {Fp : Xp ⥤ Tp} (adjT : CT ⊣ R) (adjE : Fe ⊣ Ge)
    (b : Fe ⋙ CT ≅ CZ ⋙ Fp) (H : Xe) (L : Tp)
    (q : Fp.obj (CZ.obj H) ⟶ L) : CZ.obj H ⟶ (R ⋙ Ge ⋙ CZ).obj L :=
  CZ.map (adjE.homEquiv H (R.obj L)
    (adjT.homEquiv (Fe.obj H) L (b.hom.app H ≫ q)))

/-- The origin comparison `o_N = CZ(Ge(j_N))` defined by the specified first unit.
Source: Stacks Project, categories.tex, Tags 0037, 07RB and 0DV0
(blueprint: lem-sf-fully-faithful-exceptional-hom-transport). -/
abbrev originMap (CZ : Xe ⥤ Xp) (Ge : Te ⥤ Xe) {CT : Te ⥤ Tp} {R : Tp ⥤ Te}
    (adjT : CT ⊣ R) (N : Te) :
    CZ.obj (Ge.obj N) ⟶ (R ⋙ Ge ⋙ CZ).obj (CT.obj N) :=
  CZ.map (Ge.map (adjT.unit.app N))

/-- The specified transport consists of natural bijections, sends the transported
counit to the invertible origin comparison, and has the stated full-faithfulness
normalization on origin targets. Its unique preimage of that comparison, or of
the identity after normalization, is the transported counit.
Source: Stacks Project, categories.tex, Tags 0037, 07RB and 0DV0; explicit
four-arrow Hom transport and comparison-unit evaluation
(blueprint: lem-sf-fully-faithful-exceptional-hom-transport).

Proof:
1. Write alpha and beta for `adjT.homEquiv` and `adjE.homEquiv`. The formulas of
   lem-weil-pbc-adjunction-of-natural-bijection give alpha(w) = j followed by R(w)
   and beta(mu) = identity, for these given units and counits.
2. Precomposition by b, alpha, beta, and CZ.map are bijections; the last uses
   full faithfulness of CZ. Naturality of b, alpha and beta and preservation of
   composition by CZ give the two displayed naturality identities.
3. By lem-sp-adjunction-unit-fully-faithful-left, full faithfulness of CT makes
   every j_N invertible. Applying Ge and CZ makes originMap invertible.
4. For q with target CT(N), take the unique v with CT(v) = b_H followed by q.
   Naturality of j gives alpha(CT(v)) = v followed by j_N. Naturality of beta
   then gives h(q) = CZ(beta(v)) followed by o_N. Postcomposing by the inverse
   of o_N is exactly the specified inverse-CT-Hom chain.
5. For q = b inverse followed by CT(mu), v = mu and beta(v) = identity, so
   h(q) = o_N. Bijectivity makes this its unique preimage. Normalization by
   o_N inverse identifies o_N with the identity, giving precisely the counit
   in the identity-preimage sense on these origin objects. -/
theorem fullyFaithful_transport
    (CZ : Xe ⥤ Xp) (CT : Te ⥤ Tp) [CZ.Full] [CZ.Faithful] [CT.Full] [CT.Faithful]
    (Fe : Xe ⥤ Te) (Ge : Te ⥤ Xe) (R : Tp ⥤ Te) (Fp : Xp ⥤ Tp)
    (adjT : CT ⊣ R) (adjE : Fe ⊣ Ge) (b : Fe ⋙ CT ≅ CZ ⋙ Fp) :
    (∀ (H : Xe) (L : Tp), Function.Bijective (homMap CZ adjT adjE b H L)) ∧
    (∀ (H' H : Xe) (L : Tp) (a : H' ⟶ H) (q : Fp.obj (CZ.obj H) ⟶ L),
      homMap CZ adjT adjE b H' L (Fp.map (CZ.map a) ≫ q) =
        CZ.map a ≫ homMap CZ adjT adjE b H L q) ∧
    (∀ (H : Xe) (L L' : Tp) (q : Fp.obj (CZ.obj H) ⟶ L) (s : L ⟶ L'),
      homMap CZ adjT adjE b H L' (q ≫ s) =
        homMap CZ adjT adjE b H L q ≫ (R ⋙ Ge ⋙ CZ).map s) ∧
    (∀ N : Te,
      IsIso (originMap CZ Ge adjT N) ∧
      homMap CZ adjT adjE b (Ge.obj N) (CT.obj N)
          (b.inv.app (Ge.obj N) ≫ CT.map (adjE.counit.app N)) = originMap CZ Ge adjT N ∧
      (∀ (H : Xe) (q : Fp.obj (CZ.obj H) ⟶ CT.obj N),
        homMap CZ adjT adjE b H (CT.obj N) q ≫ inv (originMap CZ Ge adjT N) =
          CZ.map (adjE.homEquiv H N (CT.preimage (b.hom.app H ≫ q)))) ∧
      (∀ q : Fp.obj (CZ.obj (Ge.obj N)) ⟶ CT.obj N,
        homMap CZ adjT adjE b (Ge.obj N) (CT.obj N) q = originMap CZ Ge adjT N ↔
          q = b.inv.app (Ge.obj N) ≫ CT.map (adjE.counit.app N)) ∧
      (∀ q : Fp.obj (CZ.obj (Ge.obj N)) ⟶ CT.obj N,
        homMap CZ adjT adjE b (Ge.obj N) (CT.obj N) q ≫ inv (originMap CZ Ge adjT N) =
            𝟙 (CZ.obj (Ge.obj N)) ↔
          q = b.inv.app (Ge.obj N) ≫ CT.map (adjE.counit.app N))) := by
  sorry

end CategoryTheory.ExceptionalHomTransport
