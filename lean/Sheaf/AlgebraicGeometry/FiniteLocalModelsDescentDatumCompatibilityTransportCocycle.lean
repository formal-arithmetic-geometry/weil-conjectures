/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum
@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- The cocycle law for compatible transport.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: lem-weil-pbc-finite-local-model-compatible-transport-cocycle)
Proof: Put R = Q ×_T U ×_T U, with its three maps to U. Since Q → U and
U → T are etale, R → T is etale. Its projection to Q is the universal point
above the first lift. Apply e inverse to that point to obtain a section s of
E on R. Compatibility identifies the first transport with the point obtained
from s above the second lift, and its subsequent transport with the point
obtained from s above the third lift. Direct transport also equals the third
point, so these transports coincide. Given arbitrary W, x, a, b, c, the maps
x.left, b, c have equal composites to T. The pullback universal property
therefore gives W → R whose composites are the given maps. Apply naturality
three times to pull back the universal equality. Functoriality of composition
then gives the displayed equality. Proof irrelevance identifies the equalities
of composites used as transport arguments. Empty schemes satisfy the same
universal properties; neither surjectivity nor nonemptiness is needed. -/
theorem finiteLocalModels_descentDatum_compatibility_transport_cocycle
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e) :
    ∀ (W : Scheme.{u}) (a b c : W ⟶ U.left)
      (hab : a ≫ U.hom = b ≫ U.hom)
      (hbc : b ≫ U.hom = c ≫ U.hom)
      (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport b c hbc (t.transport a b hab x) =
        t.transport a c (hab.trans hbc) x := by sorry
end AlgebraicGeometry.Scheme
