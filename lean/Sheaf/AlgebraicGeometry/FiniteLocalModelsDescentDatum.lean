/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleDescentData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Descent datum from finite etale local representatives

Source: Stacks Project, Tag 03RV, construction of the descent datum.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Finite etale local representatives give a finite etale scheme over an etale surjection,
with transport agreeing with the identification of sections of the original sheaf.

Source: Stacks Project, Tag 03RV, the local representatives and descent datum;
Tag 02W5, the Yoneda construction cited there.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum)

Proof: Choose a representative Q_i and its presheaf isomorphism from hrep for
 each member of the given cover. Transport that isomorphism back through the
 equivalence of sites to the localization at U_i. Form U as the coproduct of
the U_i and V as the coproduct of the Q_i. The map U to T is an etale
 surjection. The inverse image of each open and closed component U_i in V
 is Q_i. Thus V to U is finite by locality of finiteness on the target,
 and etale by locality of etaleness on the source.
The local identifications with E glue over the disjoint open components to the
displayed presheaf isomorphism e. Over U times_T U their two restrictions are
both identified with E; Yoneda full faithfulness gives the corresponding unique
scheme isomorphism. Its identity and cocycle follow by Yoneda faithfulness from
the identity and cocycle of these identifications. Express this datum in transport
form. For two lifts a and b of an etale W to U, the same section s of E(W)
corresponds to the two points displayed in the equation, which therefore agree
after transport. Naturality holds for every scheme mapping to the overlap:
base changes of V are etale over the overlap, hence are objects of its small
etale site, where Yoneda was applied. No finite bound on the ranks or finite
cover is needed. For the empty cover T and U are empty, V is empty, and the
sheaf condition for the empty covering gives the unique identifications. -/
theorem finiteLocalModels_descentDatum
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (𝒰 : Cover.{u} etalePrecoverage T)
    (hrep : ∀ i, ∃ Q : (𝒰.etalePrecoverageToEtale i).left.FiniteEtale,
      Nonempty (((Etale.overSheafEquiv (𝒰.etalePrecoverageToEtale i)
        (Type (u + 1))).functor.obj (E.over (𝒰.etalePrecoverageToEtale i))).obj ≅
          uliftYoneda.{u + 1}.obj Q.obj)) :
    ∃ (U : T.Etale) (_ : Surjective U.hom)
      (D : AlgebraicGeometry.FiniteEtaleDescentData U.hom)
      (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
        uliftYoneda.{u + 1}.obj
          (MorphismProperty.Over.mk ⊤ D.obj.V.hom D.property.2)),
      ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (D.obj.datum.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left := by sorry

end AlgebraicGeometry.Scheme
