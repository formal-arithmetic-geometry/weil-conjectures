/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentification
public import Sheaf.AlgebraicGeometry.SchemeGroupoidModule
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import Sheaf.AlgebraicGeometry.FpqcFiniteTypeModuleDescent

/-! # Quasi-coherent modules and an etale presentation groupoid

Source: Stacks Project, Properties of Spaces, Tag 03M3; Spaces Cohomology, Tag 07UB
(blueprint: lem-sfb-space-qcoh-groupoid-equivalence).

`OrdinaryEtaleIdentification` specifies restriction on the entire localized etale site,
including scalar actions and all restriction maps. The overlap formula specifies the
canonical descent isomorphism on every scheme chart of the relation. Thus the equivalence
below is characterized as the restriction functor, on both objects and morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- View the existing groupoid descent isomorphism through the ordinary tensor interface.
This only unfolds `groupoidModulePullback`, which is the same tensor functor.
Source: Stacks, Groupoids, definition-groupoid-module; Properties of Spaces, Tag 03M3
(blueprint: lem-sfb-space-qcoh-groupoid-equivalence). -/
def groupoidModuleOrdinaryBeta {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R}
    {i : R ⟶ R} {c : Limits.pullback s t ⟶ R} {hG : Scheme.IsGroupoid s t e i c}
    (M : Scheme.GroupoidModule s t e i c hG) :
    (Scheme.Modules.tensorPullback t).obj M.moduleObj ≅
      (Scheme.Modules.tensorPullback s).obj M.moduleObj := by
  simpa only [Scheme.groupoidModulePullback] using M.beta

/-- Restriction to a surjective etale scheme atlas is the canonical equivalence with
quasi-coherent modules on its relation groupoid, and detects coherence when the space
is locally Noetherian. The representing square orders its projections as `(t,s)`, so
`t = pr_0` and `s = pr_1`. The identity, inverse and composition are the given groupoid
maps; their source/target identities uniquely determine them on this relation.

The identifications `a` say that the ordinary module underlying `E(F)` is precisely the
restriction of `F` to the atlas. The first equation identifies the overlap datum with
restriction of the same sections of `F`, after every chart base change. The second
specifies restriction on morphisms. Naturality and linearity are included in `a`.

Source: Stacks, Properties of Spaces, Tag 03M3, proposition-quasi-coherent;
Spaces Cohomology, Tag 07UB, lemma-coherent-Noetherian
(blueprint: lem-sfb-space-qcoh-groupoid-equivalence).

Proof:
1. Use lem-sfb-space-qcoh-cartesian-chart-family and the scheme Zariski/etale
   quasi-coherent equivalence to write F as compatible modules F_V on all charts.
   On U put M = F_U. The transition isomorphisms c_t and c_s give beta = c_s^{-1} c_t.
   On the diagonal these maps agree. On triples cancellation of the middle transition
   gives the cocycle. Module maps commute with the transitions. This constructs E's
   functor, with exactly the section and morphism formulas displayed below.
2. Given (M,beta), on V use E_V = U times_X V with projections a_V and b_V.
   Algebraic-space fibre products and etale covering calculus make b_V a surjective
   etale scheme map; its singleton cover is fpqc. Pullback preserves quasi-coherence.
   Pull beta to E_V times_V E_V and use scheme fpqc descent to obtain N_V with an
   identification theta_V : b_V^* N_V -> a_V^* M respecting the descent datum.
3. For f : V_1 -> V_2 put d = 1_U times f. On the cover use
   theta_{V_1}^{-1} d^*theta_{V_2}. Pullback composition types this map; its overlap
   square is beta's square. Full faithfulness of fpqc descent gives c_f uniquely.
   The identity and composition equations hold on the cover by cancellation of theta,
   hence hold before pullback by faithfulness.
4. Assemble (N_V,c_f) by the cartesian-chart characterization and scheme comparison.
   Equivariant maps descend uniquely on each V, commute with c_f by faithfulness,
   and assemble into maps on X. Uniqueness proves the functor laws.
5. Starting with F, descent identifies N_V with F_V, compatibly with all transitions
   and module maps, giving the first natural inverse identity. Starting with (M,beta),
   at V=U the cover is s:R -> U and beta^{-1} identifies its datum with descent of M.
   Thus N_U is M. Pull the equivariance square back to U times_X R; it is the same
   cocycle, so faithfulness proves it. Uniqueness gives the second natural identity.
6. Coherence implies coherence on U by the chart definition. Conversely, coherent F_U
   is of finite type by the locally Noetherian scheme criterion. Its pullback a_V^*F_U
   is of finite type and is b_V^*F_V. Finite-type fpqc descent makes F_V finite type.
   Every V is locally Noetherian, so the same scheme criterion makes F_V coherent.
   This is exactly chartwise coherence; no compactness or separation is used. -/
theorem space_qcoh_groupoid_equivalence {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U R : X.EtaleSite) (hp : IsSurjective U.obj.hom) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map t.hom.left) (yoneda.map s.hom.left)
      U.obj.hom U.obj.hom)
    (e : (X.etaleForget.obj U) ⟶ (X.etaleForget.obj R))
    (i : (X.etaleForget.obj R) ⟶ (X.etaleForget.obj R))
    (c : Limits.pullback (X.etaleForget.map s) (X.etaleForget.map t) ⟶ (X.etaleForget.obj R))
    (hG : Scheme.IsGroupoid (X.etaleForget.map s) (X.etaleForget.map t) e i c) :
    (∃ E : X.QCoh ≌
        Scheme.GroupoidModule (X.etaleForget.map s) (X.etaleForget.map t) e i c hG,
      ∃ a : ∀ F : X.QCoh,
        OrdinaryEtaleIdentification X U F.obj (E.functor.obj F).moduleObj,
        (∀ (F : X.QCoh) (T : X.EtaleSite) (r : T ⟶ R)
          (m : Γ((Scheme.Modules.tensorPullback (X.etaleForget.map (r ≫ t))).obj
            (E.functor.obj F).moduleObj, ⊤)),
          (a F).app T (r ≫ s)
            ((atlasTransitionOn (E.functor.obj F).moduleObj (E.functor.obj F).moduleObj
              (X.etaleForget.map s) (X.etaleForget.map t)
              (groupoidModuleOrdinaryBeta (E.functor.obj F))
              (X.etaleForget.map r) (X.etaleForget.map (r ≫ s))
              (X.etaleForget.map (r ≫ t))
              (X.etaleForget.map_comp r s).symm (X.etaleForget.map_comp r t).symm).hom.app
                ⊤ m) = (a F).app T (r ≫ t) m) ∧
        (∀ (F G : X.QCoh) (f : F ⟶ G) (T : X.EtaleSite) (q : T ⟶ U)
          (m : Γ((Scheme.Modules.tensorPullback (X.etaleForget.map q)).obj
            (E.functor.obj F).moduleObj, ⊤)),
          (a G).app T q
            (((Scheme.Modules.tensorPullback (X.etaleForget.map q)).map
              (E.functor.map f).val).app ⊤ m) =
            f.hom.val.app (op T) ((a F).app T q m))) ∧
    (∀ (_hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
      (F : X.QCoh),
      (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F.obj)) ↔
      RingedSpace.IsCoherent (X.etaleForget.obj U).toRingedSpace
        ((X.schemeRestriction U).obj F.obj)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
