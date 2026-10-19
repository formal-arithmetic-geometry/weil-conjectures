/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.HenselianOfEtaleSectionLifting
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-! # Henselianity of the ind-etale closed lift

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 2.2.10,
Lemma 2.2.12 and the proof of Lemma 6.1.2; Stacks Project, Tags 097P and 09XI
(blueprint: lem-zl-henselian-indetale-closed-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra.ClosedLift

/-- The specified closed lift of an ind-etale quotient algebra is henselian along the
extended ideal. The compatible `A`-algebra structure is the one induced from `A ⧸ I`.
Source: Bhatt--Scholze, Definition 2.2.10, Lemma 2.2.12 and proof of Lemma 6.1.2;
Stacks Project, Tags 097P and 09XI
(blueprint: lem-zl-henselian-indetale-closed-lift).

Proof plan:
1. Put `C = ClosedLift A Cbar`, `J = I.map (algebraMap A C)`, and let `rho` be the
quotient map. By lem-exc-closed-lift-filtered, the defining colimit is filtered, so
C is ind-etale over A. By lem-exc-closed-lift-reduction the specified reduction
`theta : C/J -> Cbar` is an isomorphism with `theta rho = toAlgHom A Cbar`.
2. For an etale C-algebra E and a C-algebra map `sigma : E -> C/J`, E is finitely
presented by lem-weil-pbc-etale-algebra-finite-presentation-localization, hence is
ind-etale over C via its constant presentation. Composition stability in
lem-weil-pbc-ind-etale-stability makes E ind-etale over A.
3. Set `q = theta sigma`. It kills IE, so it descends to an A/I-algebra map
`E/IE -> Cbar`. Surjectivity of lem-exc-closed-lift-adjunction gives an A-algebra
map `tau : E -> C` satisfying `toAlgHom A Cbar tau = q`, by its formula on classes.
4. Injectivity of that same adjunction, now with source C, shows `tau u = id`:
both maps have the same composite with `toAlgHom A Cbar`. Thus tau is C-linear.
Since theta is injective, `theta rho tau = q = theta sigma` gives `rho tau = sigma`.
5. Every etale section therefore lifts. Apply
lem-weil-pbc-etale-section-lifting-henselian-pair with ring C and ideal J.
It gives the henselian pair, equivalently unique lifting of idempotents in every
finite C-algebra modulo J. No finiteness or completeness assumption on A or I is used. -/
theorem henselianRing
    (A Cbar : Type u) [CommRing A] [CommRing Cbar] (I : Ideal A)
    [Algebra A Cbar] [Algebra (A ⧸ I) Cbar] [IsScalarTower A (A ⧸ I) Cbar]
    [Algebra.IndEtale (A ⧸ I) Cbar] :
    HenselianRing (Algebra.ClosedLift A Cbar)
      (I.map (algebraMap A (Algebra.ClosedLift A Cbar))) := sorry

end Algebra.ClosedLift
