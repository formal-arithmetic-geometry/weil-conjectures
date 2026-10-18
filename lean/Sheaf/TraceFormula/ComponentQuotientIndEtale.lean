/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Etale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.RingTheory.IndEtaleStability

/-!
# The quotient onto a component ring is ind-étale

Source: Stacks Project, Algebra, Tags 00EG and 00EH, and Pro-étale Cohomology, Tags
097I and 097K; Hübner–Schmidt, §6 component-ring convention, printed p. 12
(blueprint: lem-trf-component-ind-etale-local-henselian).

The component ideal and component ring are the existing constructions in
`Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion`. A point indexes its connected
component; no openness or finiteness of the collection of components is required.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The canonical component quotient is ind-étale. It remains ind-étale over any base
from which the original ring is ind-étale. If all component rings are henselian local,
the chosen component ring is henselian local.

Source: Stacks Project, Algebra, Tags 00EG and 00EH, and Pro-étale Cohomology, Tags
097I and 097K; Hübner–Schmidt, §6 component-ring convention, printed p. 12
(blueprint: lem-trf-component-ind-etale-local-henselian).

Proof:
1. Let E be the idempotents vanishing on the component of x. The finite subsets F of E
   form a nonempty directed poset. Set J_F = (e : e in F) and d_F = 1 - ∏ (1 - e).
   Complementation and multiplication preserve idempotency. Induction using
   d_(F ∪ {e}) = d_F + e - d_F e shows d_F lies in J_F, while e d_F = e for e in F
   shows J_F = (d_F). The empty stage is J_∅ = (0).
2. Put u_F = 1 - d_F. By lem-weil-pbc-fg-idempotent-ideal-idempotent-generator,
   part (2), the quotient T/J_F is the principal localization T_(u_F), compatibly
   with its structural map from T, since its kernel is (1 - u_F).
3. By lem-weil-pbc-principal-localization-open-immersion the spectrum map of this
   localization is an open immersion, hence étale by part (1) of
   lem-weil-pbc-etale-composition-cancellation. The quotient stage is therefore étale
   over T and finitely presented by lem-weil-pbc-etale-algebra-finite-presentation-localization.
4. The maps T/J_F → T/I_Z form a cocone. To verify the universal property in
   def-weil-pbc-category-colimit, take any compatible cocone to C. Its empty-stage
   map defines g : T → C. Compatibility with each singleton stage forces g(e) = 0
   for all e in E. Thus g factors uniquely through T/I_Z. Compatibility on every
   quotient generator gives all required cocone factorizations; surjectivity of
   T → T/I_Z gives uniqueness. This exhibits T/I_Z as the filtered colimit.
5. The étale stages and the preceding colimit exhibit the canonical quotient map as
   ind-étale, exactly by def-weil-pbc-ind-etale-algebra. Only finite subsets of E,
   rather than finitely many components, enter this construction.
6. If f : A → T is ind-étale, compose it with the ind-étale quotient using
   lem-weil-pbc-ind-etale-stability to obtain the second conjunct.
7. Apply the hypothesis that every component ring is henselian local to x. This is
   universal instantiation, not a claim about arbitrary quotients. When T is the zero
   ring there is no point x of its spectrum, so the statement is vacuous.
-/
theorem componentQuotient_indEtale (T : Type u) [CommRing T] (x : PrimeSpectrum T) :
    (Ideal.Quotient.mk (componentIdeal T x)).IndEtale ∧
    (∀ (A : Type u) [CommRing A] (f : A →+* T), f.IndEtale →
      ((Ideal.Quotient.mk (componentIdeal T x)).comp f).IndEtale) ∧
    ((∀ y : PrimeSpectrum T, HenselianLocalRing (componentRing T y)) →
      HenselianLocalRing (componentRing T x)) := by
  sorry

end AlgebraicGeometry
