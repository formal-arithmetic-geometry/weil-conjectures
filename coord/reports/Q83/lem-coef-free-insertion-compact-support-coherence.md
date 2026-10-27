## Worker report

Item: lem-coef-free-insertion-compact-support-coherence, stage 2, Q83.
Module: Sheaf.Paper.FreeInsertionCompactSupportCoherence.
Main declaration: AlgebraicGeometry.freeInsertionCompactSupportCoherence.

The module states the entire coherence assertion, with one sorry, and constructs four
small named maps used by that statement. The maps are literal mates or Hom-adjuncts
under the existing adjunctions, with real data and no sorry. No definition or category
from the dependency interfaces is duplicated. The item's statement is unchanged.

Hypotheses and objects, in node order:

* The fixed algebraic closure of the finite field is D : FiniteFieldDatum, with
  D.k as the ground field. The prime and characteristic condition are l, Fact l.Prime,
  and _hl : l ≠ D.p. E, Field E, Algebra (Padic l) E, and FiniteDimensional give the
  finite coefficient extension. Its ring and uniformizer are the recorded
  Padic.coefficientExtensionIntegers l E and Padic.coefficientExtensionUniformizer l E.
  The coefficient-evaluation interface takes the quotient by the (n+1)st power of
  the principal ideal, so Lean n : ℕ is paper level n+1, covering every positive level.
* X and Y are Scheme.{u}, with Over (Spec (.of D.k)) instances. On each structure
  map, LocallyOfFiniteType and QuasiCompact give finite type, and IsSeparated gives
  the separatedness expressly required by this item. The map f is over that base,
  separated, locally of finite type and quasi-compact. c : Compactification f has
  the actual open immersion c.i and proper morphism c.g with f = c.i ≫ c.g.
* S : StrictEtaleCompactSupport ... c is the recorded compact-support construction
  of the dependency lem-pur-etale-coefficient-system-adjoint. It retains the existing
  PX, PY and PZ evaluation packages, strict semilinear system categories and their
  ordinary unbounded DerivedCategory localizations. S.functor is exactly
  S.derivedOpen ⋙ S.properDerived.system.direct, and S.levelFunctor n is its finite
  analogue. S.evaluation n is the composite of the canonical open and proper
  evaluation comparisons. No pro-etale exceptional functor is substituted: the
  node introduces both sites but explicitly makes all assertions on the etale sites.
* H is a reference StrictEtaleExceptionalAdjoint for that same S, supplied by the
  cited dependency theorem. Its sole use in the new formulas is to access
  H.val.quotientProjection h, the canonical invertible compact-support comparison
  in the direction q inverse. Its existing coherence fixes the open and proper
  pieces as adjunction mates, and fixes their composite; this is not an arbitrary
  chosen natural isomorphism. This reference packages the canonical q in the
  question and imposes no condition on the independently quantified right adjoints.
* G and adj : S.functor ⊣ G are arbitrary chosen system right adjoints; Gn and
  adjN n : S.levelFunctor n ⊣ Gn n are arbitrary finite-level choices. In particular
  they need not equal H.right or H.levelRight; neither of those is used anywhere.
  This avoids assuming evaluated coherence for the actual right adjoints being
  asserted in the theorem. Existence of the reference construction is already the
  content of the explicitly cited dependency theorem, rather than a geometric or
  boundedness hypothesis added to this node.
* L_n, e_n, derived quotient T, and sigma are respectively PX/PY.derivedExtension,
  .evaluation, (.scalar h).derived, and .sigma h. These are the exact existing
  free-insertion package, including strict representative normalizations. The
  helper strictEtaleAdjointTransition is the scalar-extension adjunct of P.transition,
  not a newly assigned transition or an arbitrary collection of component maps.

Conclusion clauses, in the order of the Lean conjunction:

1. strictEtaleFreeInsertion S n is constructed with the inverse of mateEquiv for
   PX.derivedAdj n and PY.derivedAdj n, applied to (S.evaluation n).inv. This is a_n,
   the transpose of the identity under the free-insertion/evaluation identifications.
   Concretely its transpose is F_n applied to the insertion unit followed by the
   inverse evaluated compact-support comparison; the normalized insertion unit is
   the identity in the node's notation. The first conjunct says IsIso a_n.
2. The second conjunct gives every r ≤ n evaluated component. On the left,
   PY.evaluation r maps a_n, S.evaluation r identifies e_r F with F_r e_r,
   and F_r maps PX.derivedBelow h. On the right, PY.derivedBelow h identifies
   e_r L_n^Y with T^Y(n,r), followed by H.val.quotientProjection h inverse,
   which is q(n,r). This is precisely e_r a_n = q(n,r), with the necessary
   source/target comparisons written explicitly rather than treated as equal types.
3. The next conjunct is the node's sigma equation, as an equality of genuine
   system-derived morphisms for every K. Lean ≫ lists composition in execution
   order. The right side first applies L_n^Y(q inverse), then sigma^Y at F_m K,
   then a_m; the left side applies a_n at T^X K then F(sigma^X).
4. strictEtaleRightEvaluationMate adj adjN n is the mate of the inverse canonical
   compact-support evaluation comparison. It has source G ⋙ e_n^X and target
   e_n^Y ⋙ G_n. Its invertibility is the fourth conjunct, so it fixes an actual
   natural isomorphism, not just isomorphic values on objects.
5. The Hom-bijection conjunct quantifies over every K,N and h : K → e_n G N.
   Transpose h back under L_n^X/e_n, then F/G, precompose with a_n, and transpose
   under L_n^Y/e_n. The result equals the inverse finite-level transpose of h
   followed by the constructed right-evaluation mate. This expressly identifies
   the node's natural representing bijections and hence their counit normalization.
   Naturality is inherited from the existing Hom equivalences and natural maps.
6. The next equation evaluates the system unit and uses the same right-evaluation
   mate and S.evaluation to identify it with adjN.unit at e_n M.
7. The following equation identifies the evaluated counit with adjN.counit,
   using the inverse of S.evaluation at G N. It fixes the same counit-compatible
   evaluation map, without an independent isomorphism choice.
8. strictEtaleQuotientMate H adjN h is mateEquiv of the canonical inverse q under
   adjN m and adjN n. Its component is explicitly asserted to equal eta_n followed
   by G_n(q inverse) and then G_n(T^Y epsilon_m), exactly the displayed b formula.
9. The transition equation uses strictEtaleAdjointTransition of the actual G N.
   Its evaluated-right-adjoint identifications are exactly those of clauses 4-7.
   It is t(GN) followed by theta_n = T^X(theta_m) followed by b and G_n(t(N)),
   the fully typed form of t(GN) = G_n(t(N)) b.
10. The final quantified clause permits any G', adj', Gn', adjN'. The first equation
    intertwines theta with adj.rightAdjointUniq adj' and its finite analogues.
    The second intertwines b with the finite rightAdjointUniq isomorphisms.
    These are Mathlib's unique counit-compatible changes. Together with actual
    transition naturality and the stated unit/counit equations, these express that
    all formulas are unchanged under precisely those changes, as the node requires.

Dependency declarations used:

* Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum, D.k, D.p.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite (publicly reexporting
  CoefficientExtension): Padic.coefficientExtensionIntegers,
  Padic.coefficientExtensionUniformizer, and the existing coefficient quotients.
* WeilConjectures.Compactification.RefinementCategory and its Defs dependency:
  AlgebraicGeometry.Compactification; no private version of compactifications.
* Sheaf.Paper.CoefficientSystemDerivedComparison and its ImageData/Models dependencies:
  SheafOfModules.CoefficientSystem, coefficientLevelModules and derived image data.
* Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint and CoefficientEvaluationModels:
  CoefficientEvaluationDerivedPackage, .derivedAdj, .derivedExtension, .evaluation,
  .derivedBelow, .sigma, .scalar, .transition and DerivedCoefficientScalarExtension.
  The last interface is the derived change of coefficient ring, with its tensor,
  restriction and normalized derived adjunction. It supplies the etale quotient
  operation actually needed here. The general pro-etale binary derivedTensor
  recorded on def-weil-derived-tensor was read, but is not substituted for this
  already existing coefficient-change interface on the etale site.
* Sheaf.Paper.EtaleCoefficientSystemAdjoint: strictEtaleCoefficientSystem,
  strictEtaleLevel, StrictEtaleEvaluation, StrictEtaleCompactSupport,
  StrictEtaleExceptionalAdjoint, their concrete DerivedCategory instances,
  S.functor, S.levelFunctor, S.evaluation and H.val.quotientProjection.
* Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, using the
  dependency's standard localization instances (morphism universe u+2).
* Mathlib.AlgebraicGeometry.Sites.Etale: Scheme.smallEtaleTopology. The small
  pro-etale definition Scheme.ProEt was also read; it occurs only in the setup,
  since the asserted formulas explicitly work on the etale sites.
* The convention-only scheme-properties node is used via its named Mathlib
  LocallyOfFiniteType, QuasiCompact, IsSeparated and Over/IsOver definitions.
* Mathlib.CategoryTheory.Adjunction.Mates: CategoryTheory.mateEquiv and
  Adjunction.homEquiv. Mathlib.CategoryTheory.Adjunction.Unique:
  Adjunction.rightAdjointUniq, with the recorded counit convention.
* Proof import Sheaf.CategoryTheory.SystemLevelLeftExtension is included. The
  Brown-construction, coefficient-projection and evaluation-bound proof nodes
  currently have neither a Lean record nor a Mathlib match, so have no module to
  import yet. Their use and complete proof route are retained in the docstring.

Edge cases checked before writing and on rereading:

* n=0 is paper level 1; all n : ℕ and all r ≤ n are covered. Equality m=n is
  included in both sigma and mate/transition formulas; all tensor identifications
  use the dependency's normalized derived units, not an assumed identity of types.
* Zero objects, zero morphisms and empty schemes are allowed. There is no nonempty
  condition, constructibility, normalization, or bound on any input complex.
* No quotient ring map is assumed flat. T is the derived scalar-extension functor;
  sigma and the actual system transitions are taken from the recorded package.
* Coefficient rings and sheaves use Type (u+1), the etale site has its actual
  object/morphism universes, and localization morphisms use u+2 as in the dependency.
  There is no forced equality of site object and morphism universes.
* Arbitrary changes of both the system and finite right adjoints are included,
  including identity changes. No componentwise detection of equality is assumed.

Searches (2026-10-22):

* msearch.py leanfinder, query "Derived free insertion at a coefficient level
  commutes with compact support and identifies exceptional adjoint quotient
  transition mates": 8 unrelated hits (Kaehler differential/free Lie/presentation
  declarations); no match.
* msearch.py loogle, query "CategoryTheory.mateEquiv,
  CategoryTheory.Adjunction.rightAdjointUniq": 0 combined-query hits. The named
  Mathlib declarations were then opened directly and reused with their exact types.
* msearch.py grep, query "freeInsertion|free_insertion|mateEquiv", restricted to
  CategoryTheory/Adjunction: 5 hits, all the generic mateEquiv declaration or its
  associated counit formulas. These are ingredients, not the statement of this node.
* msearch.py leansearch, query "The left adjoint to coefficient evaluation commutes
  with compactly supported direct image and its right adjoint reduction comparisons
  are adjunction mates": 8 hits, including generic evaluation adjunctions and module
  pullback adjunctions; none gives strict varying-coefficient compact-support coherence.
* rg over lean/WeilConjectures and lean/Sheaf for this node id and freeInsertion /
  free_insertion: no matching declaration. A wider name/concept check for definitions
  of adjointTransition, transitionAdj, quotientMate, evaluationMate and freeInsertion
  found coefficientSequenceTransitionAdjoint (pro-etale coefficient-sequence encoding),
  TraceFormulaASystem.adjointTransition (the levelwise derived A-system encoding),
  and Etale.pushPullTransitionAdj (a geometric pull/push map). Their full signatures
  were read: none takes the strict etale evaluation package and its actual system
  transition, so none supplies this helper. Existing scalar Hom equivalences and
  mateEquiv are used directly, rather than redefined.
* rg over Mathlib, the two project Lean roots, and dag/lean_names_upstream.json for
  all five proposed full declaration names: no collisions.

No statement dispute, correction, new DAG node or dependency-module repair is needed.
Only the item's lean field is changed; the accepted split and its statement are retained.

Validation: the complete file compiled cleanly with the prescribed scompile.py on
2026-10-22, in both sandbox and library module modes. The final compile after removing
an unnecessary pipeline notation and adding the available proof dependency was also
clean (19.6 s sandbox, 15.5 s library). All variables and universes are explicit and
autoImplicit is disabled. There are four definitions with real data and one theorem
with exactly a sorry proof. No local instance, local notation or private definition.

## Second reading by Q83

This is the dispatch worker's self-check, not a claim of an independent second agent;
the dispatcher expressly prohibits starting another agent. Independent statement review
is the maintainer's delivery review, as specified in the task brief.

I reread the node and the complete Lean signature after compilation. The clause-by-clause
mapping above was checked against the actual compositions, including both comparison
orientations, the sigma equation, and the Hom-bijection direction. In particular q is
H.val.quotientProjection inverse, while the b formula uses its hom, namely q inverse.
The actual transition is the scalar adjunct of PX.transition on G.obj N. The right
adjoints in the theorem are independent quantified choices, so their evaluated
compatibilities are conclusions rather than properties assumed of those choices.
The node expressly requires separated X and Y, so both structure-map IsSeparated
hypotheses are present even though the upstream adjoint theorem allows more general Y.
I replaced a pipeline expression in the Hom formula by an ordinary parenthesized
inverse equivalence for readability, then recompiled. No mathematical statement changed.
