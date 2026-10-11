## Worker report

The module lean/Sheaf/AlgebraicGeometry/ThickeningIntegral.lean states
AlgebraicGeometry.isIntegralHom_iff_of_thickenings with a sorry proof. It introduces
no definitions and leaves the node unchanged except for its lean record.

Hypothesis and clause correspondence:
- Schemes S, S', X, X': `{S S' X X' : Scheme.{u}}`, with an explicitly declared
  arbitrary universe u.
- Thickening maps S → S' and X → X': `(i_S : S ⟶ S')`, `(i_X : X ⟶ X')`,
  `(hS : IsThickening i_S)`, `(hX : IsThickening i_X)`. The recorded dependency's
  general IsThickening predicate is precisely IsClosedImmersion ∧ Surjective.
- Morphisms f' : X' → S' and f : X → S: the binders `(f' : X' ⟶ S')`
  and `(f : X ⟶ S)`.
- Morphism of thickenings, f' ∘ i_X = i_S ∘ f:
  `(hcomm : i_X ≫ f' = f ≫ i_S)`, using Lean's forward composition convention.
- No cartesian or finite order hypothesis: no pullback, nilpotence or order binder
  occurs. The predicate used is IsThickening, not IsFirstOrderThickening.
- Conclusion, f integral iff f' integral: `IsIntegralHom f ↔ IsIntegralHom f'`.
  The parenthetical affine/universally-closed explanation is the proof route,
  recorded in the docstring, rather than an additional conclusion.

Dependencies read and used:
- def-sbc-first-order-thickening: Sheaf.AlgebraicGeometry.Thickening,
  AlgebraicGeometry.IsThickening, whose full definition and docstring were read;
  this declaration is in its recorded declarations list.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Integral,
  AlgebraicGeometry.IsIntegralHom, whose signature and docstring were read.
  The node's Mathlib match and lean.note explicitly record this integral component.
  Its main declaration IsFinite describes the unused finite component; it is not
  needed to render the integral component.

Source: https://stacks.math.columbia.edu/tag/09ZV, Lemma 37.3.1, part (5), read
with the proof of parts (1) and (4). The local literature file is unavailable on
this machine; the official Stacks page gives exactly the general-thickening
statement. The docstring records all six steps of the node's proof, including
its shorter converse using composition and separated postcomposition.

Edge cases checked before writing: empty schemes are allowed (surjectivity from
an empty thickening source forces its target empty); identity thickenings give
the same integral property on equal composites; arbitrarily non-Noetherian
schemes and thickenings without a globally nilpotent defining ideal remain
included. No affine, finite, reduced, characteristic or nonempty hypothesis is
added. The universe is arbitrary and there is no quantification over test
objects that could become vacuous in a smaller universe.

Searches for an existing statement:
- msearch.py leanfinder: "Integrality of a morphism of schemes is invariant under
  arbitrary thickenings of source and target in a commutative square": eight
  hits, including IsIntegralHom.comp_iff, of_comp and composition instances;
  no exact statement. These give tools for the proof only.
- msearch.py loogle: "AlgebraicGeometry.IsIntegralHom": twelve hits, the
  definition and permanence/affine-universally-closed API; no thickening theorem.
- msearch.py leansearch: "integral morphism of schemes is invariant under
  thickenings": unavailable (Internal Server Error), recorded by the tool.
- msearch.py grep: "thicken|integral.*(iff|surject)|IsIntegralHom" in
  AlgebraicGeometry/Morphisms: thirteen hits, integral definition and API,
  finite/integral equivalence, and unrelated formal-unramified thickenings.
- rg in WeilConjectures and lean/Sheaf for
  "thicken.*integral|integral.*thicken|isIntegralHom.*thicken": no matches.
- grep -rn for the item id in WeilConjectures: no matches.
- rg for the proposed declaration isIntegralHom_iff_of_thickenings in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no matches.

No node correction, missing notion, unusable dependency or statement dispute
was found. Server compilation and the delivery dry run are required before READY.

## Second reading by G1

I independently read the sandbox node and module, both statement-dependency
nodes and their declarations, and the official Stacks source. The local Stacks
checkout is absent. I read more-morphisms.tex directly from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
labels definition-thickening and lemma-thicken-property-morphisms, and checked
https://stacks.math.columbia.edu/tag/09ZV and
https://stacks.math.columbia.edu/tag/04EX. The source assumes general schemes and
a morphism of general thickenings, without an ambient base, finite order,
Noetherian, or cartesian assumption. Part (5) is exactly this node's conclusion.

Object, hypothesis, and conclusion inventory, with correspondence and verdict:
- Four schemes S, S', X, X': `{S S' X X' : Scheme.{u}}`. Exact; `universe u`
  is declared and arbitrary, with no scheme property or base ring assumed.
- Closed immersion i_S: S -> S', surjective on underlying points:
  `(i_S : S ⟶ S') (hS : IsThickening i_S)`. Exact. In the recorded dependency
  module Sheaf.AlgebraicGeometry.Thickening, `IsThickening i_S` is literally
  `IsClosedImmersion i_S ∧ Surjective i_S`. I opened its definition, not merely
  the dependency's main name IsFirstOrderThickening.
- Closed immersion i_X: X -> X', surjective on underlying points:
  `(i_X : X ⟶ X') (hX : IsThickening i_X)`. Exact, using the same public
  dependency predicate. Mathlib IsClosedImmersion is a closed topological
  embedding with surjective stalk maps; Surjective is Function.Surjective
  on the underlying scheme map. Thus these are the source's closed subschemes
  with equal underlying spaces, including non-finite-order thickenings.
- Morphisms f': X' -> S' and f: X -> S:
  `(f' : X' ⟶ S') (f : X ⟶ S)`. Exact, no extra property required.
- Factorization f' composed with i_X equals i_S composed with f:
  `(hcomm : i_X ≫ f' = f ≫ i_S)`. Exact under forward composition. This is
  the scheme-theoretic factorization of 04EX(5), not just an inclusion of
  underlying sets. Supplying f explicitly is equivalent to that factorization;
  a closed immersion is a monomorphism, so the induced f is unique.
- No cartesian or finite order requirement: neither is a binder. Exact.
- Conclusion: f integral if and only if f' integral:
  `IsIntegralHom f ↔ IsIntegralHom f'`. Exact, with the same order. I opened
  Mathlib.AlgebraicGeometry.Morphisms.Integral: IsIntegralHom extends
  IsAffineHom and requires `(f.app U).hom.IsIntegral` on every affine open U.
  IsAffineHom requires affine inverse images of affine opens. These are the
  integral component recorded in def-weil-finite-integral-morphism's
  declarations, mathlib_match and lean.note, not its finite component IsFinite.
  The node's parenthetical account of affineness and universal closedness is
  a proof explanation, not an additional conclusion.

Edge cases: no index set or order parameter is introduced; hence empty index
sets and n = 0 cannot be excluded by a binder. In particular, order-zero and
identity thickenings are included by the general predicate. Empty schemes are
allowed: surjectivity forces a thickening target empty when its source is
empty, and introduces no nonemptiness requirement. Zero rings and their empty
spectra are likewise permitted. There is no characteristic, field, affine,
Noetherian, or global nilpotence restriction. Scheme.{u} is universe-polymorphic
in the same universe as Mathlib's scheme category, with no test-object
quantifier in a smaller universe. All variables and the universe are bound.

Independent searches, using different phrasing from the worker:
- msearch.py leanfinder: "Closed surjective immersions of schemes preserve
  integrality in commuting squares". Eight hits: integral closed immersions,
  universally closed integral morphisms, the affine/universally-closed
  characterization, composition, and comp_iff. No exact commuting-thickening
  theorem; these are proof tools only.
- msearch.py loogle: "AlgebraicGeometry.IsIntegralHom,
  AlgebraicGeometry.IsClosedImmersion". One hit, the integral closed immersion
  instance, which does not state the desired equivalence.
- msearch.py leansearch: "Integral morphism unchanged by closed immersions
  inducing homeomorphisms". Service unavailable (Internal Server Error);
  this is not evidence of absence. Other searches completed.
- msearch.py grep: "IsIntegralHom.*iff|integral.*thicken|thicken.*integral".
  Twenty-one hits, scheme integrality API and unrelated measure integration;
  no exact statement.
- Direct rg of Mathlib/AlgebraicGeometry, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for thickenings, nilpotence and integrality:
  existing thickening definitions and unrelated infinitesimal results only.
  A narrower search for "integral.*thicken|thicken.*integral" and the proposed
  declaration in WeilConjectures, lean/Sheaf and upstream names had no match.

No mismatch was found. I retained the module and node signature unchanged.
The two imports are used by the two predicates. There are no definitions,
private copies, file-local instances or notation, new nodes, dependency modules,
statement corrections, or proved theorems in this delivery. The sole theorem
has a sorry proof. Both docstrings carry the source and blueprint id. The
statement docstring follows all six node proof steps: thickening properties,
the easy direction by integral composition and separated postcomposition,
the affine/universally-closed characterization, universal closedness descent
along the surjective thickening, affineness via inverse images and 06AD,
and the characterization again. This supplies the complete proof route for
stage 3 without proving anything at stage 2.

Verification: scompile.py compiled the module on the server in 1.7 seconds,
exit code 0, with no warnings. The stage2_delivery.py signature reader agrees
with the node's lean.statement (including its binder order). deliver2.py
--no-push printed OK: preflight and compilation passed. No Lean or node changes
were necessary; the second reading adds this independent review only.
