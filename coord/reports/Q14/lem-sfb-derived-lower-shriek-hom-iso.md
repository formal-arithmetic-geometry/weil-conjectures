## Worker report

Attached the exact existing instance
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedLowerShriekHom` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, lines 330–334.
No Lean module is delivered. Only the item's `lean` field changes.

I read the node and its two statement dependencies, their Lean records, the complete
ChangeOfCoefficients source including all enclosing binders and docstrings, and the live
server source using `scompile.py --source`. I also read the current blueprint statement
and proof at `main-20261015/blueprint/sec-six-functors-basics/` under
`sk-def-sfb-coefficient-comparisons/lem-sfb-derived-lower-shriek-hom-iso.md` and its proof.
The source and the node agree verbatim. No repair note exists for this item.

Hypothesis and conclusion correspondence:

- The situation of `def-sfb-derived-lower-shriek-hom` has commutative condensed rings:
  `{Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}`, with `[MonObj Λ]`,
  `[IsCommMonObj Λ]`, `[MonObj Λ']`, and `[IsCommMonObj Λ']`.
- Their coefficient morphism is `(a : Λ ⟶ Λ') [IsMonHom a]`. The coefficient map on each
  scheme is `coefficientMap a X`, the actual pullback from the point.
- Flatness, precisely the finite-limit preservation required by the dependency, is
  `[∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]`.
  The derived scalar extensions are the recorded `L(Mod.extendScalars ...)`, with no
  replacement by arbitrary functors.
- The scheme morphism and compactification are `{X Y : Scheme.{u}} (f : X ⟶ Y)` and
  `[HasCompactification f]`. Its chosen open and proper factors are
  `(HasCompactification.compactification f).i` and `.g`. The compactification structure
  supplies the open-immersion and proper properties; no extra geometric assumption is added.
- The sole additional hypothesis, that (Push) for the proper factor is an isomorphism,
  is `[IsIso (derivedPushHom a (HasCompactification.compactification f).g)]`.
- The entire conclusion is `IsIso (derivedLowerShriekHom a f)`. This is invertibility of
  the canonical natural transformation, not pointwise invertibility on a restricted
  class of complexes. Its source is `R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y))`
  and target `L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧`.
  Lean's `F ⋙ G` means apply F then G, so this is precisely the displayed mathematical
  arrow `T^Y ∘ Rf_! → Rf_! ∘ T^X` on the unbounded derived categories.

Dependency declarations used, all in the same ChangeOfCoefficients module:

- `def-sfb-derived-lower-shriek-hom` records
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedLowerShriekHom`, lines 316–326.
  The definition pastes the actual derived proper push comparison, the derived
  open-immersion scalar comparison, and the canonical associators.
- `def-sfb-derived-push-hom` records
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom`, lines 247–253.
  Its mate construction and flatness binders are used directly in the hypothesis.
- The proof dependency `def-sfb-derived-open-immersion-shriek-iso` is the actual
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionShriekIso` in that module.
  Its isomorphism is whiskered by the proper pushforward in the comparison definition.

The existing proof unfolds the comparison and uses the isomorphism instances for both
whiskerings, composition and associators. This is exactly the node's proof: invert (Push),
use the inverse open-immersion isomorphism, and compose their whiskered inverses in reverse
order with the inverse associators. I wrote no proof. The upstream instance can inherit
open proof dependencies; this is a stage-2 attachment, not a claim that its axioms are closed.

Edge cases checked: the statement has no nonemptiness, nonzero-object, boundedness,
constructibility, characteristic, finite-type or Noetherian restriction. Empty schemes and
zero complexes remain included. For identity coefficient changes and identity morphisms,
the criterion remains the same formal invertibility statement. The arbitrary universe `u`
is the existing framework convention: schemes/profinite sets in `u`, abelian groups in
`u + 1`; no additional universe equality or specialization was introduced. Only the proper
factor's comparison is assumed invertible; nothing asserts invertibility of every (Push).

Searches made:

- `msearch.py ... leanfinder "derived lower shriek hom is an isomorphism when push comparison
  is an isomorphism"`: eight hits, principally continuous sheaf pushforward comparisons;
  none is this concrete derived statement.
- `msearch.py ... loogle "isIso_derivedLowerShriekHom, derivedLowerShriekHom"`:
  zero hits; upstream names are not indexed there (unknown identifier).
- `msearch.py ... grep "isIso_derivedLowerShriekHom|derivedLowerShriekHom" WeilConjectures`:
  zero Mathlib hits; the requested subdirectory does not supply these upstream declarations.
- `msearch.py ... grep "derivedLowerShriekHom|isIso_whisker" CategoryTheory`: four hits,
  including Mathlib's `Functor.isIso_whiskerLeft` and `Functor.isIso_whiskerRight`.
- `rg -n 'derivedLowerShriekHom|isIso_derivedLowerShriekHom' lean/WeilConjectures lean/Sheaf`:
  exact upstream instance and definition found in ChangeOfCoefficients. The Sheaf matches
  are documentation in the retired UpstreamExtra copy and a more general compactification
  projection construction; neither is redeclared here.
- `grep -rn 'lem-sfb-derived-lower-shriek-hom-iso' lean/WeilConjectures`: no literal node-id hit;
  the exact declaration was found by name and its full signature and docstring were read.
- The node's upstream audit already names this exact declaration, and the live server source
  confirms it. The node had no `lean` record, so the attachment is still needed.

No new nodes, dependency repairs, statement corrections, disputed statements or node faults.
Validation: `deliver2.py --no-push` will run a real server `#check` of the existing declaration
through scompile, together with the maintainer's preflight. No global build is run.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
