## Worker report

The module defines and states `AlgebraicGeometry.unramified_fibre_point_isolated`.
For a morphism `f : X ⟶ S` with `[LocallyOfFiniteType f]`, a point `x : X`, and an
open neighbourhood `U` of `x` whose restricted morphism is locally of finite type
with open diagonal, the conclusion has three clauses:

* `IsOpen ({f.asFiber x} : Set (f.fiber (f x)))` states that the canonical fibre point
  is isolated in the scheme-theoretic fibre.
* `∀ ξ : f.fiber (f x), f.fiberι (f x) ξ = x → ξ = f.asFiber x` states uniqueness of
  the fibre point over `x` under the first projection.
* `IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))` states the equivalent singleton-open
  formulation in the subspace inverse image of `f x`.

The unramified-neighbourhood hypothesis renders the node's explicit Stacks 02G4(1)
meaning of “unramified at x”; its conjunction uses Mathlib's
`LocallyOfFiniteType` and `IsOpenImmersion (pullback.diagonal ...)` corresponding to
the recorded dependency `def-weil-unramified-morphism`.

Dependencies used: `AlgebraicGeometry.Scheme` and `Scheme.Hom` from Mathlib
(`def-pc-scheme`); `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, and `asFiber`
from `Mathlib.AlgebraicGeometry.Fiber` (`def-pc-scheme-fibre`);
`AlgebraicGeometry.LocallyOfFiniteType` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`def-weil-finite-type-morphism`); `AlgebraicGeometry.IsOpenImmersion` and
`CategoryTheory.Limits.pullback.diagonal` (`def-weil-unramified-morphism`);
`AlgebraicGeometry.Scheme.residueField` is used through `fiber` (`def-weil-residue-field`);
and `AlgebraicGeometry.IsOpenImmersion` (`def-weil-open-immersion`).

Edge cases checked: the statement allows arbitrary schemes and universes `Scheme.{u}`,
zero-dimensional or empty fibres, and does not assume the fibre is nonempty; the
canonical point `f.asFiber x` exists for every `x`, and the singleton in the inverse
image is well-typed by `rfl`.

Searches made on 2026-10-11:

* `msearch.py` LeanFinder: "a locally finite type morphism unramified at a point has an
  isolated fibre point"; eight hits including `Algebra.unramifiedLocus`,
  `AlgebraicGeometry.FormallyUnramified`, and local ring unramified results, none giving
  the node's scheme-level conclusion.
* `msearch.py` Loogle: "AlgebraicGeometry.FormallyUnramified,
  AlgebraicGeometry.Scheme.Hom.fiber"; zero hits.
* `msearch.py` LeanSearch: "A morphism unramified at x has x isolated in its scheme
  theoretic fibre"; service unavailable (Internal Server Error); no verdict inferred.
* `msearch.py` grep: `unramified|isolated|singleton_asFiber` in
  `AlgebraicGeometry/Morphisms`; 16 hits. The two quasi-finite singleton theorems require
  quasi-finiteness, not the node's unramified-neighbourhood hypothesis; no exact match.
* `rg` of `lean/Sheaf` and `WeilConjectures` for fibre, singleton, and unramified notions:
  existing isolated-fibre-point hypotheses in `IsolatedFiberPointQuasiFiniteAffinePairs`
  and `EtaleSplitsOffIsolatedPoints`, but no theorem giving this conclusion.
* `rg` of `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the item
  id and proposed declaration name: no hits.

The node's six statement dependency records and the declaration signatures/docstrings
in Mathlib were read. No dependency module or new notion is needed. `fiber` unfolds to
base change along `S.fromSpecResidueField (f x)` and thus uses the prescribed residue
field, not a geometric fibre or a differently chosen field.

Source checked online because the local Stacks source is absent:
[02G4](https://stacks.math.columbia.edu/tag/02G4) defines unramifiedness at a point;
[02G7](https://stacks.math.columbia.edu/tag/02G7) gives discrete unramified fibres.
The neighbourhood wording of the node is equivalent to the affine definition, using
locality of unramifiedness. No correction was needed.

Server compilation passed without errors or warnings. The sole postponed proof is
`AlgebraicGeometry.unramified_fibre_point_isolated`; its docstring carries all four
DAG proof steps and their dependencies. An independent second reader will add the
second-reading section before delivery.

## Second reading by F1

Independently read the item node, its complete module, and all six statement
dependency nodes and their recorded Mathlib declarations. The following is the
object/hypothesis/conclusion checklist, with the Lean rendering and verdict.

1. Schemes X and S and a scheme morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   PASS: Mathlib's `Scheme` and `Scheme.Hom` are locally affine locally ringed
   spaces and their morphisms, as `def-pc-scheme` requires.
2. Point x and image s: `(x : X)` and `f x`. PASS: s is determined by x,
   not an independently quantified point with an omitted equality.
3. Residue field κ(s): `S.residueField (f x)`, used within `f.fiber (f x)`.
   PASS: ResidueField.lean:45 defines the quotient of the stalk by its maximal
   ideal and supplies its Field instance. No algebraically closed field is used.
4. Locally finite type f: `[LocallyOfFiniteType f]`. PASS: FiniteType.lean:43
   uses finite-type ring maps on affine pairs; the dependency records the
   equivalence with the affine-cover formulation. Global local finite type is
   expressly in this node, even though only a neighbourhood is needed.
5. An open neighbourhood X' of x: `∃ U : X.Opens, x ∈ U ∧ ...`.
   PASS: `U.ι` is the open-subscheme inclusion and `U.ι ≫ f` the restriction.
6. The restriction is unramified: `LocallyOfFiniteType (U.ι ≫ f) ∧
   IsOpenImmersion (pullback.diagonal (U.ι ≫ f))`. PASS: this is verbatim
   the conjunction in `def-weil-unramified-morphism.mathlib_match`, rather than
   a stronger étale, finite-presentation, flatness or global unramified assumption.
7. Fibre X_s and first projection p: `f.fiber (f x)` and `f.fiberι (f x)`.
   PASS: Fiber.lean:38 and :41 define the pullback along
   `S.fromSpecResidueField (f x)` and its first projection. These are exactly
   the declarations of `def-pc-scheme-fibre`.
8. The unique point ξ above x: `f.asFiber x` and the conclusion
   `∀ ξ : f.fiber (f x), f.fiberι (f x) ξ = x → ξ = f.asFiber x`.
   PASS: existence and p(ξ)=x are already supplied by the definition at
   Fiber.lean:116 and `fiberι_asFiber` at :120. Thus selecting the canonical
   point loses no quantifier or existence condition; the explicit clause
   states the node's uniqueness, not an additional geometric claim.
9. Singleton open in the scheme fibre:
   `IsOpen ({f.asFiber x} : Set (f.fiber (f x)))`. PASS: exactly isolation,
   with no assertion that all points of the full fibre are isolated.
10. Equivalent singleton open in the inverse-image subspace:
    `IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))`. PASS: the topology is the
    subtype topology, not openness in all of X. `f.fiberHomeo (f x)` at
    Fiber.lean:103 identifies the two singletons. Giving both equivalent
    clauses as a conjunction is exactly the node's two formulations.

Source reading: local Stacks .tex files are absent on this machine, so read
the actual upstream [morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex)
at `section-unramified`, `definition-unramified`,
`lemma-unramified-characterize`, `lemma-base-change-unramified`,
`lemma-unramified-over-field`, and `lemma-diagonal-unramified-morphism`.
The source section imposes no standing Noetherian, separated, quasi-compact,
or characteristic assumption. [02G4](https://stacks.math.columbia.edu/tag/02G4)
uses affine neighbourhoods; locality gives the node's unramified open
neighbourhood formulation. [02GE](https://stacks.math.columbia.edu/tag/02GE)
identifies unramifiedness with local finite type and an open diagonal.
[02G7](https://stacks.math.columbia.edu/tag/02G7) gives discreteness after
residue-field base change of that neighbourhood. No statement correction is
needed; the sandbox has no `statement_change` or additional delivery nodes.

Edge cases: empty X (including an affine zero ring) has no x, so the statement
is vacuous as in the node; empty S admits no image of an x. The fibre at f(x)
contains `asFiber x`, with no extra Nonempty instance. Empty U cannot satisfy
x ∈ U. No assumption forces other fibres to be nonempty or discrete.
The natural-number and index-set edge cases are inapplicable: neither occurs.
Arbitrary residue characteristics are allowed. The bound universe u is
arbitrary; Scheme morphisms and fibre products use the same ambient scheme
universe, with no quantified test-scheme universe that could become vacuous.

Independent searches on 2026-10-11, using different queries from the worker:

* LeanFinder via msearch: "open diagonal locally finite type morphism isolated
  singleton fiber point" returned eight candidates. The diagonal theorem
  establishes an unramifiedness characterization, not this conclusion;
  `Scheme.Hom.discrete_fiber` requires a finite morphism. No exact match.
* Loogle via msearch: `AlgebraicGeometry.Scheme.Hom.asFiber, IsOpen` returned
  `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`. Opened its signature
  at QuasiFinite.lean:395: it is an equivalence with QuasiFiniteAt, not an
  implication from the node's unramified-neighbourhood hypothesis.
* LeanSearch via msearch: "An open diagonal and locally finite type imply that
  a point in the fibre is isolated" failed with Internal Server Error.
  Recorded as unavailable, with no inferred verdict.
* msearch grep for `quasiFiniteAt_iff_isOpen_singleton_asFiber|`
  `isDiscrete_preimage_singleton` found quasi-finite material only.
* Independently ran rg over Mathlib/AlgebraicGeometry, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json for `isOpen_singleton`,
  `isDiscrete_preimage`, `singleton.*asFiber`, `unramified.*isolated`,
  `unramified_fibre_point_isolated` and `IsolatedFiberPoint`. Read the
  quasi-finite candidate's signature; other hits are applications or lemmas
  assuming isolation. No existing theorem renders this node, and no new
  notion or dependency module is required.

H5/H6/H8/H9: the module contains no new definition, private copy, local notation,
local instance, or proved theorem. The one named theorem has proof `sorry`.
Its source/blueprint docstring records all four DAG proof steps and their named
dependencies. Every variable and universe is bound; imports serve the fibre,
finite-type and open-diagonal expressions; all Lean lines are within 100 characters.
The node's `lean.statement` equals the theorem signature verbatim.

Mismatches and changes: none in the Lean or node; retained them as written.
Added only this independent second-reading report. Server scompile passed in
2.3 seconds with no errors or warnings.
