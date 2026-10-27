## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiprojectiveQCComposition` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_on_affineOpens_comp`.
There is one theorem, with proof `sorry`, no new definitions, and no statement correction.
The node is copied from the current shared repository, changing only `lean`.

Hypothesis and clause correspondence:

- Schemes X, Y, S: `{X Y S : Scheme.{u}}`, with arbitrary explicit universe u.
- Scheme morphisms f : X → Y and g : Y → S: `(f : X ⟶ Y) (g : Y ⟶ S)`.
- Both morphisms of finite type: `[LocallyOfFiniteType f] [QuasiCompact f]` and
  `[LocallyOfFiniteType g] [QuasiCompact g]`, precisely the conjunction in the recorded
  finite-type definition node (there is no bundled finite-type class).
- Quasi-compact final base S: `[CompactSpace S]`; no separation assumption is imposed.
- Existence of an invertible module L on X: `hf : ∃ (L : X.Modules) (_ : L.IsInvertible), …`.
- L is f-relatively ample: quasi-compactness is already explicit as `[QuasiCompact f]`;
  the remainder of hf is `∀ V : Y.Opens, IsAffineOpen V → … IsAmple …` on the
  restriction to `(f ⁻¹ᵁ V).toScheme`.
- Existence of an invertible module M on Y: `hg : ∃ (M : Y.Modules) (_ : M.IsInvertible), …`.
- M is g-relatively ample: `[QuasiCompact g]` and the analogous every-affine-open
  condition in hg, now for `V : S.Opens`.
- Finite type of g ∘ f: `LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g)`.
- Existence of invertible N on X: the concluding `∃ (N : X.Modules) (_ : N.IsInvertible), …`.
- N is (g ∘ f)-relatively ample: the explicit concluding `QuasiCompact (f ≫ g)` and
  `∀ V : S.Opens, IsAffineOpen V → … IsAmple …` for its inverse-image restriction.

In every restriction, `(tensorPullback (h ⁻¹ᵁ V).ι).obj L` is the canonical module
pullback by the open inclusion, hence restriction. `∃ h : … .IsInvertible, @IsAmple … h`
only supplies the invertibility proof needed to type absolute ampleness. Restricting
an invertible module preserves invertibility; this adds no geometric hypothesis.
There is no choice of a new restriction functor, arbitrary comparison, or changed ampleness.

Statement dependencies read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; read their full structures/docstrings.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`; read class signatures/docstrings.
- def-sc-invertible-module: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; read the local-trivialization class
  and its pullback instance.
- def-weil-pbc-ample-invertible-module: `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple`; read its complete predicate/docstring,
  including quasi-compactness and positive tensor powers with affine nonvanishing loci.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`, `CompactSpace`;
  read its class/docstring, which explicitly does not require separation.

The canonical restriction functor is the already constructed
`AlgebraicGeometry.Scheme.Modules.tensorPullback` from
`WeilConjectures.AlgebraicGeometry.TensorPullback`, also exposed by the recorded
module of def-pc-module-pullback. It is not redefined.

All already stated proof dependencies are imported. The two proof dependencies
lem-sfb-finite-type-composition-base-change and lem-sfb-relative-ample-absolute-twist
have no Lean binding in the read repository; there is therefore no module to import
for them. Their roles and the complete five-step DAG proof appear in the theorem
docstring. They are proof dependencies only, not missing statement prerequisites.

Source checked directly: literature/stacks-project/morphisms.tex, 01VH at line 8627,
0C4K at line 8888, and 0C4M at line 9755. 0C4M gives the composition assertion;
0C4K explains the finite common twist over a quasi-compact base.

Edge cases checked before writing: empty S forces empty Y and X; the affine-open
conditions remain meaningful (including the empty affine open). The finite cover may
be empty and the proof's common exponent is then zero. Identity morphisms and zero
powers require no extra hypotheses or exclusions. No nonempty, reduced, Noetherian,
separated or quasi-separated hypothesis is introduced, in particular none on Y.
Schemes and their structure sheaves share the usual arbitrary scheme universe u;
there is no independent universe of test objects capable of making a hypothesis vacuous.

Searches actually run through msearch.py for Q23 / this item:

- leanfinder: "Composition of finite type scheme morphisms with relatively ample
  invertible sheaves over a quasi compact base admits a relatively ample invertible
  sheaf": OK 8 hits, all ordinary finite-type, finite, quasi-finite or quasi-compact
  composition assertions (including `AlgebraicGeometry.quasiCompact_comp`); no match.
- loogle: `"IsRelativelyAmple", "IsAmple"`: OK 0 hits.
- grep in Mathlib/AlgebraicGeometry:
  `[Rr]elatively[Aa]mple|[Qq]uasi[Pp]rojective|[Aa]mple.*[Cc]omp`: OK 0 hits.
- rg in live lean/WeilConjectures and lean/Sheaf for relative-ampleness names and
  quasi-projective composition: no existing composition statement. The project has
  inline affine-open encodings in SchemeRelativeAmpleBaseChange and
  SchemeRelativeAmpleAffineCover; these were read and followed.
- rg of the item ID in lean/WeilConjectures: no match.
- rg of the chosen theorem name in Mathlib, WeilConjectures and Sheaf: no match.

No STATEMENT-DISPUTED issue found. The previous worker's stale-assignment conclusion
confused stage-1 completion with stage-2 completion: the live node is split and
reviewed by Q10 but has no `lean`. This delivery preserves that split and its review;
it supplies only the missing stage-2 binding.

## Second reading by Q23

A separate second pass by this same dispatcher-started worker read the node and the
completed module side by side. No other agent was started, as the brief expressly
prohibits that; the maintainer provides the independent delivery review.

The two finite-type pairs, CompactSpace S, both existential invertible modules, both
every-affine-open ampleness hypotheses, the finite-type conclusion, and the existential
relatively ample N all match the node clause by clause. Quasi-compactness belongs to
the respective relative-ampleness conditions and is stated explicitly for f, g and
the composite. The proof witnesses on restricted modules do not impose new assumptions.
No hypothesis on Y's separation or compactness was smuggled in. No mismatch was found
and no mathematical statement was changed.

Validation: scompile.py passed for both sandbox and actual library module names with
no errors or warnings (11.5 s and 8.6 s). An initial module-visibility error for
QuasiCompact was repaired by adding its explicit public Mathlib import. Only the
node's lean field differs from the live read copy, the recorded signature matches
the file verbatim, all Lean lines are at most 100 characters, and the only sorry
is the item theorem's proof.
