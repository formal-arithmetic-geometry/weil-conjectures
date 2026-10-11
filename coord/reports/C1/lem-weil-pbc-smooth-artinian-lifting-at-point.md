## Worker report

Module: `Sheaf.AlgebraicGeometry.SmoothArtinianLiftingAtPoint`.
Declaration: `AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point`.
This states the node's equivalence, with `sorry` as the only proof. No new
notion or dependency module was needed and no node statement was corrected.

Hypotheses and clauses:
- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally finite type: `[LocallyOfFiniteType f]`.
- Locally Noetherian base: `[IsLocallyNoetherian S]`.
- The specified source point: `(x : X)`.
- (1), smooth on an open neighbourhood: `∃ U : X.Opens, x ∈ U ∧
  Smooth (U.ι ≫ f)`. `U.ι` is the open-subscheme inclusion.
- Equivalence of (1) and (2): `↔`.
- All Artinian local test rings: `∀ (B' B : Type u)` with explicit
  `CommRing`, `IsArtinianRing`, and `IsLocalRing` instances for both.
  The universe is the same as that of the schemes; there is no independent
  smaller universe of test objects. Rings and schemes can be lifted together
  to a larger universe when needed.
- Small extension: `(φ : B' →+* B)`, `Function.Surjective φ`, and
  `Module.length B' ↥(RingHom.ker φ) = 1`. These are precisely the defining
  conditions of Stacks 02HS. The node's parenthetical residue-field-module,
  maximal-ideal-annihilation and square-zero assertions are consequences,
  not additional restrictions or independent conclusions of the equivalence.
- The induced closed immersion is the explicit term
  `Spec.map (CommRingCat.ofHom φ)`; no statement-level `let` is used.
- Test maps: `α : Spec (CommRingCat.of B) ⟶ X` and
  `β : Spec (CommRingCat.of B') ⟶ S`.
- Commutative square: `α ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ β`.
- Closed point sent to the prescribed point: `α (IsLocalRing.closedPoint B) = x`.
  The named closed point is the prime given by the local ring's maximal ideal.
- Lift: `∃ γ : Spec (CommRingCat.of B') ⟶ X`.
- Both required triangles: `Spec.map (CommRingCat.ofHom φ) ≫ γ = α ∧ γ ≫ f = β`.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (available through the imports).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- Existing Mathlib primitives: `Module.length` (RingTheory.Length; the
  already existing DAG node def-weil-pbc-module-length is a Mathlib leaf),
  `RingHom.ker`, `IsArtinianRing` (RingTheory.Artinian.Module),
  `IsLocalRing.closedPoint` (RingTheory.Spectrum.Prime.Topology).
No private copy of a dependency notion was made. The theorem docstring gives
all five proof steps with their DAG dependencies.

Sources checked: https://stacks.math.columbia.edu/tag/02HX (equivalence (1)/(3))
and https://stacks.math.columbia.edu/tag/02HS (definition of small extension).
The cited local TeX files are absent on this machine, so the official pages
were opened. They confirm the hypotheses and test data verbatim.

Edge cases checked: an empty source has no `x` and is not incorrectly excluded
by a Nonempty hypothesis; local rings here are nontrivial as required for their
closed point; an isomorphism has zero-length kernel and is not a small extension;
no characteristic or residue-field-isomorphism restriction is imposed; rings
may have arbitrary Artinian length, provided the kernel has length exactly one.
Both lift equations have the correct domains and contravariant Spec direction.

Searches:
- `msearch.py ... leanfinder` query: "A morphism locally of finite type over a
  locally Noetherian scheme is smooth at a point iff lifts along all small
  extensions of Artinian local rings exist". Eight hits, including
  `AlgebraicGeometry.isSmooth_iff`, standard-smooth chart criteria, and
  `RingHom.smooth_def`; no Artinian test-ring criterion.
- `msearch.py ... loogle` query: "AlgebraicGeometry.Smooth, IsArtinianRing,
  Module.length". No hits.
- `msearch.py ... grep` query `Artinian|small.extension` in
  `AlgebraicGeometry/Morphisms`. Five hits in QuasiFinite, no criterion.
- `rg` over Mathlib and WeilConjectures for `SmallExtension|smallExtension`
  and Artinian lifting found no existing statement. Search for the item's
  exact ID and `artinian.*lift|lifting.*artinian` in WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json found only references in the
  docstring of EtaleInfinitesimalNeighbourhoods, not a declaration.
- Exact proposed declaration-name search across Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no collision.

Validation: server single-file compile succeeded (1.7 seconds), no errors or
warnings. Initial compile used the nonexistent Artinian.Basic import; repaired
it to the existing Artinian.Module import. No outstanding statement disputes.

## Second reading by C1

Independently read the sandbox node and module together. Verdict: the Lean says
exactly the node's statement; no mismatch found and no Lean or node change needed.
The only change in this reading is this independent review section.

Source check: the local Stacks TeX tree is absent. Read the official pages
https://stacks.math.columbia.edu/tag/02HX and
https://stacks.math.columbia.edu/tag/02HS, and independently read the labelled
TeX blocks `lemma-lifting-along-artinian-at-point` in upstream
`more-morphisms.tex` and `definition-small-extension` in upstream `algebra.tex`
(from https://raw.githubusercontent.com/stacks/stacks-project/master/).
02HX explicitly assumes locally Noetherian S and locally finite type f;
its (1)/(3) is the node's equivalence. Condition (4)'s residue-field
isomorphism is not part of (3), and is correctly absent from this Lean.
02HS imposes exactly local Artinian rings, surjectivity, and length-one kernel.

Objects, hypotheses, and conclusion clauses (each verdict is PASS):

- Schemes X and S: `{X S : Scheme.{u}}`; the same category as def-pc-scheme.
- Scheme morphism f: `(f : X ⟶ S)`; Scheme.Hom, with no base or field added.
- Locally finite type: `[LocallyOfFiniteType f]`, not a quasi-compact or
  finite-type hypothesis. This is the applicable clause of
  def-weil-finite-type-morphism.
- Locally Noetherian base: `[IsLocallyNoetherian S]`, precisely pqf-def-locnoeth;
  no global Noetherianity or extra source hypothesis is imposed.
- Specified point: `(x : X)`; a point of the underlying topological space.
- Smooth at x: `∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)`.
  The neighbourhood is an open subscheme and the inclusion is U.ι;
  Smooth is the recorded def-sbc-smooth-morphisms notion, identified with
  the formally-smooth/locally-finitely-presented definition by Stacks 02H6.
- Equivalence: `↔`, with the smooth-neighbourhood clause on its left.
- Every pair of test rings: `∀ (B' B : Type u) [CommRing B'] [CommRing B]`
  and the four Artinian/local instances. These introduce arbitrary
  commutative Artinian local rings, not fields or algebras over an added base.
- Small extension: `(φ : B' →+* B)` followed by
  `Function.Surjective φ → Module.length B' ↥(RingHom.ker φ) = 1 →`.
  RingHom.ker is an ideal of B', with its canonical B'-module structure;
  Module.length measures that module, not length over B. The node's
  parenthetical residue-field-module, annihilation, and square-zero facts
  are consequences of this definition, not extra conditions to assume.
- Induced i: each `Spec.map (CommRingCat.ofHom φ)` has domain Spec B and
  codomain Spec B', in the recorded contravariant spectrum convention.
- Arbitrary test maps: `∀ (α : Spec (CommRingCat.of B) ⟶ X)` and
  `(β : Spec (CommRingCat.of B') ⟶ S)`, after the small-extension hypotheses.
- Commutative square: `α ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ β →`;
  Lean's composition order is the source's f composed with α equals β with i.
- Closed point condition: `α (IsLocalRing.closedPoint B) = x →`.
  closedPoint is the maximal ideal, and an Artinian local spectrum has
  exactly this point; no residue-field-isomorphism condition is added.
- Existence of lift: `∃ γ : Spec (CommRingCat.of B') ⟶ X`, after all test data.
- First triangle: `Spec.map (CommRingCat.ofHom φ) ≫ γ = α`.
- Second triangle: `γ ≫ f = β`, joined to the first by conjunction.
  Neither uniqueness nor a merely local lift replaces these two equations.

Opened all five statement dependency nodes and read their recorded declarations
in the actual pinned Mathlib sources: Scheme and Scheme.Hom
(Scheme.lean:42,74), Spec and Spec.map (Scheme.lean:470,479),
LocallyOfFiniteType (Morphisms/FiniteType.lean:43), IsLocallyNoetherian
(Noetherian.lean:57), and Smooth (Morphisms/Smooth.lean:62).
The all-affine-open presentations of the latter properties are the same
notions as their nodes' local presentations, as their records explain.
Also read Scheme.Opens.ι (Restrict.lean:52), IsLocalRing.closedPoint
(Spectrum/Prime/Topology.lean:1299), IsLocalRing's Nontrivial superclass
(LocalRing/Defs.lean:30), IsArtinianRing (Artinian/Defs.lean:66),
RingHom.ker (Ideal/Maps.lean:745), and Module.length (Length.lean:35).
No dependency record was unusable, no missing notion required a new node,
and the delivery has no dependency modules, new nodes, or statement correction.

Edge cases: an empty X has no x, exactly as in the source; an empty S admits
no f with such an x. The zero ring is excluded by IsLocalRing's Nontrivial
superclass, correctly matching a ring with a maximal ideal and closed point.
A zero kernel has length zero, so isomorphisms are not small extensions;
length-one extensions of any Artinian length are covered. There is no
characteristic assumption, finiteness of residue fields, or relative-dimension
parameter n (so n = 0 and an index set are inapplicable). `universe u` is
bound explicitly; the test rings inhabit the schemes' universe, with no
independent smaller test universe that could make the criterion vacuous.
The theorem is uniform in u, including larger common universes.

Independent searches, using different wording from the worker:

- msearch leanfinder: "smoothness near a scheme point characterized by solving
  infinitesimal diagrams with length one kernel"; eight hits consisting of
  smooth chart and relative-dimension criteria, not this Artinian criterion.
- msearch loogle: `"lift", IsArtinianRing`; zero hits.
- msearch grep: `length.*ker|ker.*length`; only an exact-sequence length
  computation in Mathlib/RingTheory/Length.lean, not the desired theorem.
- Direct rg, case-insensitive `small.?extension`, `artinian.{0,80}lift`,
  `lift.{0,80}artinian`, and the proposed declaration name over pinned
  Mathlib AlgebraicGeometry and RingTheory/Smooth, WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json: only an algebraic
  formally-smooth lift over a nilradical and the project's
  EtaleInfinitesimalNeighbourhoods proof-docstring citations. Neither states
  this equivalence. No duplicate declaration or name collision was found.

H5/H6/H8/H9: there are no definitions or hidden data holes; the only theorem
has `by sorry`. The module and theorem docstrings give both source tags and
this blueprint ID. All five node proof steps, with their dependency names,
are present in the theorem docstring. All variables and u are explicitly
bound, the imports provide notions actually used, and lines meet the limit.
The node's lean.statement matches the file signature verbatim.

Validation: scompile.py compiled the sandbox module on the server in 1.8 s,
exit code zero, with no errors or warnings. The first invocation used a
relative path from the read-only repository and could not find the sandbox
file; rerunning with its absolute path succeeded. This was an invocation
error, not a compiler or statement defect.
