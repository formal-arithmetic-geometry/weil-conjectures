## Worker report

The module `Sheaf.AlgebraicGeometry.ProperStability` states
`AlgebraicGeometry.proper_stability`, with one `sorry` and no definitions.
The statement is unchanged from the node and its blueprint source:
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-proper-stability.md`.

Clause-by-clause correspondence:
- The class of proper morphisms is Mathlib's `AlgebraicGeometry.IsProper` on
  `Scheme.{u}`. Its definition is separated, universally closed, locally of
  finite type; universal closedness supplies quasi-compactness, hence this is
  exactly the convention's separated, finite type, universally closed notion.
- Stability under arbitrary base change is the first conjunct,
  `MorphismProperty.IsStableUnderBaseChange (@IsProper.{u})`. Its field tests
  every pullback square, not only a chosen fibre product.
- Stability under composition is the second conjunct,
  `MorphismProperty.IsStableUnderComposition (@IsProper.{u})`. Its field takes
  any composable pair with properness of each and concludes properness of
  the composite.
- The field is `(k : Type u) [Field k]`; the two schemes are arbitrary
  `(X Y : Scheme.{u})`. The node names the morphism to `Spec k`, so the
  structure maps are explicit `f : X ⟶ Spec (CommRingCat.of k)` and
  `g : Y ⟶ Spec (CommRingCat.of k)`.
- The hypothesis that X is proper over k is `IsProper f`, preceding the
  implication in the final conjunct. There is no property hypothesis on g.
- The conclusion is `IsProper (pullback.snd f g)`. The pullback is exactly
  `X ×_k Y`, and `pullback.snd` is its projection to Y.

Dependencies read and used:
- `lem-weil-pbc-proper-base-change`: its Mathlib match is the pullback-snd
  instance, `AlgebraicGeometry.IsProper.instSndScheme`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; its complete signature has
  arbitrary f and g over S and only `[IsProper f]`. The same module's
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange` states the first
  stability clause. These declarations have no individual docstrings; the
  module documentation and the IsProper docstring were read.
- `lem-weil-pbc-proper-composition`: the recorded declaration is
  `AlgebraicGeometry.IsProper.instCompScheme` in that same module, with
  `[IsProper f] [IsProper g] : IsProper (f ≫ g)`. The module also supplies
  `AlgebraicGeometry.IsProper.stableUnderComposition`. Again the instance
  has no individual docstring.
- `def-weil-pbc-scheme-conventions`: this is explicitly a convention-only
  node with no module or declaration, directing properness to Mathlib's
  `IsProper`. No replacement convention or private definition is introduced.
The public import of Proper supplies both statement and proof dependencies;
no further proof-only import is needed. The theorem docstring records the
node's full proof plan using both dependency nodes.

Edge cases: X and Y may be empty; no nonemptiness, smoothness, separatedness
of Y, or characteristic restriction is imposed. Both identity base changes
and compositions with identities are included. All fields, including positive
characteristic, are included. The explicit universe u is arbitrary and shared
by schemes and the base field, as in Mathlib's scheme category and Spec.
There is no independent smaller universe of test schemes and no index set.
The statement has no added hypothesis and no discarded clause.

Searches performed:
- `msearch.py leanfinder`: "Proper morphisms of schemes stable under base
  change and composition, proper projection from a product over a field".
  Eight hits include `IsProper.instSndScheme`, `isStableUnderBaseChange`,
  `instCompScheme`, and `instIsMultiplicativeScheme`; these cover individual
  clauses, with no declaration for their conjunction and the field projection.
- `msearch.py loogle`: "AlgebraicGeometry.IsProper.isStableUnderBaseChange,
  AlgebraicGeometry.IsProper.stableUnderComposition": zero hits.
- `msearch.py grep`: `isStableUnderBaseChange|stableUnderComposition|pullback.snd`
  in `AlgebraicGeometry/Morphisms/Proper.lean`: three matching lines (58, 72,
  83), all inspected in the full source. The search wrapper mislabels the
  line number as a filename when searching a single file.
- `msearch.py leansearch`: "proper morphisms of schemes are stable under
  base change and composition": service unavailable, Internal Server Error.
- Direct `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `lem-kun-proper-stability`, proper stability names and base-change stability:
  no matching theorem, only unrelated text hits. Direct `rg` for
  `proper_stability` in Mathlib and the upstream name index also found none.
The combined statement is therefore new, while each notion is reused.

Server validation: `scompile.py NZ lem-kun-proper-stability` compiled the
single delivered file cleanly in 1.3 seconds, nice 19, two threads, limit
60 seconds. No node faults or disputed statements were found. No new nodes
or dependency modules are needed. Only the item's `lean` field changes.

## Second reading by NZ

I independently read the item node, its blueprint source (order 1709), all
three statement-dependency nodes, Mathlib's Proper module and the definitions
of the two morphism-property stability classes. I also read Stacks
`morphisms.tex`, the properness definition and Lemmas 01W3 and 01W4. Those
lemmas concern arbitrary schemes; neither imposes a Noetherian, finiteness
of the base, separatedness of the base, or field-characteristic hypothesis.

Object, hypothesis and conclusion checklist:

- Proper morphisms of schemes: `@IsProper.{u}` on `Scheme.{u}` in both
  stability conjuncts. Verdict: exact. Mathlib's class extends `IsSeparated`,
  `UniversallyClosed`, and `LocallyOfFiniteType`; universal closedness gives
  quasi-compactness, so this is the convention node's properness notion.
- Arbitrary base change: the first conjunct is
  `MorphismProperty.IsStableUnderBaseChange (@IsProper.{u})`. Its
  `of_isPullback` field quantifies over arbitrary pullback squares and
  assumes properness only of the morphism being pulled back. Verdict: exact.
- Composition: the second conjunct is
  `MorphismProperty.IsStableUnderComposition (@IsProper.{u})`. Its
  `comp_mem` field takes arbitrary composable morphisms and properness of
  both, concluding properness of their composite. Verdict: exact.
- Base field: `(k : Type u) [Field k]` universally quantifies the field in
  the final clause. Verdict: exact; there is no perfectness, algebraic
  closedness, or characteristic assumption.
- Schemes and structure maps: `(X Y : Scheme.{u})`,
  `f : X ⟶ Spec (CommRingCat.of k)` and
  `g : Y ⟶ Spec (CommRingCat.of k)` give precisely the two k-schemes.
  The explicit maps are appropriate because the node names f and involves
  its base change. Verdict: exact.
- Properness hypothesis: `IsProper f →` supplies precisely properness of
  X over k; g has no property hypothesis. Verdict: exact.
- Projection conclusion: `IsProper (pullback.snd f g)` asserts properness
  of the morphism from `X ×_k Y` to Y. The chosen pullback is the fibre
  product over the displayed Spec, and snd has target Y. Verdict: exact.
- Quantifiers and conjunctions: the two global stability assertions precede
  the universally quantified field projection clause; no hypothesis of the
  field clause restricts the global assertions. Verdict: exact.

Dependency verification: the base-change dependency's Mathlib match is the
instance `(f : X ⟶ S) (g : Y ⟶ S) [IsProper f] :
IsProper (Limits.pullback.snd f g)` at Proper.lean:83. The composition
match is `[IsProper f] [IsProper g] : IsProper (f ≫ g)` at line 67.
Their general stability declarations are at lines 72 and 58 respectively.
All are supplied by the public import used for the statement. The scheme
conventions dependency explicitly collects existing notions and has no
separate module. There is no unusable dependency, new definition node,
dependency module, private copy, or statement correction to review.

Edge cases: empty X and empty Y are allowed; identities and arbitrary
pullbacks are allowed; positive characteristic and characteristic zero are
allowed. No index set, integer n, or additive zero object occurs. The
universe u is explicitly bound and arbitrary, with schemes and the field
in the same universe as Mathlib's Spec and pullbacks. There is no smaller
independent universe of test objects. No extra instance restricts any case.

Independent searches, using wording different from the worker's:

- LeanFinder: "Universally closed separated finite type scheme maps:
  stability under pullbacks and composites" returned eight hits, including
  the individual universally-closed stability declarations, not the full
  properness conjunction.
- Loogle: `"IsProper"` returned twelve name hits, primarily proper-star and
  topological proper-map declarations, not the scheme statement.
- LeanSearch: "Proper maps of schemes remain proper after taking a fiber
  product or composing two maps" was unavailable (Internal Server Error).
- The grep wrapper for `stableUnderComposition|isStableUnderBaseChange|
  pullback.snd` in AlgebraicGeometry/Morphisms/Proper.lean found the three
  individual declarations at lines 58, 72, and 83; I read their signatures.
- Direct rg searches of Mathlib algebraic geometry, upstream
  WeilConjectures, and project lean/Sheaf for `proper_stability`,
  `ProperStability`, stability names, proper/base-change/composition wording,
  and properness conjunctions found no exact full statement. The upstream
  Proper module's image-factorization conjunction concerns different maps.
  Existing individual clauses do not state this node's full conjunction.

No mathematical or Lean mismatch was found; no module or node field was
changed. The module has one named theorem with a sorry proof and no data
definitions or auxiliary proofs. Its docstrings give the source and
blueprint identifier and reproduce the node's proof: use both stability
lemmas, then base change f along g and identify the result with pr₂.
All Lean lines satisfy the 100-character convention. The node's
lean.statement is verbatim the declaration signature in the file, and all
variables and universes are explicitly bound. Only this second-reading
report was added.

Second-reader validation: scompile.py compiled the sole delivered module
cleanly on the server in 1.3 seconds, nice 19, two threads, 60-second
per-file limit. Signature equality and the Lean line widths were checked.
