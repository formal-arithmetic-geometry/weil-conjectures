## Worker report

The module `Sheaf.AlgebraicGeometry.OpenSectionClopen` states
`AlgebraicGeometry.open_section_clopen`, with one `sorry` and no definitions.
The statement is unchanged from the node. Read the original blueprint node in
sec-smooth-purity/sk-def-sf-operations and Stacks schemes.tex,
lemma-section-immersion (Tag 01KT), including its separated-section assertion.

Hypotheses and clauses, individually:

- Arbitrary schemes V and S: `{V S : Scheme.{u}}`, with explicit universe `u`.
- The separated morphism p: `(p : V ⟶ S) [IsSeparated p]`.
- The open immersion s: `(s : S ⟶ V) [IsOpenImmersion s]`.
- The section identity p composed with s: `(hs : s ≫ p = 𝟙 S)`.
- Its image is open and closed in V: `IsClopen (Set.range s)`.
- Its complement is an open subscheme: `∃ W : V.Opens`, with
  `(W : Set V) = (Set.range s)ᶜ`. The standard `W.toScheme` carries the
  restricted structure sheaf and `W.ι` is its inclusion.
- The decomposition is a scheme disjoint union into these open subschemes:
  `Nonempty (IsColimit (BinaryCofan.mk s W.ι))`. The vertex is V and the
  legs are exactly s and the complementary inclusion; this is the universal
  property of their scheme coproduct. The given open immersion identifies S
  with its image open subscheme, so using S as the first summand expresses
  precisely the stated image decomposition, including its inclusion into V.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  and its recorded separatedness notion `AlgebraicGeometry.IsSeparated`
  (defined in Morphisms.Separated as closedness of the diagonal).
  Properness itself is not assumed: this dependency also carries separatedness.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  the underlying locally ringed space open immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding with surjective stalk maps.
- The recorded proof dependency `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsClosedImmersion.of_comp`, cancellation of a separated
  postcomposition from a closed immersion composite. Its module is imported
  without `public` for the proof plan.
- `Mathlib.AlgebraicGeometry.Limits` supplies the scheme coproduct framework.
  Read `nonempty_isColimit_binaryCofanMk_of_isCompl`: complementary open
  immersions give exactly this binary cofan colimit.

Edge cases: no nonempty, affine, finite type, proper, or Noetherian assumptions.
If S is empty, its image is empty and W is all of V. If V is empty, S is
empty too and both summands are empty. If s is an isomorphism, W is empty.
Each is allowed by the statement and by the coproduct universal property.
The universe is shared by the two arbitrary schemes, as in Mathlib's category.
No node fault or disputed statement was found.

Searches actually run through msearch.py:

- LeanFinder: "An open immersion section of a separated scheme morphism has
  clopen image and gives a coproduct decomposition into complementary open
  subschemes". Eight hits, chiefly `isCompl_opensRange_inl_inr`,
  `nonempty_isColimit_binaryCofanMk_of_isCompl`, and coproduct inclusions.
  None states this full section theorem.
- Loogle: `AlgebraicGeometry.IsSeparated, AlgebraicGeometry.IsClosedImmersion`.
  Nine hits including `IsClosedImmersion.of_comp` and diagonal properties;
  no full statement including the complementary open decomposition.
- Mathlib grep: `isClopen_range|nonempty_isColimit_binaryCofanMk_of_isCompl`
  in AlgebraicGeometry. Three hits: the complementary-open colimit lemma,
  its use in Limits, and its use in ZariskisMainTheorem.
- LeanSearch: "An open section of a separated morphism of schemes has clopen
  image and is a coproduct summand". Service unavailable, Internal Server Error.
- Direct rg on WeilConjectures and project lean/Sheaf for open-section terms,
  `isClopen_range` and `nonempty_isColimit_binaryCofanMk_of_isCompl` found
  compactification clopen-image facts and uses of complementary-open coproducts,
  but no exact statement. Upstream `Scheme.Hom.isClopen_range` assumes an
  open immersion is universally closed and does not state this section theorem
  or its decomposition clause.
- Direct grep for this node id in upstream WeilConjectures found nothing.
- Direct rg for `open_section_clopen|openSectionClopen` in Mathlib,
  WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json found
  no declaration with the proposed name.

Validation: scompile.py compiled the delivered module cleanly on the server
(nice 19, two threads, 60 seconds per file); no local compiler was run.

## Second reading by NJ

Read the sandbox node and Lean module independently against the original blueprint
sec-smooth-purity/sk-def-sf-operations/lem-weil-pbc-open-section-clopen.md and
Stacks schemes.tex, lemma-section-immersion (Tag 01KT). The Stacks lemma assumes
only a scheme morphism and its section; separatedness gives the closed immersion.
It imposes no standing Noetherian, finite type, properness, or field hypothesis.
The blueprint then adds openness and the complementary-open decomposition.

Object/hypothesis/conclusion checklist (all pass):

- Schemes V and S: `{V S : Scheme.{u}}` introduces arbitrary schemes in an
  arbitrary explicit universe. No additional structure on either scheme.
- Morphism p from V to S: `(p : V ⟶ S)`; `[IsSeparated p]` is exactly the
  separatedness hypothesis, not properness or absolute separatedness of V.
- Morphism s from S to V: `(s : S ⟶ V)`; `[IsOpenImmersion s]` identifies S
  with its image open subscheme, with its restricted structure sheaf.
- Section equation: `(hs : s ≫ p = 𝟙 S)` is precisely p composed with s equals
  the identity of S, with the correct composition order.
- Image open and closed in V: `IsClopen (Set.range s)` uses the underlying
  point map of this same scheme morphism, with both clauses of clopenness.
- Complement as an open subscheme: `∃ W : V.Opens` followed by
  `(W : Set V) = (Set.range s)ᶜ` identifies exactly the complement. `W.ι` is
  the canonical inclusion of the standard restriction scheme `W.toScheme`.
- Scheme disjoint-union decomposition: `Nonempty (IsColimit (BinaryCofan.mk
  s W.ι))` says these very inclusions exhibit V as the scheme coproduct of S
  and the complementary open subscheme. Because s is an open immersion onto
  its image, this is exactly the blueprint decomposition, including structure
  sheaves, and adds no extra choice of decomposition or compatibility condition.
  W is quantified after the given p, s, and section equation, as required.

Dependency signatures checked directly in their recorded Mathlib modules:
`def-weil-proper-morphism` explicitly records `IsSeparated` alongside `IsProper`;
Separated.lean defines it by closed immersion of `pullback.diagonal p`.
`def-weil-open-immersion` records `IsOpenImmersion`, the underlying locally ringed
space open immersion (OpenImmersion.lean). `def-weil-closed-immersion` records
`IsClosedImmersion`, closed embedding plus surjectivity on stalks
(ClosedImmersion.lean). The proof dependency
`lem-weil-pbc-closed-immersion-from-composite` records
`IsClosedImmersion.of_comp` in Separated.lean: closed immersion of `f ≫ g` and
separatedness of g imply closed immersion of f. It has exactly the required
hypotheses with f=s and g=p. No dependency repair, private notion, new definition
node, or sibling module is needed. Limits.lean's
`nonempty_isColimit_binaryCofanMk_of_isCompl` corroborates the encoding of the
scheme decomposition using complementary open immersions.

Edge cases: S empty allows empty image and W=V; V empty forces S empty. If s is
an isomorphism, W is empty. No nonemptiness assumption excludes any of these.
There is no index set, coefficient ring, characteristic, or integer n in this
statement, so empty-index, zero-object, characteristic and n=0 restrictions do
not arise. The explicit arbitrary universe u is the ordinary Mathlib category
of schemes and introduces no bound on scheme size. Every variable is bound.

Independent searches, using different wording from the first worker:

- LeanFinder through msearch.py: "A section of a separated scheme map which is
  an open embedding identifies the scheme with the coproduct of the section
  and its open complement". Eight hits, including open coproduct inclusions,
  `nonempty_isColimit_binaryCofanMk_of_isCompl` and complementary coproduct
  ranges; no exact full statement.
- Loogle through msearch.py: `"IsClosedImmersion.of_comp"`. Two hits: the
  separated-postcomposition cancellation and its closed-postcomposition
  specialization. Read the former's complete signature in Separated.lean.
- LeanSearch through msearch.py: "An open embedding section of a separated
  scheme morphism has clopen image and an open complement coproduct
  decomposition". Service unavailable (Internal Server Error), not a negative
  search result.
- Direct rg in Mathlib AlgebraicGeometry, upstream WeilConjectures, project
  lean/Sheaf and dag/lean_names_upstream.json for `isClopen_range`,
  `open_section_clopen`, `openSectionClopen`, and the complementary-open colimit
  lemma; also searched section/closed and complementary/open wording in both
  project source trees. No duplicate full theorem. Opened upstream
  `Scheme.Hom.isClopen_range`: it requires `[IsOpenImmersion f]` and
  `[UniversallyClosed f]`, and concludes only clopenness. Compactification's
  specialized clopen-image theorem likewise does not state this section theorem
  and decomposition. Neither is an exact existing match.

No mathematical or record mismatch found, and no Lean or node text changed.
The module has one named theorem with whole proof `sorry`, no definitions or
proved helpers. Its module and theorem docstrings cite the source and node;
the theorem docstring contains both proof steps (closed section by cancellation,
then disjoint open cover and sheaf gluing). Imports, namespace, line lengths and
explicit universe satisfy the conventions. The node's `lean.statement` is
verbatim the file signature. No statement correction or citer review applies.

Second-reader validation: scompile.py compiled the sole delivered file on the
server cleanly in 1.3 seconds, nice 19, two threads, 60 seconds per file. No
warnings or errors were emitted; no local compiler or library build was run.
