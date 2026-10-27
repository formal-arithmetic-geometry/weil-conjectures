## Worker report

The module `Sheaf.AlgebraicGeometry.FreeFiniteSpaceQuotientSeparated` states
`AlgebraicGeometry.AlgebraicSpace.free_finite_space_quotient_separated`, with exactly
one postponed theorem and no new definitions. The node text is unchanged.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`; a scheme over it is `W : Over S`.
  `Scheme` and its morphisms are the recorded Mathlib declarations in
  `Mathlib.AlgebraicGeometry.Scheme`. Universes `u v` are explicit; the finite
  group may live in a different universe from the schemes.
- Absolute separatedness of W is `[W.left.IsSeparated]`, Mathlib's closed
  diagonal condition over the terminal scheme (Spec Z), not a relative condition
  on `W.hom`. See `Scheme.isSeparated_iff_isClosedImmersion_prod_lift`.
- The finite abstract group and its action over S are `(G : Type v) [Group G]
  [Finite G] (a : G →* Aut W)`. An automorphism of the object W in Over S is
  precisely an automorphism of its underlying scheme compatible with W -> S.
- The action relation is `∐ fun _ : G ↦ W` in Over S. Its action map is
  `Sigma.desc (fun g : G ↦ (a g).hom)` and its projection is
  `Sigma.desc (fun _ : G ↦ 𝟙 W)`. The displayed `Mono (prod.lift ... ...)`
  states exactly injectivity of the relation on every scheme test. This
  coproduct is canonically G_S x_S W. Sections are locally constant labels,
  including labels varying across components; they are not just elements of G.
- `(Q : AlgebraicSpace S)` supplies the fppf sheaf and the assumed algebraicity.
  The presheaf coequalizer of the two Yoneda relation maps is the orbit
  presheaf on all scheme tests. The map `η` and hypothesis `hη` say that
  precomposition with η bijects maps from Q to each fppf sheaf with maps from
  this presheaf to that sheaf. This is exactly the sheafification universal
  property of def-weil-pbc-sheafification, also used by the recorded
  `etale_relation_quotient`; it requires no extra hypothesis that a globally
  small-valued sheafification functor exists on this large site.
- The first conjunct quantifies over ALL scheme pairs U,V over S and maps b,c
  into Q. Its witnesses P,p,q represent U x_Q V by `IsPullback` of Yoneda maps.
  `IsClosedImmersion (prod.lift p.left q.left)` tests the map into the product
  of the UNDERLYING schemes. That product is in Scheme, hence over Spec Z;
  it is not the product in Over S. This is the scheme-pair characterization
  of the closed absolute diagonal (Stacks Properties of Spaces, Tag 0AHS).
  It includes the affine-pair criterion as a special case and follows from
  the full diagonal condition by base change. Conversely an arbitrary test
  T -> Q_abs x Q_abs gives two S-structures on T and hence two objects U,V
  with underlying scheme T and maps to Q. Pull back the pair-test closed
  immersion P -> T x T along the diagonal T -> T x T: it represents the
  desired equality locus. Base change of a closed immersion is closed,
  regardless of whether T is separated. Thus this is the full condition
  for the exact sigma-formula extension in the node, not a weakening.
- The second conjunct is the dependency's exact
  `IsSeparatedPresheafMap (terminal.from Q.obj.obj)`. The terminal presheaf
  on Over S is h_S, so this is separatedness of Q -> S, with its presheaf
  diagonal representable by closed immersions on every S-scheme test.
- No affine-orbit, Noetherian, quasi-compactness, base-separatedness or
  prime-to-characteristic hypothesis occurs. Taking S = Spec Z gives the
  stated absolute case without changing the signature.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`;
  the size convention is realized by explicit universes, not a duplicate object.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `Scheme.IsSeparated`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, with `.over S` for the site's slice.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`. Their adjunction's universal
  property is written at the particular orbit presheaf, as in the existing
  quotient dependency, rather than imposing `HasWeakSheafify` on the entire site.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`; the representable pullback-square
  condition in the conclusion is this existing scheme-test notion.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicSpace.diagonalPresheafMap`, `IsSeparatedPresheafMap`.
- Recorded proof dependencies are imported without `public`:
  `Sheaf.AlgebraicGeometry.EtaleRelationQuotient` (`etale_relation_quotient`),
  `Sheaf.AlgebraicGeometry.SpaceChangeBase` (`exists_spaceChangeBase`), and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`.
  Mathlib's closed-immersion base-change and target-locality matches are
  available through the geometric imports. The unrecorded proof dependency
  lem-trf-space-closed-immersion-cover-descent has no module to import.

Sources checked: local `literature/stacks-project/spaces.tex`,
lemma-quotient (02Z2), lemma-quotient-finite-separated (02Z4(2)), and
lemma-change-base-scheme (03I4); `spaces-properties.tex`,
lemma-characterize-separated (0AHS). These justify the exact action relation,
sheafification, absolute interpretation and equivalent scheme-pair test.

Edge cases checked before writing: W empty (all relation summands empty and
its quotient empty), trivial group (the relation and quotient reduce to W),
disconnected tests (the scheme coproduct permits locally varying labels),
nonseparated S (absolute product and absolute W condition retained), and
characteristic dividing |G| (no invertibility used). A group is necessarily
nonempty, so no artificial empty-group case is introduced. Finite G in
universe v imposes no equality with u. No statement dispute or correction.

Searches made using the prescribed wrappers and source search:

- LeanFinder: “The quotient algebraic space of an absolutely separated scheme
  by a free finite constant group action is absolutely separated”: 8 hits,
  all scheme separatedness/finite morphism facts, no quotient-space theorem.
- LeanSearch: “A separated scheme modulo a free action of a finite constant
  group is a separated algebraic space”: 8 scheme-separatedness hits,
  no exact theorem.
- Loogle: `"IsSeparated", "quotient"`: 0 hits.
- Mathlib grep: `(quotient|Quotient).*(separated|Separated)|AlgebraicSpace`
  in AlgebraicGeometry: 0 hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for action/quotient,
  `orbitPresheaf`, constant groups and absolute separation: no exact theorem.
  `AdmissibleFreeFiniteQuotient` requires affine orbit neighborhoods and
  produces a scheme quotient, so it is not this statement. Its relation
  helpers are for absolute schemes, while our maps are directly the canonical
  coproduct maps in Over S; no helper or notion is copied.
  `AlgebraicSpaceUCSurjectionSeparation` uses the same absolute pair criterion,
  but states descent under a different hypothesis, not this quotient result.
  `grep -rn` for this node id in `lean/WeilConjectures` returned no match;
  proposed declaration-name search also returned no match.

## Second reading by Q21

Author's second reading under the dispatcher's no-subagents instruction;
independent review is performed by the maintainer. I reopened the node and the
finished declaration and checked: W is absolutely separated, action maps are
in Over S, the freeness monomorphism is of the full scheme coproduct relation,
Q is the specified orbit sheafification, and BOTH absolute and relative
conclusions are present. In particular `prod.lift p.left q.left` is in Scheme,
whereas the freeness `prod.lift` is in Over S. The absolute pair condition
allows different S-structures on U and V; restricting to pairs with a common
S-structure would have lost tests and was not done. No mismatch required a
node change. No new nodes or dependency repairs are needed.

Validation: the prescribed `scompile.py Q21
lem-sfb-free-finite-space-quotient-separated <module>` completed successfully
for both the sandbox probe and the actual library module path, with no compiler
errors or warnings. Every delivered line is at most 100 characters. The only
node field changed is `lean`, whose statement is extracted verbatim from the
source declaration signature. Every theorem proof is exactly `by sorry`.
