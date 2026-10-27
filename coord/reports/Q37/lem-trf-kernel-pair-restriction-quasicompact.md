## Worker report

The module `Sheaf.CategoryTheory.Sites.KernelPairRestrictionQuasicompact` states
`CategoryTheory.kernelPair_restriction_quasiCompact`, with its whole proof `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
The module and theorem docstrings cite Stacks Tag 00W2 and carry the full four-step
proof plan of this node. The mathematical statement is unchanged.

Hypotheses and objects, clause by clause:

- The topos is `{E : Type u} [Category.{v} E]` with
  `hE : IsGrothendieckTopos.{w} E`. This is the existing definition of a category
  equivalent to `Type w`-valued sheaves on a site with objects and arrows in `w`.
  Thus it includes arbitrary small-site presentations, rather than requiring a
  coherent presentation. Universes `w u v` are explicitly declared. The size node
  is a metatheoretic convention, so it has no module to import.
- `[HasCoproducts.{w} E] [HasFiniteLimits E]` expose the existing categorical
  structures needed to use the dependency's quasi-compactness predicates and
  Mathlib's chosen pullbacks. They are structures every such topos has, not extra
  geometric hypotheses. No universe equality is imposed.
- `{P A : E} (p : P ⟶ A)` is arbitrary, without an epimorphism instance.
  `pullback p p` is R, `pullback.fst p p` is r1, and `pullback.snd p p` is r2.
- `hP : IsQuasiSeparatedObject.{w} P` and
  `hR : IsQuasiCompactObject.{w} (pullback p p)` are precisely the two finiteness
  assumptions. There is no assumption of quasi-compactness of P, or of coherence
  of E or its terminal object.
- The family binds every `K L : E`, `k : K ⟶ P`, `l : L ⟶ P`, and proofs of
  `IsQuasiCompactObject.{w} K` and `IsQuasiCompactObject.{w} L`.
  `pullback k (pullback.fst p p)` is T and its `pullback.snd` is t_R.
- `e K L k l hK hL` has source `pullback (k ≫ p) (l ≫ p)` and target
  `pullback (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l`,
  exactly the displayed isomorphism. The existential family is canonically
  characterized by its projection equations; it does not choose an unspecified
  comparison map or define data by a postponed existence proof.
- Conjuncts 1 and 2 give the forward K- and L-projection equations. Conjuncts
  3 and 4 give the two R coordinates as `pullback.fst ... ≫ k` and
  `pullback.snd ... ≫ l`. Since T and R are pullbacks, these equations uniquely
  characterize the forward arrow. In a site presentation Tag 00W2 computes
  limits sectionwise; evaluating the four equations gives exactly
  `(x,y) ↦ (x,(k(x),l(y)),y)`. This formulation works for any choices of the
  categorical pullbacks, including Mathlib's chosen limits.
- Conjuncts 5 and 6 give the inverse K- and L-projection equations. Since the
  left object is the pullback over A, these characterize the inverse as the
  map forgetting the R component, hence imply the literal site-section formula.
- Conjuncts 7 and 8 state quasi-compactness of T and of `pullback (k ≫ p) (l ≫ p)`.
- The final conjunct quantifies all quasi-compact `K' L'`, maps `k' l'` to P,
  maps `a : K' ⟶ K`, `b : L' ⟶ L`, and the equations
  `ha : a ≫ k = k'`, `hb : b ≫ l = l'`. Its equality is the naturality square
  for the same family e. The left pullback map is `pullback.map` over `𝟙 A`.
  On the right the inner pullback map uses a and `𝟙 R`, and the outer one uses
  that map and b over `𝟙 P`. Thus the R coordinate is preserved as required.
  The inline `simp` proofs merely type these standard maps using ha and hb;
  the theorem itself is entirely postponed. Naturality of inverses follows
  equivalently by composing this identity with the inverses of the isomorphisms.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.CoherentToposRepair`, the recorded module of
  `def-trf-coherent-topos`, publicly imports
  `Sheaf.CategoryTheory.Sites.CoherentTopos`. From the latter the statement uses
  `CategoryTheory.IsQuasiCompactObject` and `CategoryTheory.IsQuasiSeparatedObject`.
  Their full docstrings and signatures were read: finite subfamilies of epimorphic
  coproducts, and quasi-compactness of arbitrary pullback cones of quasi-compact
  objects, respectively. The same dependency imports
  `Sheaf.CategoryTheory.Sites.GrothendieckTopos`, whose
  `CategoryTheory.IsGrothendieckTopos` gives the small-site presentation.
  The repair's coherent-topos predicate is not an assumption of this theorem.
- `def-weil-size-convention` is recorded as `convention: true` with no declaration;
  explicit universes and `IsGrothendieckTopos.{w}` implement it.
- The proof dependency `lem-weil-pbc-site-sheaf-sets-limits-sectionwise` is a
  Mathlib leaf: `CategoryTheory.Sheaf.createsLimitsOfShape`,
  `Mathlib.CategoryTheory.Sites.Limits`. Its signature, surrounding hypotheses,
  and `Sheaf.isSheaf_of_isLimit` were read. That module is a non-public proof
  import. The source `literature/stacks-project/sites.tex`, lemma-limit-sheaf
  (Tag 00W2), was read, including the proof that presheaf limits are sheaves.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting` supplies the standard
  pullback API. Its `pullbackRightPullbackFstIso` and
  `pullbackLeftPullbackSndIso` were read. The construction and naturality use
  Mathlib's `pullback`, `pullback.fst`, `pullback.snd`, and `pullback.map`.

Edge cases checked: P, K or L may be initial; section sets and finite covering
subfamilies may be empty. No nonemptiness binder is present. The degenerate
case p = identity and arbitrary non-epimorphic p are included. P need not be
quasi-compact; only its quasi-separatedness is used, twice. No condition on A
or on the terminal object is assumed. The family is indexed by all appropriate
objects and maps; the naturality equation also includes identities and arbitrary
composites. There is no division, coefficient condition, or nonzero restriction.

Searches, all before writing:

- `msearch.py ... leanfinder` query: "A kernel pair restricted along two maps to a
  quasi separated sheaf gives a quasi compact pullback and a canonical pullback
  isomorphism". Eight hits: scheme quasi-compactness and sheaf pullback functors;
  no statement about these quasi-compact topos objects.
- `msearch.py ... loogle` query:
  `CategoryTheory.Limits.pullbackRightPullbackFstIso`. Eleven hits, the generic
  canonical pullback pasting isomorphism and its projection equations; these are
  ingredients, not the complete node including finiteness and naturality.
- `msearch.py ... grep` query:
  `kernelPair|IsQuasiSeparated|pullbackRightPullbackFstIso`, subdirectory
  `CategoryTheory`. Twenty-five hits, generic kernel pairs and pasting; no exact
  statement. The project's predicates are absent from Mathlib.
- `msearch.py ... leansearch` query: "A quasi compact kernel pair over a quasi
  separated sheaf restricts to a quasi compact fibre product". Eight hits,
  scheme morphism finiteness and topological quasi-separatedness, not this node.
- `rg` of `kernelPair|kernel_pair|IsQuasiSeparated|IsQuasiCompact` in
  `lean/WeilConjectures` and `lean/Sheaf/CategoryTheory`, followed by targeted
  `kernelPairRestriction|kernel_pair_restriction|kernelPair_restriction_quasiCompact`
  in both source roots and `dag/lean_names_upstream.json`: no existing statement.
  The related coherent epimorphic quotient theorem has extra coherence and epi
  hypotheses and only concludes coherence of A; it is not this auxiliary.
- `rg -n lem-trf-kernel-pair-restriction-quasicompact` in both source roots:
  no declaration carrying this node. No competing notion is introduced.

Validation: each delivered module is checked separately with the prescribed
`scompile.py`; the delivery dry run repeats compilation and server preflight.
No global build, direct Git command, or edit of the shared repository is used.
There are no statement disputes or node faults.

## Second reading by Q37

Author self-check for direct delivery; independent mathematical review is the
maintainer's responsibility, as in the dispatch brief. Re-read the node alongside
the complete Lean signature. Matched the small-site presentation, all finiteness
hypotheses, both nested pullbacks, forward K/L and R coordinates, inverse K/L
coordinates, both quasi-compactness conclusions, and the naturality square.
The four forward projections uniquely specify the advertised section formula;
the inverse equations specify forgetting R. The naturality maps are the actual
Mathlib pullback maps, with identity on R and both indicated maps over P.
No source clause is omitted; no coherence, epi, nonemptiness, or quasi-compact-P
hypothesis has entered the signature. No mismatches requiring correction found.
