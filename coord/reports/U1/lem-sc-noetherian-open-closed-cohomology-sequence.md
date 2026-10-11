## Worker report

The module `Sheaf.Topology.NoetherianOpenClosedCohomologySequence` states
`TopCat.noetherian_open_closed_cohomology_sequence`. Its sole theorem has proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The existing landed node `def-weil-pbc-site-extension-by-zero-presheaf` is added to
`stmt_deps`, as allowed for landed definitions by brief-stage2 §5.

Hypothesis and clause correspondence:

- A Noetherian topological space: `(X : TopCat.{u}) [NoetherianSpace X]`.
  Mathlib defines Noetherianity by well-founded strict reverse inclusion on opens;
  complements identify this with well-founded strict inclusion on closed subsets,
  equivalently the node's minimal-element condition. No separation assumption is added.
- The open inclusion is specified by `(U : Opens X)`. The closed complement is exactly
  `TopCat.of ↥((U : Set X)ᶜ)` with its subspace topology and the continuous subtype
  inclusion `TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩`.
- The abelian sheaf is `(F : TopCat.Sheaf AddCommGrpCat.{u} X)`.
- `j^*F` is `F.over U`, the existing restriction to the slice of opens over `U`.
  Objects of this slice are precisely opens `V` of `X` contained in `U`, and its
  value there is `F(V)`; Mathlib's `Opens.overEquivalence` and `sheafEquivOver`
  identify this site and restriction with those on the topological subspace `U`.
- `j_!j^*F` is `presheafToSheaf ... |>.obj
  ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)` (written without a pipe in
  the signature). This reuses the general slice-site definition, rather than
  defining a second topological extension by zero. At `V`, its presheaf has
  the direct sum of `F(V)` over `φ : V ⟶ U`. There is exactly one such `φ`
  if `V ≤ U`, and none otherwise, giving the node's presheaf formula.
- The first morphism `a` is specified by its action on every direct-sum generator
  after `toSheafify`: the displayed equation sends each section `s` to itself.
  This specifies the canonical map uniquely, by direct-sum and sheafification
  universal properties. At opens not contained in `U`, the presheaf map is zero.
  Existential quantification here constructs this map; it is not an unconstrained
  map hypothesis. The generator formula is essential to specifying the map.
- `F → i_*i^*F` is exactly the unit of
  `TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat` for the closed
  complement inclusion. The inverse image is the recorded Mathlib pullback, with
  the unit of that same adjunction (no mismatch between two choices of pullback).
- The short exact sequence is the second conjunct:
  `∃ h : a ≫ unit.app F = 0, (ShortComplex.mk a (unit.app F) h).ShortExact`.
  `ShortExact` asserts the first arrow is mono, the complex is exact, and the
  second arrow is epi. Thus both endpoint zeros and exactness are present.
- The closure-support assertion is `∃ F' : TopCat.Sheaf ...
  (TopCat.of ↥(closure (U : Set X))), Nonempty (j_!j^*F ≅ i'_*F')`.
  The map `i'` is the subtype inclusion of the actual topological closure.
  Existence of an isomorphism is exactly the assertion that the sheaf is a
  closed direct image, without a new support assumption.
- Cohomology on the closed subspace is the final `∀ p : ℕ, Nonempty (...)`.
  It compares `H'(F',p,⊤)` on the closure to `H'(j_!j^*F,p,⊤)` on `X`, using
  `HasExt.standard` exactly as the recorded closed-immersion comparison does.
  Nonnegative integers are indexed by naturals; degree zero is included.

Dependencies read and used:

- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
  `CategoryTheory.Sheaf.H'`: the recorded abelian-sheaf cohomology on the terminal open.
- `Sheaf.Topology.ClosedImmersionPushforwardCohomology`,
  `TopCat.cohomology_closed_immersion_pushforward`: the existing comparison and its
  `HasExt.standard` convention; invoked in the natural-language proof's final step.
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf`,
  `CategoryTheory.siteExtensionByZeroPresheaf`, `siteExtensionByZeroSection`:
  the additional landed definition used directly in the signature.
- Mathlib `Sheaf.over`, `presheafToSheaf`, `toSheafify`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`, and `TopCat.Sheaf.pushforward`
  supply restriction, sheafification, the closed unit, and direct image.

The docstring carries all five DAG proof steps: stalk calculations on the open
and its complement; stalkwise short exactness; the closure-support isomorphism;
closed-pushforward cohomology and transport. Proof dependency declarations are
not imported merely to leave proofs as `sorry`.

Edge cases checked before writing: `X` empty; `U = ⊥` (extension by zero and its
closure sheaf are zero, closed unit is an isomorphism); `U = ⊤` (first map is an
isomorphism, complement empty); `F = 0`; `p = 0`; non-Hausdorff spaces. None is
excluded. The statement follows the dependencies' single universe convention
`TopCat.{u}` / `AddCommGrpCat.{u}` / `HasExt.standard`; increasing `u` accommodates
arbitrary-sized spaces and sheaves. No finite, connected, or separated condition
is present, and Noetherianity is retained even though the local sequence does not
need it.

Searches performed (msearch.py, group U1 and this item):

- leanfinder: `short exact sequence abelian sheaf open subset extension by zero
  closed complement` returned 8 hits: MayerVietorisSquare shortComplex and
  shortExact concern an open cover, not a complementary open/closed decomposition.
- loogle: `TopCat.Sheaf, kernel` returned no hits (unknown identifier `kernel`).
- grep: `extensionByZero|extendByZero|openClosedShortComplex` in
  `Topology/Sheaves` returned no hits.
- leansearch: `extension by zero abelian sheaf topological open embedding left
  Kan extension` was unavailable, Internal Server Error.
- rg across project and upstream: `extensionByZero|extendByZero|lowerShriek`.
  Upstream hits are étale/pro-étale/Weil sheaves, not topological abelian sheaves.
  Project hits include module extension by zero and, crucially, the general
  abelian slice-site construction in `SiteExtensionByZeroPresheaf.lean`, reused here.
- `tools/blueprint_refs.py search 'extension by zero'` and searching DAG definition
  nodes confirmed the general slice-site node and the distinct étale/module nodes.
- rg for the item id in upstream had no hit. rg for
  `noetherian_open_closed_cohomology_sequence` in upstream and project had no hit.

Source text was read at https://stacks.math.columbia.edu/tag/02UT and
https://stacks.math.columbia.edu/tag/02UZ because the literature checkout is
absent on this machine. Both agree with the node: adjunction maps give the
sequence, and extension by zero is a closed pushforward from the closure.
No node fault or STATEMENT-DISPUTED flag.

Local compile: clean, 2.6 seconds. Server compile and preflight are checked by
`deliver2.py --no-push` before READY. Independent second reading remains for the
next worker; no second-reading claim is made here.

## Second reading by U1

I reread the node statement, its Stacks source (Cohomology Lemmas 02UT and 02UV and
Proposition 02UZ), the dependency declarations, and the Lean theorem. The objects and
hypotheses correspond as follows: `X : TopCat.{u}` with `[NoetherianSpace X]` renders a
Noetherian space (Mathlib's `WellFoundedGT (Opens X)`, equivalent to minimal closed
subsets); `U : Opens X` renders the open inclusion `j`; the subtype inclusion of
`((U : Set X)ᶜ)` renders the closed complement `i`; and
`F : TopCat.Sheaf AddCommGrpCat.{u} X` renders an abelian sheaf. The sheaf
`presheafToSheaf ... ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)` is the
sectionwise direct-sum/sheafification realization of `j_!j^*F`, using the recorded
`def-weil-pbc-site-extension-by-zero-presheaf` declaration. The existential `a` and its
`DirectSum.of` generator equation render the canonical map `j_!j^*F → F`; the equation
covers every summand and the empty-summand case is forced by the zero direct sum. The
existential `h` and `ShortComplex.mk ... .ShortExact` render the short exact sequence,
including the zero composite, monomorphism, exactness, and epimorphism. The existential
`F'` on `closure (U : Set X)` and the displayed `Nonempty` isomorphism render that
`j_!j^*F` is a closed direct image from the closure. The final `∀ p : ℕ, Nonempty`
isomorphism of `Sheaf.H'` values on `⊤`, with `HasExt.standard`, renders cohomology
computed on that closed subspace, including degree zero.

No extra separated, finite, connected, Hausdorff, or characteristic hypothesis appears;
the sole class hypothesis is the node's Noetherianity. Universes are shared throughout
(`TopCat.{u}`, `AddCommGrpCat.{u}`), so no case is excluded. Edge cases checked were
`X = ∅`, `U = ⊥` and `U = ⊤`, zero `F`, empty complement/closure, and `p = 0`; the
signature remains meaningful in each case. The complement and closure are represented by
subtype spaces, including non-Hausdorff spaces.

The searches were reread from the worker record and repeated with `rg` in Mathlib and
`WeilConjectures/`; no existing open-closed sequence declaration was found. The only
relevant project construction is `CategoryTheory.siteExtensionByZeroPresheaf`, whose
landed definition node is now cited in `stmt_deps`; no duplicate definition was added.
The theorem compiles cleanly with `lcompile.py`. I found one delivery-record mismatch:
the worker report said this landed definition had been added, but the repository copy of
the node lacked it. The sandbox node was corrected to include
`def-weil-pbc-site-extension-by-zero-presheaf`; no Lean source change was needed.
