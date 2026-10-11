## Worker report

The module `Sheaf.CategoryTheory.DerivedCoupleExact` states all four clauses of
`lem-sp-derived-couple-exact`, without changing the node. The main theorem
`CategoryTheory.BigradedExactCouple.derived_couple_exact` states clauses 1–3;
`CategoryTheory.BigradedExactCouple.pageCouple_image` states clause 4. Both proofs
are `by sorry`. There are no new definitions, new nodes, or dependency modules.

Hypotheses and objects:

- The abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`, with both
  universes explicit and no smallness, concreteness, embedding, or coproduct assumption.
- The nonnegative integer type is `{s : ℕ}` and the given exact couple is
  `X : BigradedExactCouple C s`. Its fields `D`, `E`, `alpha`, `f`, `g` have exactly
  the prescribed bidegrees. Its three zero-composition fields express complexes,
  and its three `exact_*` fields express the three image/kernel equalities.
  Integer bidegrees are universally quantified `p q : ℤ`.
- `X.d` is `X.f ≫ X.g`. `derivedD` is the incoming alpha image, and
  `derivedDInclusion` is its canonical inclusion. `factorThruImage` is the epi
  from the source of incoming alpha; the image factorization identity is supplied
  by Mathlib. `derivedE` is the cokernel of the incoming differential lifted into
  the outgoing kernel: precisely cycles modulo boundaries. `derivedEProjection`
  is the canonical quotient projection. `gToCycles` is the kernel factorization.

Clause 1:

- `kernelSubobject (X.d p q) = (Subobject.pullback (X.f p q)).obj
  (kernelSubobject (X.g (p + 2) (q - 1)))` is the first kernel identity.
- Replacing the pulled-back kernel by `imageSubobject a` states the second
  identity. The local `a` is the incoming alpha at `(p+2,q-1)`, transported
  across the integer identities `(p+3)-1=p+2`, `(q-2)+1=q-1`. The intervening
  `kernelSubobject ... = imageSubobject a` also states the node's `ker g=im alpha`.
- The next two identities are `imageSubobject (X.d p q)` equal to the image of
  `(imageSubobject (X.f p q)).arrow ≫ X.g ...`, and to the image of
  `(kernelSubobject (X.alpha ...)).arrow ≫ X.g ...`. The further equality
  `imageSubobject (X.f p q) = kernelSubobject (X.alpha ...)` states `im f=ker alpha`.
  These compare subobjects of `E (p+2+s) (q-1-s)`. Reindexing this target to the
  node's `(p,q)` gives exactly its incoming-differential identities: the shift
  is a bijection on integer pairs, and all pairs are quantified. The image of a
  subobject under `g` is its inclusion followed by `g`, then `imageSubobject`;
  `Subobject.map` cannot be used, since Mathlib reserves it for mono maps.

Clauses 2 and 3:

- The inequality `imageSubobject (kernel.ι (X.d p q) ≫ X.f p q) ≤ imageSubobject a`
  states `f(ker d) ⊆ im alpha` explicitly.
- `gToCycles ≫ kernel.ι = g` states the kernel factorization explicitly.
- `X.d p q ≫ X.d ... = 0` states square-zero explicitly.
- `kernel.ι (factorThruImage ...) ≫ gToCycles ... ≫ derivedEProjection ... = 0`
  says that the cycle quotient composed with the lifted `g` kills the kernel
  of the incoming alpha image epimorphism.
- `∃! M : DerivedMaps X, True` supplies the three maps with their equations
  `alpha_comm`, `f_comm`, `g_comm`, all three complex relations and all three
  exactness equalities. The `DerivedMaps` hom types specify precisely type `s+1`.
  The equations are those in the node, using Lean's composition order.
  Uniqueness of this structure is uniqueness of the maps (proof fields are
  irrelevant). The equations alone force uniqueness by mono image inclusions,
  the epi cycle quotient and the epi image factorization; requiring exactness
  in the witness does not discard any alternative solution of those equations.

Clause 4:

- Given `X : BigradedExactCouple C 0`, `pageCouple n` is the type-`n` couple at
  actual page `r=n+2`; its definition gives the initial couple and recursion
  by `derived`. Natural `n` covers every integer `r≥2`, including `r=2`.
- Existential `A n p q : D (p+n) (q-n) ⟶ D p q` is fixed by the identity at zero
  and the explicit incoming-alpha composition recurrence. Thus it is exactly
  `alpha^(r-2)`, not an arbitrary family of maps.
- Existential `I n p q : (pageCouple n).D p q ⟶ D p q` is fixed by the identity
  at zero and composition of each `derivedDInclusion` with the preceding `I`.
  `Mono (I n p q)` and `imageSubobject (I n p q) = imageSubobject (A n p q)`
  give the asserted equality of subobjects in the original `D p q`.
- `(pageCouple n).alpha ≫ I = I ≫ X.alpha` says its alpha is the restriction.
- The final cokernel/kernel-lift equality is precisely the cycles/boundaries
  formula for `E_(r+1)` of the node.
- The hom types in `pageCouple n` give alpha degree `(-1,1)`, f degree `(2,-1)`,
  g degree `(n,-n)=(r-2,2-r)`; its `d` is f followed by g, with degree
  `(n+2,-n-1)=(r,1-r)`. These are encoded by the dependency's definitions,
  rather than by a redundant copy of the maps or notion of bidegree.

Dependencies read in full and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. Its finite-products/preadditive,
  kernels/cokernels and normal mono/epi signature is the node's abelian notion.
- `def-sp-exact-couple`: `CategoryTheory.BigradedExactCouple` and its namespace
  declarations in `Sheaf.CategoryTheory.ExactCouple`: `d`, `dInto`,
  `derivedD`, `derivedE`, `derivedDInclusion`, `derivedEProjection`, `gToCycles`,
  `DerivedMaps`, `derived`, `pageCouple`, and `pageDifferential`. The full file,
  including commutative equations and docstrings, was read.

Edge cases checked: type zero; zero objects and zero differentials; page two
(`A 0` and `I 0` are identities, so `D₂=D`); all negative bidegrees; unbounded
iteration; arbitrary object and hom universes. No hypothesis is lost in these
cases. Equality of subobjects is used instead of equality of chosen image
objects. The index transports are integer equalities, not extra assumptions.

Searches made:

- `msearch.py ... leanfinder "The derived couple of a bigraded exact couple is exact"`:
  eight hits for exact complexes and homology sequences, no exact-couple theorem.
- `msearch.py ... loogle "CategoryTheory.Abelian, CategoryTheory.Subobject"`:
  twelve hits, including `ShortComplex.exact_iff_image_eq_kernel` and subobject
  infrastructure, none stating this node.
- `msearch.py ... grep "ExactCouple|derivedMaps_exists|derived_couple"`: zero Mathlib hits.
- `msearch.py ... leansearch "exact couple derived couple exact bigraded"`:
  service unavailable (Internal Server Error); other searches were used.
- `rg` for `exact.couple|ExactCouple|derivedCouple|derived_couple` in Mathlib's
  Algebra/Homology tree, the source `WeilConjectures`, and `lean/Sheaf`:
  only the project's dependency module `Sheaf.CategoryTheory.ExactCouple` matched.
  `derivedMaps_exists` there states existence/exactness but not the kernel/image
  identities, uniqueness, or the iterated-power image formula: no existing
  declaration renders all clauses of this node.
- The node id has no occurrence in source `WeilConjectures`; the names
  `derived_couple_exact|pageCouple_image` are absent in `dag/lean_names_upstream.json`,
  source `WeilConjectures`, and Mathlib.

Source checked: the local `literature/stacks-project/homology.tex` is absent on
this machine, so the exact Stacks places were opened at
https://stacks.math.columbia.edu/tag/011R,
https://stacks.math.columbia.edu/tag/011S and
https://stacks.math.columbia.edu/tag/0AMJ.
The shifted formulas and well-definedness footnote agree with the node.
Stacks starts at page one; the node and its dependency deliberately use page two.
No node correction or disputed statement was needed.

Validation: server single-file compile succeeded without warnings (1.4 seconds).


## Second reading by C1

I independently read the node, both dependency nodes, the full delivered module,
and the full landed `Sheaf.CategoryTheory.ExactCouple` module. I also read
Mathlib's `Abelian` class. The mathematical statements require no repair.
The node has no statement correction, and this delivery has no new definition
nodes or dependency modules.

Source: I retrieved the Stacks `homology.tex` into the item's scratchpad and read
`section-exact-couple`, including `definition-exact-couple` (011Q),
`lemma-derived-exact-couple` (011R),
`definition-spectral-sequence-associated-exact-couple` (011S),
`lemma-spectral-sequence-associated-exact-couple` (011T), and
`remark-shifted-exact-couple` (0AMJ), including its footnote. The section assumes
an arbitrary abelian category; there is no concreteness, smallness, finite-support,
or countable-coproduct hypothesis. The bigraded dependency and node use the
blueprint's page-two convention. The source's page-one numbering translates by
one and adds no restriction.

Object/hypothesis/conclusion checklist, with the file and node open:

1. Arbitrary abelian category: `{C : Type u} [Category.{v} C] [Abelian C]`
   in both theorem signatures. The independent object/hom universes cover the
   node's categories. Mathlib's finite-products/normal-mono/normal-epi formulation
   supplies exactly the zero object, finite biproducts, kernels and cokernels of
   `def-sp-abelian`. Verdict: exact match; no additional instance.
2. Nonnegative integer type and all integer bidegrees: `{s : ℕ}` and
   `X : BigradedExactCouple C s`, with `∀ p q : ℤ`. Natural numbers represent
   exactly nonnegative integers. The dependency's `D`, `E`, `alpha`, `f`, `g`
   have the node's respective domains, targets and degrees. Its three `*_zero`
   and three `exact_*` fields give the three complexes and exactness conditions
   after bijective translations of the integer indices. Verdict: exact match.
3. Differential: `X.d p q` unfolds to `X.f p q ≫ X.g (p + 2) (q - 1)`.
   This is `g ∘ f`, with target `(p+s+2,q-s-1)`. Verdict: exact match.
4. Derived objects and canonical maps: `derivedD` is the incoming-alpha image;
   `derivedDInclusion` is its mono inclusion, transported to `D p q`.
   `factorThruImage` is its source-to-image epimorphism. `derivedE` is the
   cokernel of `kernel.lift d dInto dInto_comp_d`, hence cycles modulo incoming
   boundaries; `derivedEProjection` is the cokernel projection, and
   `gToCycles` is the canonical kernel lift. Mathlib's image factorization
   gives the node's alpha factorization equation. Verdict: exact match, using
   the recorded dependency rather than a private copy or a hollow definition.
5. Clause 1, kernel identities: the first three conjuncts in the `∀ p q`
   block state `ker d = pullback f (ker g)`, `ker d = pullback f (im alpha)`,
   and `ker g = im alpha`. The local `a` is exactly the incoming alpha into
   `D (p+2) (q-1)`, with only integer-identity transport. Verdict: exact match.
6. Clause 1, image identities: the next three conjuncts state
   `im d = im (inclusion (im f) ≫ g)`, the analogous identity with `ker alpha`,
   and `im f = ker alpha`. They are stated at the outgoing target
   `(p+2+s,q-1-s)`. To obtain the node's incoming form at `(P,Q)`, substitute
   `p=P-s-2`, `q=Q+s+1`; then the intermediate object is `D (P-s) (Q+s)`.
   This substitution is a bijection of integer pairs. Image of a subobject
   under `g` is exactly image of its inclusion composed with `g`.
   Verdict: exact match, with no mono assumption on `g`.
7. Clause 2, well-definedness: the last conjunct of the first block gives
   `imageSubobject (kernel.ι d ≫ f) ≤ imageSubobject a`, namely the cycle
   restriction of `f` lands in the incoming alpha image. The next blocks give
   `gToCycles ≫ kernel.ι = g`, `d ≫ d = 0`, and vanishing of
   `kernel.ι (factorThruImage alpha) ≫ gToCycles ≫ derivedEProjection`.
   The latter is exactly the quotient map killing the image epimorphism's
   kernel. Verdict: all four explicit requirements present.
8. Clauses 2 and 3, maps and exactness: `∃! M : DerivedMaps X, True` gives
   the three maps. I read `DerivedMaps.alpha_comm`, `f_comm`, `g_comm`:
   these are respectively the restriction, quotient descent of `f`, and
   descent of lifted `g` through the alpha image epimorphism. The hom types
   give degrees `(-1,1)`, `(2,-1)`, `(s+1,-s-1)`. Its three zero and three
   exactness fields give every derived complex and middle exactness clause.
   Bundled uniqueness is not weaker than uniqueness among all solutions of
   the commutative equations: mono cancellation forces the alpha map;
   epi projection followed by mono cancellation forces the f map; epi
   image-factorization cancellation forces the g map. Any solution therefore
   equals the existing exact solution and automatically has its exactness
   properties. Proof fields do not add choices. Verdict: exact match.
9. Clause 4, initial couple and recursion: the second theorem takes
   `X : BigradedExactCouple C 0`; the dependency's `pageCouple 0 = X` and
   `pageCouple (n+1) = (pageCouple n).derived` represent `C₂=C` and
   `C_(r+1)=C_r'`, with `n=r-2`. Its result type is a type-`n` exact couple.
   Verdict: all pages `r≥2` covered, with the specified initial couple.
10. Clause 4, original subobject and alpha powers: `A 0` is the transported
    identity and its recurrence composes the incoming alpha with the preceding
    power. Thus `A n p q : D (p+n) (q-n) ⟶ D p q` is precisely alpha to
    the n-th power. `I 0` is identity and its recurrence composes each derived
    image inclusion with the preceding inclusion. `Mono (I n p q)` and
    `imageSubobject (I n p q) = imageSubobject (A n p q)` identify the required
    subobjects of the original `D p q`. These are not unconstrained existential
    families: their base cases and recurrences determine them. Verdict: exact.
11. Clause 4, restriction, degrees and homology: the next equality is
    `(pageCouple n).alpha ≫ I = I ≫ X.alpha`. The dependency's map types
    retain f-degree `(2,-1)` and g-degree `(n,-n)` and give d-degree
    `(n+2,-n-1)=(r,1-r)`. The final equality identifies the next E-object
    with the cokernel of the incoming differential lifted into the outgoing
    kernel. Verdict: every remaining clause present, with the same objects.

Edge cases: `s=0` is admitted; `n=0` gives page two with identity A and I and
image of the identity equal to the full subobject. All negative p and q and
arbitrarily large iterations are admitted. Zero objects and zero differentials
are admitted whenever the given three exactness conditions hold; nothing requires
nonzero maps. No index family is assumed inhabited or finite; the node fixes
integer bidegrees, so an alternative empty index set is not part of its statement.
Schemes, empty schemes, field characteristic and coefficient rings do not occur
in this categorical statement. No smallness or relation between u and v is imposed.

Independent searches (different conceptual wording from the first reading):

- LeanFinder: `spectral sequence exact triangle induced maps on cycles modulo
  boundaries`, eight results about homology sequences and connecting maps,
  none about an exact couple or the four clauses here.
- Loogle: `"imageSubobject", "kernelSubobject"`, no hits.
- LeanSearch: `An exact triangle of bigraded objects induces an exact triangle
  on images and homology`, unavailable (Internal Server Error).
- msearch grep: `couple|derivedMaps|pageCouple`, 24 unrelated Mathlib hits;
  none define this notion or state this theorem.
- Independent rg in Mathlib, source WeilConjectures, project's lean/Sheaf,
  and upstream name inventory for `derived.?couple|exact.?couple|pageCouple_image|
  derived_couple_exact`, and additional conceptual searches for
  `exact triangle|cycles modulo boundaries|induced.*exact|image.*alpha`.
  The only exact-couple implementation is the recorded dependency. Other
  conceptual matches concern derived-category functors and homology sequences,
  not this statement. I opened the dependency's `derivedMaps_exists`: it gives
  existence/exactness, but does not state uniqueness, the kernel/image identities,
  or the iterated-alpha-image formula. No existing declaration represents the
  entire node, so retaining this module is appropriate.

Mismatches and repairs: the first theorem's docstring referred to node steps
0--9 but also summarizes the assembly in step 10; changed it to 0--10. The
iteration theorem's docstring named step 10 although iteration is node step 11;
changed it to step 11. No signatures or mathematical node fields changed.
The node's `lean.statement` was checked by exact string equality against the
main signature, including its internal let expression. Both proofs remain
`by sorry`; the module introduces no definitions, extra instances or unbound
variables. The only import is the dependency actually used; docstrings retain
source places and the node's blueprint tag.

## Reviewer fix (R-dce1312)

The delivered last conjunct `∃! M : DerivedMaps X, True` asserted uniqueness only
among `DerivedMaps` witnesses, i.e. among triples that already satisfy all six
complex/exactness fields of a type-`(s+1)` couple. Clause 2 asks for uniqueness of
`α'`, `f'`, `g'` as the maps satisfying their defining equations alone. The conjunct is
now `∃ M : DerivedMaps X` together with, for each of the three maps separately, that
every map satisfying the corresponding `alpha_comm` / `f_comm` / `g_comm` equation
equals `M.alpha` / `M.f` / `M.g`. Nothing else changed.
