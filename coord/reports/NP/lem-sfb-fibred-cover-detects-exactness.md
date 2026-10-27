## Worker report

The module `Sheaf.AlgebraicGeometry.FibredCoverDetectsExactness` states
`CategoryTheory.exact_of_fibred_etale_cover`, with one `sorry` and no definitions.
The accepted stage-1 split is unchanged. The inherited previous BLOCKED message
was about stage-1 `deliver.py`; coord/brief-stage2.md §0 expressly says to continue
this stage-2 assignment with `deliver2.py`. The sandbox initially held no files;
there is no repair note for this item.

Source read: literature/stacks-project/stacks-sheaves.tex, lines 3302–3341,
Tag 06XD, lemma-check-exactness-covering, statement and proof. Its topology is
specialized to etale exactly as the DAG requests. Its proof and the DAG's four-step
local lifting proof are included in the declaration docstring.

Clause-by-clause correspondence:

- Size convention: explicit universes `u v₁ w₁ v₂ w₂ a`, `Scheme.{u}`, and
  independently sized `BasedCategory.{v₁, w₁}` and `BasedCategory.{v₂, w₂}`.
  `AddCommGrpCat.{max u v₁ w₁ v₂ w₂ a}` puts coefficients in a common sufficiently
  large universe; `a` permits any larger bound. No equality of object and morphism
  universes is imposed. As recorded by the size-convention node, the convention
  is metatheoretic and needs no Lean declaration.
- Scheme S: `{S : Scheme.{u}}`.
- Categories fibred in groupoids U and X: the two `BasedCategory (Over S)` binders
  and `hU : IsFibredInGroupoids U`, `hX : IsFibredInGroupoids X`. These use the
  dependency's total-category definition, including existence of lifts and the
  uniqueness part of strong cartesianness.
- Morphism over schemes: `f : BasedFunctor U X`; its field `w` says precisely
  `f.toFunctor ⋙ X.p = U.p`. No faithfulness, representability, atlas, or
  algebraicity is assumed.
- Each big etale site: `(Scheme.etalePrecoverage.comap (X.p ⋙ Over.forget S))`
  (respectively U), followed by `.toGrothendieck`. Mathlib's `comap` says a
  presieve covers exactly when its image in schemes covers. Mathlib's
  `Scheme.etalePrecoverage` is the intersection of the jointly surjective
  precoverage and the etale morphism precoverage. In particular this uses the
  original objects and all arrows of the total category. Generated-topology
  sheaves give the same covering equalizer condition. This is a direct use of
  existing constructions, not a new notion requiring a definition node.
- Abelian sheaves: `Sheaf ... AddCommGrpCat`, Mathlib's full sheaf subcategory of
  contravariant functors. No underlying set-valued replacement is used.
- Local covering hypothesis: `hcover` supplies, for each `x`, an actual covering
  presieve `R`, and for every arrow `r : y ⟶ x` in it, an object `z : U.obj`
  and `Nonempty (f.toFunctor.obj z ≅ y)`. Presieves encode families with repeated
  arrows removed; neither their coverings nor this local-image property depend
  on repeated indexing. The isomorphisms are not required to lie over the
  identity, since the node asks only that the objects be isomorphic.
- Original complex F → G → H and ba = 0: `K : ShortComplex (Sheaf ... )`;
  `K.X₁`, `K.X₂`, `K.X₃`, `K.f`, `K.g`, `K.zero` are exactly these data.
- Precomposed sheaves, with precomposed arrows: `L` is a sheaf short complex on U,
  and `hL` identifies its underlying presheaf complex with the underlying K
  precomposed by `f.toFunctor.op`. `ShortComplex.map` transports every object,
  both arrows, and the zero-composite relation. The whiskering functor performs
  literal precomposition. Thus L is the precise complex in the hypothesis,
  rather than an arbitrary exact complex. No continuity or preservation-of-
  exactness hypothesis is added. Quantifying a sheaf complex together with this
  identification is a choice-free presentation of that precomposed complex;
  the source assures that precomposition is a sheaf for these inherited sites.
- Assumed exactness at the middle on U: `hexact : L.Exact`.
- Concluded exactness at G: `K.Exact`. This is the dependency's exactness, not
  objectwise exactness of presheaves (the latter would be stronger).
- F = 0 or H = 0: neither endpoint has any nonzero assumption. The theorem
  specializes directly to either zero endpoint and to both zero endpoints.
- The paragraph defining v_* fixes notation for a direct image that occurs
  nowhere in the criterion or its proof; no v, N, v_*, 2-product, or global
  section is an input or output of this theorem. Consequently no unused direct-
  image construction is introduced here. The only pullback used is the literal
  precomposition fixed by hL.

Dependency declarations and signatures read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (local affine
  locally ringed spaces), and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, the
  affine-locally etale morphism predicate. `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.etalePrecoverage`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `ModuliTwoIso`,
  `GroupoidTwoFiberProduct`, `moduliTwoFiberProduct`, and `moduliTwoFiberFst`.
  The first is used directly; the rest of the node's two-category vocabulary
  does not enter this criterion. The BasedCategory and BasedFunctor signatures
  were also read in Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its definition and docstring
  identify the site convention. The actual statement uses the retained
  Mathlib `Precoverage.comap`, `Precoverage.toGrothendieck`, and `Sheaf` API.
- `Mathlib.Algebra.Homology.ExactSequence`: the recorded exact-sequence API;
  `CategoryTheory.ShortComplex`, `ShortComplex.Exact` are used directly.
  Read `ShortComplex.Exact` and `exact_iff_epi_kernel_lift` in
  Mathlib/Algebra/Homology/ShortComplex/Exact.lean.
- Proof imports `Mathlib.CategoryTheory.Sites.Sheafification` (sectionwise
  limits / left exact sheafification) and `Mathlib.CategoryTheory.Sites.EpiMono`
  (`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`); the exact-iff-epi-kernel-
  lift dependency is already exposed through ExactSequence. These three proof
  dependencies are Mathlib leaves with mathlib_match and need no Lean repair.

Edge cases checked: empty covering presieves are allowed exactly over objects
whose underlying scheme admits the empty etale covering; no nonempty index type
is required. Empty fibred categories are allowed and the local-image hypothesis
controls when they can cover X. Zero left/right terms and the all-zero complex
are included. The identity based functor satisfies the intended criterion.
Automorphisms and nonfaithful functors are retained; no passage to isomorphism
classes or representable source is made. The coefficient universe covers both
sites and permits enlargement. All implicit variables are explicitly bound and
`set_option autoImplicit false` checks this.

Searches performed in this session (no exact existing declaration found):

- `msearch.py ... leanfinder "A locally essentially surjective functor of
  categories fibred in groupoids detects exactness of abelian sheaves by
  precomposition"`: eight hits, including coherent/extensive local surjectivity,
  Mayer–Vietoris exactness, sheaf exact limits/colimits and Functor.exact_tfae.
  None establishes this criterion for the inherited fibred-category site.
- `msearch.py ... loogle '\"Sheaf\", \"exact\"'`: twelve hits, including
  HasSheafify.isLeftExact, sheaf exact limits/colimits and cohomology long
  sequences. None is the criterion.
- `msearch.py ... grep 'reflects_exact|exact_iff|[Ff]ibred|[Ff]ibered'
  CategoryTheory/Sites`: one hit in Descent/IsPrestack.lean, a comment about
  fibered-category descriptions, not this theorem.
- `rg` in both project roots for `reflects_exact`, fibred exactness and the item
  id: no matching statement. General faithful-functor reflection occurs in
  several modules, but does not supply the asserted fibred-site functor or its
  hypotheses. `tools/lean_names_upstream.py show` was consulted; the proposed
  name has no match in its index or either source root.
- Read Mathlib `Precoverage.comap`, `Scheme.etalePrecoverage`, and
  `Scheme.ofArrows_mem_precoverage_iff` to confirm the exact covering condition.

Server validation: scompile.py compiled the final module in sandbox and library
mode, cleanly (7.8 s / 3.3 s), after correcting the namespace qualification
`Functor.whiskeringLeft`. No statement correction, new node, or dependency
module is needed. No STATEMENT-DISPUTED flag.

## Second reading by NP

Author's final cross-check, not a claim of independent review: this dispatcher
brief forbids starting other agents; the maintainer performs the independent
reading after delivery. I reread the node, Stacks 06XD and the final signature.
Every input of the criterion is represented: fibred categories over S, based
functor, covering-local image, an abelian sheaf complex, and exactness of its
precomposition. The output is middle exactness of that same complex. The
underlying-complex equality hL constrains both arrows as well as the three
objects, so it does not permit an unrelated exact L. Both endpoint cases and
nonfaithful morphisms remain included. The unused v_* notation is explanatory
context, with no occurrence in the assertion. No DAG statement or split changed.
