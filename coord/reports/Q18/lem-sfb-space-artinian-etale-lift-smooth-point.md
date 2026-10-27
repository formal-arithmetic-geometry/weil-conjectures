## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceArtinianEtaleLiftSmoothPoint` states
`AlgebraicGeometry.AlgebraicSpace.smooth_near_of_artinian_etale_lifting`, with the
single proof `by sorry`. It introduces no definitions. The node statement and proof
are unchanged. Its `stmt_deps` gains the already landed definition node
`def-trf-scheme-algebraic-space`, owning the existing `schemeSpace` construction.

Sources read: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-lifting-along-artinian-at-point` (0APN), and
`lemma-smooth-formally-smooth` (04AM), including its lift-torsor argument.
The former gives the small-extension pointwise criterion and the latter supplies
the passage from local lift sections to a global section on an affine scheme.

Hypotheses and clauses, with the node and Lean file open:

* The locally Noetherian scheme S is `{S : Scheme.{u}} [IsLocallyNoetherian S]`.
* The algebraic space X over S is `(X : AlgebraicSpace S)`.
* The morphism f to S is `(f : X ⟶ schemeSpace (Over.mk (𝟙 S)))`.
  The target is the existing actual representable sheaf h_S, not an arbitrary model.
  It is terminal among spaces over S, so f is the structure morphism. Naturality
  of every map of Over-S presheaves enforces compatibility with this morphism.
* Local finite presentation is exactly
  `(hfp : MapIsLocallyOfFinitePresentation f)`, the dependency's compatible
  étale-chart predicate, with no representability assumption on f.
* The point x of |X| is `(x : Point X.obj.obj)` using the existing field-valued
  point quotient, without choosing a representative or atlas.
* Every pair of Artinian local rings is quantified by `(B' B : Type u)` with
  `[CommRing B'] [CommRing B] [IsArtinianRing B'] [IsArtinianRing B]`
  and `[IsLocalRing B'] [IsLocalRing B]`. Artinianness is the existing descending
  chain condition on submodules of the ring, equivalently its ideals. Localness
  includes the unique maximal ideal and excludes the zero ring, as the source does.
* The test surjection is `(φ : B' →+* B), Function.Surjective φ`; its square-zero
  kernel is `(RingHom.ker φ) ^ 2 = ⊥`. There is no length-one restriction.
* The lower arrow is `(c : Spec (CommRingCat.of B') ⟶ S)`. The upper arrow is
  `(a : yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ c)) ⟶ X.obj.obj)`.
  These are precisely maps Spec B → X over S with base map j ≫ c. Consequently
  the commutativity equation f a = c j is built into the Over-S map, rather than
  imposed as an extra hypothesis. Yoneda identifies these natural
  transformations with the scheme-source maps to the algebraic space.
* Centering at x is `schemePointMap a (IsLocalRing.closedPoint B) = x`.
  The closed point is the unique point because B is Artinian local.
* An étale covering of Spec B' is expressed explicitly as
  `∃ (I : Type u) (T : I → Over S) (q : ∀ i, T i ⟶ Over.mk c),`
  `(∀ i, Etale (q i).left) ∧`
  `(∀ y : Spec (CommRingCat.of B'), ∃ (i : I) (z : (T i).left), (q i).left z = y)`.
  This is jointly surjective, without requiring each q_i to be surjective.
  The universe is that of the test schemes, also used by the existing scheme
  Artinian criterion. Any covering family can be reduced to this size by choosing
  one member and one lift for each point of the target.
* For each i the lifted arrow is `∃ b : yoneda.obj (T i) ⟶ X.obj.obj`.
  It is over S by its type. The displayed equality
  `yoneda.map (pullback.fst (q i) j) ≫ b = yoneda.map (pullback.snd (q i) j) ≫ a`
  is restriction to T_i ×_(Spec B') Spec B, where j is explicitly
  `Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl` with source and target
  annotated. Pullbacks in Over S are the actual scheme fibre products with their
  induced structure maps, so this equality is exactly the required restriction.
* The conclusion is `∃ V : OpenSubspace X, x ∈ pointImage V.val.ι ∧ ...`.
  This uses the dependency's representably open subfunctor, whose image is the
  corresponding open subset of |X|. It does not replace V with an arbitrary
  subset or arbitrary étale neighbourhood.
* Smoothness of f restricted to V is
  `∀ (U : Over S) (a : yoneda.obj U ⟶ V.val.toFunctor), IsEtale a → Smooth U.hom`.
  This is the chart test for the structure map V → S: every representable étale
  scheme chart of V is smooth over S. The target chart can be taken to be S
  itself; other étale charts of S give the equivalent usual two-chart test by
  étale base change and locality. Since f is the structure map, U.hom is exactly
  its composite with a. No choice of an algebraic-space structure on the open
  subfunctor is needed to spell out the chart test.

Dependency declarations used, with full signatures/docstrings inspected:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
* `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocallyOfFinitePresentation`, defined using
  `MapIsLocally` and the Mathlib locally-finite-presentation property.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`:
  `AlgebraicGeometry.AlgebraicSpace.OpenSubspace`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointImage`; it imports the recorded point
  quotient `Point` and `schemePointMap` from `AlgebraicSpacePointClasses`.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace`, owned by the added landed node.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.

Statement dependencies imported transitively through their recorded owning modules
remain the existing declarations; none was copied. Public imports expose all
statement ingredients. Already stated proof dependencies are imported privately:
`WeilConjectures.AlgebraicGeometry.Thickening` (`IsFirstOrderThickening`),
`WeilConjectures.CategoryTheory.Sites.Torsor` (`Sheaf.Torsor`,
`Sheaf.nonempty_equiv_H_one_torsor`),
`WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift`
(`Etale.etale_affine_qcoherent_ulift`),
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`
(`CategoryTheory.stack_chartwise_smooth_etale_calculus` and its accompanying laws),
and `WeilConjectures.AlgebraicGeometry.SmoothArtinianLiftingAtPoint`
(`smooth_near_iff_artinian_lifting_at_point`). Three proof-only prerequisites have
no Lean record locally: `lem-sfb-space-infinitesimal-lift-pseudotorsor`,
`lem-sfb-smooth-space-affine-infinitesimal-lift`, and
`lem-sfb-space-smooth-source-point-locality`; no nonexistent module is imported.
They do not supply notions needed in the signature. The docstring retains every
step of the node's natural-language proof, including these deferred proof inputs.

Edge cases checked before and after writing:

* Empty X (or empty S) has no point x, so no unjustified existence claim results.
* The zero ring has no unique maximal ideal and is correctly excluded by localness.
* The identity extension (kernel zero) is included: lift a itself after the
  identity étale cover. No nonzero-kernel or length-one premise was inserted.
* Dual numbers are among the tests; non-smooth infinitesimal points are not
  silently excluded by passing only to residue fields.
* Empty covering families are syntactically allowed but cannot cover Spec B'
  for a local ring. Infinite covers and arbitrary nonaffine members are allowed.
* X and f need not be separated, quasi-compact, or representable by schemes.
* All schemes, field representatives and Artinian test rings use the same
  universe u, with the existing Point quotient in Type (u+1). There is no
  independently smaller test universe that could make the hypothesis vacuous.

Searches for existing statements and notions (2026-10-24):

* `msearch.py ... leanfinder` with query
  `A locally finitely presented algebraic space over a locally noetherian scheme is smooth at a point if centered square zero Artinian local lifting problems have etale local solutions`:
  eight hits, including `isSmooth_iff`, `IsSmooth.exists_isStandardSmooth`,
  `instLocallyOfFinitePresentationOfIsSmooth` and smooth relative-dimension results.
  They are scheme statements and do not state the algebraic-space criterion.
* `msearch.py ... loogle '\"Smooth\", \"Artinian\"'`: zero hits.
* `msearch.py ... grep 'Artinian.*smooth|smooth.*Artinian|artinian.*lifting' AlgebraicGeometry`:
  zero hits.
* `msearch.py ... leansearch` with query
  `An algebraic space locally of finite presentation over a locally noetherian scheme is smooth at a point if Artinian square zero tests centered there lift etale locally`:
  eight hits, including scheme smoothness constructors, `RingHom.smooth_def`,
  `Algebra.IsSmoothAt`, `Algebra.Smooth.formallySmooth` and finite presentation;
  none states the algebraic-space pointwise assertion.
* `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `artinian.*etale.*smooth`, `artinian.*smooth.*point`, and
  `smooth_near_of_artinian_etale_lifting`: no duplicate statement. Broader
  Artinian/smooth searches locate the existing scheme criterion and supporting
  scheme/ring results, which were inspected and reused as proof imports.
* `rg` of `dag/lean_names_upstream.json` with the same exact-id/name patterns:
  no exact match. Searches for `OpenSubspace`, `MapIsLocally.*Smooth` and
  `schemeSpace` located the existing APIs. Reading
  `def-trf-scheme-algebraic-space.json` confirmed the landed definition node for
  the representable construction, so it is cited rather than recreated.

No statement correction, dependency repair, new node, or STATEMENT-DISPUTED issue
is needed. Compilation uses the prescribed scompile wrapper only.

## Second reading by Q18

The dispatcher prohibits starting another agent. This section records a separate
self-reading after reopening the completed module and original node; it does not
claim an independent second worker. The maintainer's independent review remains.

I checked the quantifiers and their scope: the Artinian test ranges over both rings,
all surjections with square-zero kernel, every c and every a over c j centered at
x; the cover and all compatible lifts occur after these tests. Cover surjectivity
is collective and no individual q_i is required to be surjective. The restriction
equation has the first pullback projection before b and the second before a.
The first compile exposed insufficient type information for the first occurrence
of the Over-S closed immersion; both occurrences now carry the same explicit
source and target. No mathematical condition changed.

I checked that representing S by h_S loses no f: h_S is terminal in Over-S
presheaves, so both the input diagram and the lifted maps commute over S by their
types. The open conclusion uses the existing OpenSubspace and its point image,
and Smooth U.hom is the actual structure map on every étale chart of that open.
This matches the node's smooth-neighbourhood conclusion without making the whole
of X smooth or replacing the neighbourhood by a covering chart.

I also compared the module's proof docstring with all five node proof steps:
the lift pseudo-torsor, affine H1 trivialization, chart choice and finite-type
calculus, transfer of Artinian tests to the chart, and the scheme criterion followed
by smooth-source descent are all present. No data definition or theorem other
than the assigned statement was introduced.
