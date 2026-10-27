## Worker report

Item: `lem-trf-scheme-descent-cocycle-etale-relation`, group Q38, stage 2.
The module `Sheaf.AlgebraicGeometry.SchemeDescentCocycleEtaleRelation` states
`AlgebraicGeometry.SchemeDescentCocycle.etale_relation` with one `sorry`.
Its six proof-free abbreviations name only the constructions already displayed in
this node: the iterated overlaps, their two projections, and the structure, source,
and target coproduct maps. All are recorded in `lean.declarations`. They use
Mathlib's chosen pullbacks and coproducts; no descent-datum structure or independent
notion is introduced. There are no new nodes, dependency repairs, or statement changes.

Source read: `literature/stacks-project/descent.tex`, lines 8170–8270,
Tag 023W, `definition-descent-datum-for-family-of-morphisms` and
`remark-easier-family`; `groupoids.tex`, lines 65–120, Tag 022P,
`definition-equivalence-relation`; `spaces.tex`, lines 1595–1630,
Tag 02WW, `theorem-presentation`. As the node and proof_origin explicitly say,
02WW consumes the constructed relation; the actual cocycle calculation is the
agent-origin argument grounded in 023W and 022P. I read the item and all five
statement dependencies, including their recorded interfaces, and the seven
proof-dependency interfaces. No repair note is present for this item.

Clause-by-clause rendering:

- The scheme S is the section binder `{S : Scheme.{u}}`. The index is
  `{I : Type u}` and the schemes are `{U X : I → Scheme.{u}}`. The morphisms
  `u : ∀ i, U i ⟶ S` and `f : ∀ i, X i ⟶ U i` introduce exactly the stated
  covering members and their local schemes. All section variables and universes
  are explicitly bound; `autoImplicit` is false.
- Étaleness of every covering map is `[hu : ∀ i, Etale (u i)]`. Joint surjectivity
  is `hcover : ∀ x : S, ∃ (i : I) (y : U i), u i y = x`, exactly the pointwise
  union-of-ranges condition in the recorded small-étale-site covering lemma.
  The hypothesis is retained although the relation construction does not use
  surjectivity; it is not universally true for arbitrary families.
- `U_ij` is `pullback (u i) (u j)`, and `overlap u f i j` is exactly
  `pullback (f i) (pullback.fst (u i) (u j))`. Thus the statement uses the
  specified iterated fibre product itself, not just an isomorphic replacement.
  `projection` is its first projection `p_i`. `otherBase` is the composite of
  the other projection with `pullback.snd (u i) (u j)`. The first base coordinate
  is `projection u f i j ≫ f i`, by the pullback condition.
- The isomorphisms are `θ : ∀ i j, overlap u f i j ≅ overlap u f j i`.
  Both base-interchange clauses are in `hbase`: the target's X_j projection
  followed by f_j is the input's U_j coordinate, and its other U_i coordinate
  is the input's X_i projection followed by f_i. Neither clause is omitted.
- The diagonal restriction is `hdiagonal`, quantified over every `T : Scheme.{u}`
  and `a : T ⟶ overlap u f i i` with equal base coordinates. This equality
  says exactly that the base map factors through the diagonal U_i → U_ii.
  The conclusion fixes the X_i coordinate. The base coordinates of its image
  already agree by `hbase`; uniqueness in the two nested pullbacks then fixes
  the entire point. Conversely, a diagonal-restriction identity implies this
  formula on every T. This is equality of morphisms by Yoneda, not a condition
  only on underlying topological points.
- The triple-overlap pullback cocycle is `hcocycle`. Here `a : T → R_ij`,
  `b : T → R_jk`, `c : T → R_ik`. Its first premise says that b's X_j
  coordinate is the result of θ_ij on a. The second says that c has a's X_i
  coordinate. The third says that b and c have the same U_k coordinate.
  By the fibre-product universal property, such triples are exactly test points
  of the domain of the triple-overlap cocycle: choose x_i, its compatible U_j
  coordinate and its compatible U_k coordinate. The corresponding b and c
  exist uniquely by pullbacks, since `hbase` supplies the X_j base compatibility.
  Its conclusion equates the X_k coordinates of θ_jk(b) and θ_ik(c).
  Their U_i and U_j coordinates agree already by `hbase`, so this is exactly
  θ_jk ∘ θ_ij = θ_ik on the triple pullback. Taking the universal test object
  recovers the morphism identity; pulling that identity back recovers this
  hypothesis. No extra cocycle assumption is imposed.
- `V` is `∐ X` and `R` is `∐ fun ij : I × I ↦ overlap u f ij.1 ij.2`.
  Their component inclusions are Mathlib's `Sigma.ι`. `structureMap` is
  `Sigma.desc (fun i ↦ f i ≫ u i)`. `sourceMap` is the coproduct desc of
  `projection ... ≫ Sigma.ι X i`, and `targetMap` is the desc of
  `(θ i j).hom ≫ projection ... ≫ Sigma.ι X j`. Thus both endpoint maps are
  exactly the maps prescribed in the statement, not arbitrary candidates.
- The first two conclusions are `Etale (sourceMap u f)` and
  `Etale (targetMap u f θ)`. The existential equality witness `h` types the
  canonical pairing into the fibre product over S. It is the implicit
  well-definedness of the node's displayed `(s,t)` map, not a new hypothesis
  or an independently chosen map. `Mono (pullback.lift ... h)` is precisely
  the scheme monomorphism R → V ×_S V.
- Finally `∀ T : Over S` ranges over all S-schemes, and the two variables of
  `Equivalence` are S-morphisms `T ⟶ Over.mk (structureMap u f)`.
  The relation is `∃ r : T.left ⟶ R, r ≫ sourceMap ... = a.left ∧
  r ≫ targetMap ... = b.left`. The first endpoint equality automatically
  makes r an S-morphism for R's induced structure map s ≫ structureMap.
  Thus its witnesses are exactly R(T), with no excess witnesses. `Mono`
  supplies injectivity and `Equivalence` supplies reflexivity, symmetry and
  transitivity of its image, giving the asserted identification.

Dependency declarations used, with source signatures and docstrings read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom` (Scheme.lean:42, 74).
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology`, `Scheme.Etale`, and
  `Scheme.ofArrows_mem_smallEtaleTopology_iff` (Sites/Etale.lean:51, 61;
  Morphisms/Etale.lean:157). The union-of-ranges clause is rendered explicitly.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`
  (HasPullback.lean:95–138), with scheme pullback existence from Mathlib.
- `lem-weil-pbc-scheme-coproduct-family`: `Mathlib.AlgebraicGeometry.Limits`,
  the `HasColimitsOfShape (Discrete σ) Scheme` instance,
  `sigmaOpenCover`, and `disjoint_opensRange_sigmaι` (Limits.lean:187, 202, 241).
  The constructions use `Sigma.desc`, `Sigma.ι` and `∐` from that interface.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (Etale.lean:41), publicly available through Sites.Etale.
- Proof-only interfaces are the recorded Mathlib leaves: `Etale.etale_isStableUnderBaseChange`
  and the projection instances (Etale.lean:74–90);
  `IsOpenImmersion` (OpenImmersion.lean:38);
  `Etale.etale_comp`, the open-immersion instance, and `Etale.of_comp`
  (Etale.lean:69, 78, 130);
  `IsZariskiLocalAtSource.iff_of_iSup_eq_top` (Morphisms/Basic.lean:272);
  `Scheme.Cover.glueMorphisms`, `Scheme.Cover.hom_ext`, `ι_glueMorphisms`
  (Gluing.lean:448–474). They are available from the public statement imports
  except Gluing, which is imported with plain `import` for stage 3.

Edge cases checked mathematically before writing:

- Empty I: `hcover` then forces S empty. Both coproducts are empty, their endpoint
  maps are étale, and the relation on each test Hom set is the empty or singleton
  equivalence relation as appropriate. No Nonempty instance is assumed.
- Empty local schemes and empty overlaps: the test-point equalities still state
  the identities without requiring inhabited schemes or fibres.
- Disconnected test T: the conclusion uses all maps T → V, not a sigma type of
  maps into one X_i. Such a map may meet several components. The proof docstring
  explicitly partitions by inverse images of the coproduct components and glues.
- Singleton cover with u_i not mono: R_ii need not be X_i. The normalization is
  imposed only on the diagonal base restriction; it does not incorrectly demand
  θ_ii = id on the whole overlap.
- Infinite families, nonseparated schemes, and arbitrary f_i: no finiteness,
  separatedness, or extra property of f_i appears. The index and schemes use the
  same universe, as required by the recorded scheme-coproduct interface; universe
  enlargement accommodates an arbitrary set-sized family. Test schemes use that
  same Scheme category, so no quantification over a smaller category is hidden.
- In particular hdiagonal and hcocycle are tested on all scheme-valued points,
  including nonreduced test schemes, rather than geometric or carrier points.

Searches performed (all msearch invocations are logged in sandbox searches.jsonl):

- LeanFinder: `A scheme descent cocycle for an etale cover gives an etale equivalence
  relation on the coproduct` returned GlueData.Rel, covering coproduct and étale-site
  interfaces. A second query, `Construct an etale equivalence relation from descent
  isomorphisms on overlaps of a scheme cover`, returned the same GlueData/site
  interfaces. I read GlueData (Gluing.lean:91) and Rel (241): they concern gluing
  by open immersions and a relation on carrier points, not this arbitrary étale
  construction on all scheme-valued points.
- LeanSearch: `etale equivalence relation constructed from scheme descent data`
  returned pseudofunctor stack/equivalence results, Etale, and TopCat.GlueData.rel_equiv.
  None states the construction in this node.
- Loogle: `Scheme, Etale, Relation` could not resolve the short identifier Scheme.
  Retried with `AlgebraicGeometry.Scheme, CategoryTheory.Mono`, which returned
  open-immersion monomorphisms, pullback map properties, and flatness results,
  with no statement matching this construction.
- msearch grep: `DescentDatum|EquivalenceRelation|descent.*cocycle` in
  `AlgebraicGeometry` returned zero hits from that search wrapper. The subsequent
  file-targeted query `GlueData|glueMorphisms|Descent` in
  `AlgebraicGeometry/Gluing.lean` returned the gluing interfaces, inspected above.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` searched DescentDatum,
  descentCocycle, etaleRelation, equivalenceRelation, and later their capitalized
  variants. Existing SchemeCoverDescentDatum is a represented-sheaf descent-data
  interface, not the relation-construction theorem (its module was read).
  Existing EtaleRelationQuotient takes an already given equivalence relation,
  and does not prove one arises from θ_ij (its source was read).
  IsDescentCocycle for twisted constant sheaves and DescentCocycle for global
  functions likewise have different objects. The new namespace and theorem name
  have no hit in either library, Mathlib, or dag/lean_names_upstream.json.
- `grep -rn 'lem-trf-scheme-descent-cocycle-etale-relation' lean/WeilConjectures`
  returned no upstream binding.

Validation: the prescribed scompile.py compiled both its sandbox probe and the
actual module cleanly (3.9 s and 1.9 s); there are no errors or unexpected warnings.
The only postponed theorem is `etale_relation`; its docstring gives the full
six-step node argument, including the cited proof dependencies. No definitions
have postponed data. No STATEMENT-DISPUTED or node correction is needed.

## Second reading by Q38

This is the submitting worker's second pass; the independent review belongs to
the maintainer as specified in the dispatcher brief. I reopened the node and the
module and checked the five statement dependencies against their recorded sources.
The particularly sensitive clauses are unchanged: R_ij is the iterated pullback,
θ interchanges both base projections, diagonal normalization is restricted to the
diagonal rather than all R_ii, and the cocycle has the correct i→j→k order.
On a triple overlap, selecting a fixes x_i and u_j; selecting the last base
coordinate fixes c and then b uniquely. The three premises in hcocycle express
exactly those selections, and the conclusion fixes precisely the resulting x_k.
There is no assumption that θ_ji is given as θ_ij's inverse; it follows from the
stated cocycle and diagonal condition, as in the node's symmetry proof.

I also checked the coproduct component formulas against the node, the relative
base of the canonical monomorphism, and the full test-point conclusion. The
existential r is automatically over S, and monicity makes its lift unique.
The explicit `h` only types the canonical pullback pairing; it does not assume
commutativity as an extra input. Empty and disconnected test schemes remain
included. All six helper abbreviations have real Mathlib constructions and source
docstrings, and only the theorem is `sorry`. This second pass found no mismatch
requiring a statement change.
