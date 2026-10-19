## Worker report

The module `Sheaf/Paper/IntegralEtaleCoverDisjointRefinement.lean` states
`AlgebraicGeometry.integral_etale_cover_disjoint_refinement`, the Stacks 04DR/04DP
property for an integral morphism.  It introduces schemes `X Y`, an integral map
`f`, an object `V : Y.Etale`, point `v`, an index type `I`, and an étale family
`U : I → (X ×_Y V).Etale`.  The hypothesis `hU` says every point of the pullback
lies in the image of one member, expressed using the underlying topological map.
The conclusion supplies `V'`, an étale map `a : V' ⟶ V`, and `v'` over `v`; an
index type `J`, schemes `W j`, open immersions `w j` into `X ×_Y V'`, an index map
`α`, and maps `b j` into the selected `U (α j)`.  The first conjunct makes the
underlying ranges pairwise disjoint, the second makes their union all points, and
the final conjunct is the required compatibility with the pullback map induced
by `a`.  The empty-index case is allowed by the existential quantification.

The potentially ambiguous pullback in the family type is forced to be the scheme
pullback by `(CategoryTheory.Limits.pullback f V.hom : Scheme)`; this is definitionally
the `[def-pc-fibre-product]` notion and avoids Lean selecting the type-theoretic
pullback.  The `pullback.map` in the compatibility clause is Mathlib's induced map.

Dependencies used are Mathlib declarations recorded by the node:
`AlgebraicGeometry.IsIntegralHom` from `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
`AlgebraicGeometry.Scheme.Etale` and its category structure from
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`CategoryTheory.Limits.pullback`/`pullback.map` from
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, and
`AlgebraicGeometry.IsOpenImmersion` from
`Mathlib.AlgebraicGeometry.OpenImmersion`.

Edge cases checked: `I` and `J` are arbitrary `Type u`, including empty types;
when the pullback is empty the covering hypothesis and existential conclusion
permit the empty decomposition; no nonemptiness or separatedness assumptions
were added.  The point maps use the underlying `TopCat` map of a scheme morphism,
so the domain and codomain are the actual scheme points.

Searches for an existing statement/definition found no match: `msearch.py ...
leanfinder` with “disjoint open refinement of etale coverings after shrinking an
etale neighborhood for an integral scheme morphism” returned only general étale
and integral declarations; `msearch.py ... loogle` with `"IsIntegralHom",
"Disjoint"` returned no hits; grep of Mathlib for `disjoint.*refin` and of
`WeilConjectures/` and `lean/Sheaf` for the item/name found no corresponding
statement.  The existing Mathlib notions above were used rather than copied.

No `STATEMENT-DISPUTED` issue or node fault remains.  The earlier coercion failure
was repaired by explicit scheme-pullback type annotations; the mandated server
compile is clean with only the expected `sorry` proof warning suppressed by the
project options.

## Earlier second reading (a previous round; superseded)

I reread the node and the module independently.  The binders match clause by clause: `f` is integral, `V` and `U` are étale objects, and `hU` is joint surjectivity on underlying points.  The conclusion has the required pointed étale refinement, open immersion pieces, pairwise disjoint ranges, exhaustive union, selected-cover maps, and pullback compatibility.  The explicit `(pullback f V.hom : Scheme)` annotations only disambiguate Mathlib elaboration and do not change the scheme fibre product.  No mismatch was found.

## Second reading by NC

Read the item JSON and Stacks etale-cohomology.tex, lemma-integral-B (04DR),
lemma-finite-B (04DQ), and lemma-simplify-B (04DP), including the surrounding
Property (B) section. No Noetherian, separatedness, finiteness, characteristic,
or nonempty-fibre hypothesis is assumed there. The node is a faithful explicit
refinement formulation. There is no statement_change, new node, or dependency
module to review.

Object/hypothesis/conclusion checklist (node order):

- Schemes X and Y: `{X Y : Scheme.{u}}`; matches arbitrary schemes in the fixed
  scheme universe, with no additional structure.
- Integral morphism f: `(f : X ⟶ Y) [IsIntegralHom f]`; matches. Opened
  Mathlib Morphisms/Integral.lean: the class extends IsAffineHom and requires
  integral section maps on every affine open, exactly the integral clause of
  def-weil-finite-integral-morphism, not its stronger finite clause.
- Small-etale object V over Y: `(V : Y.Etale)`; matches. Opened the protected
  Scheme.Etale definition in Morphisms/Etale.lean: morphism-property Over with
  etale structural map, and morphisms are over Y. Its instance makes every
  `a.left` etale. Thus existential `V' : Y.Etale` adds no assumption: an etale
  V' over V is etale over Y by composition, and conversely a map of these
  etale Y-schemes is etale.
- Chosen ordinary point v: `(v : V.left)`; matches, with no residue-field
  or geometric-point datum required.
- Arbitrary indexing set and etale family over X times_Y V: `(I : Type w)`
  and `U : I → (pullback f V.hom : Scheme).Etale`; matches. Corrected the
  former `I : Type u`, which excluded cover indices in larger universes.
- Joint surjectivity: `hU` gives for every pullback point an index and member
  point mapping to it. Opened Sites/Etale.lean and its
  `ofArrows_mem_smallEtaleTopology_iff`, confirming that the recorded topology
  uses precisely joint surjectivity of ranges; no finite-cover hypothesis.
- Fibre products: `CategoryTheory.Limits.pullback f V.hom` and `pullback f
  V'.hom`; matches def-pc-fibre-product. Opened HasPullback.lean at pullback,
  fst, snd, lift and map; these are the categorical universal constructions,
  instantiated in Scheme, not pullbacks of underlying sets.
- Pointed etale refinement: existential `V'`, `a : V' ⟶ V`, `v' : V'.left`
  and `(Scheme.Hom.toLRSHom' a.left).base v' = v`; matches precisely a point
  above v. No rational-point or residue-field-isomorphism condition is added
  to the explicit node formulation.
- Set J and open subschemes: existential `J : Type u`, `W : J → Scheme`,
  `w : ∀ j, W j ⟶ pullback f V'.hom`, and `∀ j, IsOpenImmersion (w j)`;
  matches. Opened OpenImmersion.lean at its abbreviation to the locally ringed
  space notion. Presenting an open subscheme by an open immersion is equivalent
  to presenting its image open and restricted structure sheaf. J may be small:
  the source proof actually constructs finitely many pieces, and nonempty
  disjoint opens in a u-small space also form a u-small family.
- Pairwise disjointness: `Set.Pairwise Set.univ` applied to disjoint ranges
  of the point maps `w j`; matches for distinct indices.
- Exhaustiveness: the indexed union of these ranges is `Set.univ`; matches
  every point of the total pullback, not just points over the chosen point.
- Selected original members: `α : J → I` and `b : ∀ j, W j ⟶ (U (α j)).left`;
  matches the quantifier order and retains maps into the original cover.
- Compatibility: `b j ≫ (U (α j)).hom = w j ≫ pullback.map ... (𝟙 X)
  a.left (𝟙 Y) ...`; matches the restriction of id_X times a. The two proof
  arguments express the required commutative squares, with `a.w.symm` the
  over-Y triangle. They impose no new hypothesis or conclusion.

Edge cases: I and J can be empty. If I is empty, hU forces the original total
pullback empty; an empty decomposition is permitted. If the new total pullback
is empty, choose empty J, so no impossible map from a nonempty J to empty I is
required. Empty X is allowed. Empty V or Y supplies no point v, just as in the
node. No zero-object, numerical n, or characteristic parameter is involved;
zero rings and empty spectra are not excluded by any binder. Universe w of I
is now independent of u; no test objects are quantified in too small a universe.
All variables and both universes are explicitly bound.

Independent searches: msearch leanfinder with "An integral scheme morphism
admits partitions subordinate to an etale covering after a pointed etale base
extension" returned eight general normalization/site/etale declarations, no
matching ordinary-point refinement theorem. Loogle `"IsIntegralHom",
"refinement"` returned zero hits. LeanSearch with "An etale covering of the
base change of an integral scheme morphism has a disjoint open refinement etale
locally at a base point" was unavailable (Internal Server Error); no verdict is
claimed for that service. Used rg with
`integral.{0,50}(disjoint|refin)|disjoint.{0,50}(etale|étale)` and the proposed
name in Mathlib/AlgebraicGeometry, upstream WeilConjectures, project lean/Sheaf,
and dag/lean_names_upstream.json.

The rg search found upstream Integral/DisjointCover.lean. Opened its definitions,
section assumptions, and `AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`
in full. It quantifies over a geometric point from an algebraically closed field,
a geometric pointed neighbourhood, and a covering sieve on the etale X-site;
it concludes sieve membership of open inclusions. It does not have the node's
ordinary-point, indexed-family signature with selected member maps. Passing
between them requires geometric-point choices, generated-sieve factorization,
and the pullback-symmetry identification. It is therefore a useful proof input,
not an exact existing declaration for this node. Other grep hits concern
already-given disjoint covers or pointed single-piece refinements. All notions
in the statement use the four existing dependency declarations read above;
none is copied or redefined.

Mismatches repaired: independent universe w for arbitrary cover indices (H3);
replaced the summary-only theorem docstring by all seven node proof steps,
including the finite-subalgebra cover argument and empty-fibre shrinking (H8);
added the three recorded upstream proof-dependency imports and restored the
module/public-import/exposed-section conventions (H9). The natural statement
and dependency lists did not change. No definition or mathematical theorem was
proved; the only theorem proof remains sorry. The proof terms inside
pullback.map merely certify its typing squares. No hollow definition exists.
The node lean.statement was resynchronized verbatim with the theorem signature.

Validation: scompile.py on the server passed in 1.5 seconds with nice 19, two
threads, 60-second per-file limit, with no errors or warnings. No local compiler,
Lake build, upstream source edit, or live-library write was used.
