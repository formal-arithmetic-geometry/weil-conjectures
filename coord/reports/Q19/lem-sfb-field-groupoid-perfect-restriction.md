## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGroupoidPerfectRestriction` states
`AlgebraicGeometry.exists_perfect_field_groupoid_restriction`, with one `sorry`, and
constructs the auxiliary arrow-coordinate projection
`AlgebraicGeometry.groupoidRestrictionProjection` as the composite of two actual
pullback projections. No definitions use postponed data. No mathematical statement
was corrected; there is no statement dispute.

Sources read: Stacks `more-groupoids.tex`, lines 1002–1042, Tag 04LQ
(`lemma-restrict-groupoid-on-field`), and lines 1598–1620, Tag 04Q9
(`lemma-locally-closed-image-is-closed`), first proof paragraph;
`groupoids.tex`, lines 3475–3516, Tag 02VB (`lemma-restrict-groupoid`).
The first paragraph of 04Q9 makes the perfect closure reduction and identifies both
arrow projections as composites of two base changes of a universal homeomorphism.
Tag 02VB supplies the restriction operations on test points. The restriction data
are written for absolute groupoids: the two maps to Spec k need not agree.

Hypotheses, clause by clause:

- A field k: `(k : Type u) [Field k]`; its V is exactly
  `Spec (CommRingCat.of k)` everywhere in the signature.
- The two arrow schemes and the five operations are encoded by families indexed
  by `Fin 2`: `R`, `s`, `t`, `e`, `i`, `c`. Indices 0 and 1 are respectively the
  node's indices 1 and 2. A two-term family adds no third object or assumption.
  The domains of `c j` are exactly `pullback (s j) (t j)`.
- The groupoid condition is
  `hG : ∀ j : Fin 2, IsGroupoidScheme (s j) (t j) (e j) (i j) (c j)`.
  The recorded dependency's full signature and docstring were read: its source,
  target, identity, inverse and associativity laws are the test-scheme laws of
  the node, with composition ordered c(r,v) = r after v.
- The arrow morphism is `a : R 0 ⟶ R 1`. The assumptions `hs`, `ht`, `he`, `hi`,
  `hc` express compatibility with source, target, identity, inverse, composition,
  respectively. `hc` uses Mathlib's canonical `pullback.map a a (𝟙 V)` with the
  source/target compatibility proofs, so the object map is the identity.

Conclusions, clause by clause:

- A field extension is `∃ (K : Type u) (_ : Field K) (_ : Algebra k K)`.
  Its structure homomorphism is `algebraMap k K`; it is injective since k is a
  field and K is nontrivial. `PerfectField K` is Mathlib's standard perfectness.
  `PerfectField.ofCharZero` and `PerfectField.toPerfectRing` show the agreement
  with the node's characteristic-zero/positive-characteristic description;
  the latter gives surjectivity of Frobenius in positive characteristic.
- V' is exactly `Spec (CommRingCat.of K)`. The existential morphism `g` is fixed
  by the explicit equation
  `g = Spec.map (CommRingCat.ofHom (algebraMap k K))`; it is the canonical map.
- The restricted arrow scheme for j is exactly
  `pullback (groupoidSaturationMap (s j) (t j) g) g`.
  Unfolding the existing saturation map gives
  `(V' ×[V,t j] R j) ×[s j,V] V'`. No isomorphic replacement is introduced.
- The existing `groupoidRestrictionSource` is the last endpoint projection and
  `groupoidRestrictionTarget` the first endpoint projection. They fix the two
  outer coordinates. The existential `e'`, `i'`, `c'` have precisely the domains
  of the restricted unit, inverse and composition. Their `IsGroupoidScheme`
  clause states all groupoid axioms, natural in every test scheme.
- The equations for `e' j ≫ groupoidRestrictionProjection` and
  `i' j ≫ groupoidRestrictionProjection` fix their middle coordinates to e(gx)
  and i(r). Together with the groupoid source/target laws they give exactly
  `(x,e(gx),x)` and `(y,i(r),x)`.
- The universally quantified equation with `H`, `r`, `v`, `h`, `h₀` fixes the
  middle coordinate of composition to `c j (r,v)`. The groupoid source/target
  laws fix its endpoints, giving `(x,c(r,v),z)` for a composable pair.
  This clause is not vacuous: by the two pullback conditions, source' followed
  by g equals projection followed by source, and target' followed by g equals
  projection followed by target. Composing `h` with g therefore supplies `h₀`.
  Both proofs are universally quantified, so no dependence on a chosen proof
  is imposed. Pullback uniqueness gives the indicated formula on all test points.
- The induced arrow map `a'` has exactly the two restricted arrow schemes as
  domain and codomain. Its existential equations `hs'`, `ht'` preserve the two
  endpoint projections, and its final projection equation preserves the middle
  coordinate by a. These three equations uniquely specify `(x,r,y) ↦ (x,a(r),y)`.
- The next three equations assert that `a'` commutes with unit, inverse and
  composition. The composition equation uses the canonical `pullback.map`
  on composable pairs with object map the identity of V'. Together with `hs'`
  and `ht'` these are exactly the five operation compatibilities in the node.
- For each j the clause
  `IsHomeomorph (groupoidRestrictionProjection (s j) (t j) g).base` says that
  the underlying continuous arrow-coordinate projection is a homeomorphism.
- The last equation
  `a' ≫ groupoidRestrictionProjection (s 1) (t 1) g =
   groupoidRestrictionProjection (s 0) (t 0) g ≫ a`
  is exactly q₂ ∘ a' = a ∘ q₁, in Lean's left-to-right composition convention.
- No finiteness, quasi-compactness, separatedness, equality of s and t, or
  compatibility with a common k-scheme structure is assumed.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (def-weil-affine-spectrum).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`
  (def-pc-field-extension).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.map`
  (def-pc-fibre-product); their signatures and universal-property docstrings
  were read, including the order of all three maps and both equations of map.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  `AlgebraicGeometry.IsGroupoidScheme` (def-a1-groupoid-scheme).
- `Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction`:
  `AlgebraicGeometry.groupoidSaturationMap`, `groupoidRestrictionSource`,
  `groupoidRestrictionTarget`. The new existing:true definition ownership node
  `def-sfb-groupoid-restriction` is cited in stmt_deps for precisely these three
  canonical definitions. The module’s Cohen–Macaulay theorem is not a statement
  dependency. The helper definitions' complete docstrings and bodies were read.
- `Mathlib.FieldTheory.Perfect`: `PerfectField`, with the characteristic
  comparisons `PerfectField.ofCharZero` and `PerfectField.toPerfectRing`.
- Proof dependency imports: `Mathlib.FieldTheory.PurelyInseparable.PerfectClosure`
  (`perfectClosure.isPurelyInseparable`, `perfectClosure.perfectField`), together
  with `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, give the recorded
  Mathlib match of lem-weil-pbc-perfect-purely-inseparable-overfield;
  `WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`
  gives `AlgebraicGeometry.isHomeomorph_baseChange_of_isPurelyInseparable`
  (lem-pc-homeo-pure-insep). These are plain proof imports; the first three
  statement modules above are public imports or exposed through the groupoid
  dependency. No independent dependency interface needed repair.

Edge cases checked before writing and on the second pass:

- Characteristic zero allows K=k; an already perfect positive-characteristic
  field likewise allows the identity extension. Nothing forces positive
  characteristic or a proper extension.
- Imperfect positive-characteristic fields use their perfect purely inseparable
  closure, available in the same universe u. The homeomorphism is asserted for
  the underlying spaces, not as an isomorphism of schemes.
- s and t may be different: the two factors are base changed separately, so
  absolute field groupoids with two field embeddings are included.
- Arbitrary nonreduced and non-quasi-compact arrow schemes are allowed. There is
  no reducedness or finiteness binder. Unit maps rule out an empty arrow scheme
  over the nonempty field spectrum, as already forced by the input groupoid laws;
  an empty test scheme is included and satisfies all the pointwise formulas.
- The identity morphism a and terminal groupoids satisfy precisely the same
  formulas. The test-scheme composition clause has no vacuous missing proof:
  the old composability proof exists by the pullback equations as explained above.
- The common universe is arbitrary; a perfect closure of k exists in Type u.
  There is no independently smaller universe in a universal test hypothesis.

Searches actually run:

- msearch.py LeanFinder: "Perfect field extension restriction of an internal
  groupoid scheme gives homeomorphisms of arrow schemes". Eight hits, including
  `arrowResLEAppIso`, `morphismRestrictEq`, `morphismRestrictRestrict` and
  `Scheme.SpecToEquivOfField`; none states the groupoid assertion.
- msearch.py Loogle: "IsGroupoidScheme, pullback, IsHomeomorph". Zero hits;
  diagnostic "unknown identifier 'IsGroupoidScheme'". This search does not
  establish absence of the local project declaration; that declaration was
  located and reused by direct source search.
- msearch.py grep: "IsGroupoidScheme|groupoidRestriction|restrictGroupoid".
  Zero Mathlib hits.
- msearch.py LeanSearch: "Restricting a morphism of groupoid schemes to the
  spectrum of a perfect closure preserves the topology of the arrow schemes".
  Eight hits about restriction to opens and permanence of morphism properties;
  none is this statement.
- rg of `lean/WeilConjectures` for the item id: no match. Source searches for
  groupoid/restriction and IsGroupoidScheme did not find the theorem.
- rg of `lean/Sheaf` for groupoid restriction and `IsGroupoidScheme` found the
  groupoid definition, the existing Cohen–Macaulay restriction source/target
  helpers, fppf restriction in an Over category, and
  `PerfectFieldGroupoidImageClosure`. The last starts with an already perfect
  field and concludes a reduced image groupoid, not a restriction to a perfect
  field. The Over-category construction has different objects and grouping;
  the absolute helpers are the exact applicable definitions and are reused.
- rg in Mathlib, WeilConjectures and Sheaf for the two new declaration names
  `groupoidRestrictionProjection|exists_perfect_field_groupoid_restriction`:
  no matches before writing. The sole new Lean helper is the explicit coordinate
  projection belonging to this item. The repair adds an existing:true definition
  node for the three reused definitions; it adds no duplicate Lean construction.

Validation: prescribed scompile.py server compile of the complete module succeeded
in sandbox mode and library module mode (2.5 seconds each), with no errors or
unexpected warnings. Every variable and universe is explicitly bound, with
`set_option autoImplicit false`. All lines have at most 100 characters.

## Second reading by Q19

This is the author's second pass; the maintainer supplies the independent review
required by the dispatcher brief. I reopened the node and the complete module and
checked the five input compatibility equations, both restricted groupoid clauses,
the three middle-coordinate operation formulas, the three coordinates of a',
its five operation compatibilities, and both homeomorphism assertions. The only
index change is 1,2 to 0,1 in Fin 2. Reading the two pullback conditions shows that
the old composability proof `h₀` always follows from `h`, so that part does not
silently weaken the composition formula. Reading IsGroupoidScheme's source/target
fields shows that the endpoints of every operation are fixed, not left as
arbitrary maps. The final square is q₂ ∘ a' = a ∘ q₁, with the correct direction
of Lean composition. The existential g is fixed by its equality to Spec(algebraMap),
so no arbitrary base map or additional hypothesis is introduced. The mathematical statement matches the node. The independent review found H2:
the original dependency list cited the owning theorem node rather than a definition
node for the three plain helpers. This repair adds and cites the definition ownership
node described below; the Lean file and the mathematical statement are unchanged.


## New nodes

`def-sfb-groupoid-restriction` owns the existing declarations
`AlgebraicGeometry.groupoidSaturationMap`, `groupoidRestrictionSource`, and
`groupoidRestrictionTarget` in
`Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction`, with existing:true.
Its source is Stacks Tag 02VB (`lemma-restrict-groupoid`), restriction diagram.
For arbitrary schemes U,R,B and maps s,t,g, the statement defines W=B×_t R,
h=pr_R followed by s, R_B=W×_h B, source=last projection, target=first projection
followed by pr_B. These are exactly the three explicit definitions read in the
module. No groupoid law is required for these definitions. Empty schemes and
arbitrary unrelated s and t are allowed. No theorem is invoked to choose any data.
The definition uses the existing scheme and fibre-product nodes, cited exactly
in stmt_deps. No extra module or duplicate Lean definition is introduced.

Before creating the node, `rg --files dag/nodes` found no node of this id, and
`rg -l` for the three declaration names found only the Cohen–Macaulay theorem
node. `tools/blueprint_refs.py search 'groupoid restriction'` returned zero
blueprint matches. `tools/blueprint_refs.py ancestor` returned the inherited null
ancestor; the new blueprint record keeps that ancestor and prepends this item
to its via path. LeanSearch (source/target projections of restricted groupoids)
and LeanFinder (restriction by two endpoint pullbacks) returned fibre, open
restriction, and group-object base-change results, not these maps. Mathlib grep
for the three names found zero hits; source grep located the three existing
Sheaf definitions and no upstream copies. Actual complete search outputs are
in the new node's mathlib_searches.

## Repair of returned delivery 4d98c1e881c3

H2, the sole returned point: removed `lem-sfb-cm-groupoid-double-restriction`
from the item's stmt_deps, added `def-sfb-groupoid-restriction`, and supplied
that new definition node as an existing:true record of the three plain maps.
The item’s lean.note and this report now cite that definition ownership node.
The theorem statement and Lean module remain byte-identical to the returned
version. No definition is extracted from a theorem by choice. The current main
node was compared with the retained sandbox node: only lean and the single
added definition dependency differ; all mathematical node fields are preserved.
The prescribed delivery wrapper rebases the packet on the current server main.

Second reading of the repair: the new node's W,h,R_B,s_B,t_B formulas agree
with the existing definitions in the module, including the order of the two
endpoint projections and pullbacks. Its dependencies are exactly schemes and
fibre products, and it owns all three declaration names used by the item.
The original item still has its five input compatibilities, pinned spectrum
map, coordinate characterizations of all operations and a', both homeomorphism
clauses, and the final projection square. The repair changes only declaration
ownership and statement-dependency metadata, as requested by the reviewer.
