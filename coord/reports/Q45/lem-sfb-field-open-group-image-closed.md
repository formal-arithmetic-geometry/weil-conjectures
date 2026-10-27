## Worker report

The module `Sheaf.AlgebraicGeometry.FieldOpenGroupImageClosed` states
`AlgebraicGeometry.isClosed_range_of_isMonHom_of_isOpen`, with its only proof
`sorry`. It introduces no definitions. The node is changed only in `lean`.

Source read: `literature/stacks-project/groupoids.tex`, lines 857–878,
Tag 047S (`lemma-open-subgroup-closed-over-field`). The source states exactly
that the open image of a morphism of group schemes over a field is closed.
There is no finite-type or separation hypothesis. The theorem docstring records
the node's two-step proof: identify the groups with absolute groupoid schemes
on Spec k, then apply `lem-sfb-field-groupoid-open-image-closed` (Tag 04Q6).

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`, with `u` explicitly declared.
- Schemes P and Q over Spec k: `{P Q : Over (Spec (CommRingCat.of k))}`.
  The structure maps are `P.hom` and `Q.hom`, and the underlying schemes are
  `P.left` and `Q.left`. This is the recorded specialization of the group's
  dependency, also documented in upstream `GroupScheme/Defs.lean`.
- Group operations satisfying the diagrams: `[GrpObj P] [GrpObj Q]`.
  Its inherited `MonObj` gives multiplication, unit, associativity and unit
  diagrams; `GrpObj` adds inverse and its two cancellation diagrams.
- A group-scheme homomorphism u: `(f : P ⟶ Q) [IsMonHom f]`.
  Being an Over morphism asserts compatibility with the structure maps.
  `IsMonHom.one_hom` and `IsMonHom.mul_hom` assert compatibility with unit
  and multiplication; inverse compatibility follows automatically from
  `CategoryTheory.GrpObj.inv_hom`. Thus no inverse hypothesis was omitted.
- The point image is open: `(hopen : IsOpen (Set.range f.left))`.
  `Scheme.Hom` coerces to its underlying map of point spaces, definitionally
  `f.left.base`; `Set.range` is precisely u(|P|).
- That same point image is closed: `IsClosed (Set.range f.left)`.
- The final sentence of the node imposes no further conditions: the signature
  contains no finite-type, smoothness, separation, affineness, injectivity or
  surjectivity assumption. It does not assert a closed immersion.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, lines 171–180.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, lines 36–47;
  `Scheme.Hom`, lines 72–75; `Spec`, lines 469–472, and `Spec.map`, lines 478–480.
  The defining module is publicly exposed by
  `Mathlib.AlgebraicGeometry.Pullbacks`, whose lines 709–715 provide the
  Cartesian monoidal structure on `Over S` needed for group objects.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, lines 41–48,
  with `GrpObj.inv_hom`, lines 322–326. Its public monoid import supplies
  `CategoryTheory.IsMonHom` (`Monoidal/Mon.lean`, lines 211–216).
- Proof dependency `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  `AlgebraicGeometry.IsGroupoidScheme`; its full structure and docstring were
  read. Imported without `public`, as a proof dependency. The other proof
  dependency `lem-sfb-field-groupoid-open-image-closed` has no Lean binding
  in the supplied repository and therefore no module to import yet. It is
  named in the theorem's proof docstring; no proof prerequisite is added as
  a hypothesis and no duplicate groupoid statement is created.

Edge cases checked before writing: arbitrary characteristic, imperfect fields,
noncommutative and nonreduced groups, non-finite-type groups, the trivial group,
and morphisms with kernel or proper image are all admitted. An empty scheme
cannot be a group scheme over the nonempty Spec of a field because of its unit,
so no added nonemptiness hypothesis is needed. The image of an identity or a
surjective map is the whole target and the claim specializes correctly.
Nothing identifies the point space of a group scheme with an ordinary
 topological group. Schemes and the base field are in an arbitrary common
universe `u`, as in the project's recorded group-scheme interface; enlargement
of that universe is unrestricted.

Searches run (2026-10-24):

- `msearch.py ... leanfinder "The image of a homomorphism of group schemes over
  a field is closed if it is open"`: eight results, including ordinary
  automorphism-group closed range, universally closed scheme maps and locally
  closed immersion ranges; none is this theorem.
- `msearch.py ... leansearch "The image of a group scheme homomorphism over a
  field is closed when it is open"`: eight results, including scheme-theoretic
  image, immersion ranges and universally closed maps; none matches.
- `msearch.py ... loogle "GrpObj, IsClosed, Set.range"`: zero results with the
  diagnostic `unknown identifier 'GrpObj'`. This Loogle query was inconclusive;
  local source inspection resolved the names.
- `msearch.py ... grep "open.*subgroup|[Ii]sClosed.*[Rr]ange"
  AlgebraicGeometry/Group`: one result in Mathlib's Abelian.lean, line 97,
  closed range of a proper map, not this statement.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry/GroupScheme` for open subgroup,
  open image and closed range found
  `AlgebraicGeometry.isClosed_range_of_isMonHom` in `Basic.lean`. Its full
  signature/docstring, lines 870–884, require source finite type and target
  locally finite type, so it is not a match for arbitrary open images.
- `rg` for the node id in `lean/WeilConjectures` found no binding. Searches
  for the proposed name in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` found no clash. Broader open-image/closed-range
  searches of both project source roots found no exact match; unrelated open
  immersions and clopen ranges use additional hypotheses.

No statement dispute, node correction, dependency repair or new node is needed.
`scompile.py Q45 lem-sfb-field-open-group-image-closed <module>` passed in both
sandbox and library module modes (1.4 and 1.5 seconds), without errors or
unexpected warnings. Every variable is explicitly bound and `autoImplicit` is
false.

## Second reading by Q45

Author's second reading for direct delivery; the maintainer performs the
independent review. I reopened the node and the final module and compared the
field, the two relative schemes, both group structures, the homomorphism, the
openness assumption and the closedness conclusion. The same `Set.range f.left`
occurs in assumption and conclusion. The Over morphism is over the identity
of the shared Spec k. The recorded `GrpObj`/`IsMonHom` interface supplies all
three operation compatibilities, with inverse compatibility automatic as
checked in `GrpObj.inv_hom`. No commutativity or geometric finiteness assumption
has slipped in. The node's proof is reproduced step by step in the docstring.
The statement is the point-image claim rather than an immersion claim. No
mismatch was found and no correction was made. There are no new nodes or
dependency modules to review.
