## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.DerivedCommutatorWordArbitraryField`
states `AlgebraicGeometry.exists_derived_commutator_word_arbitrary_field` with
one `sorry`. It introduces no definitions and proves nothing. The node's
statement and accepted proof are unchanged. The already landed definition node
`def-sfb-semisimple-group-scheme` and the new existing-definition record
`def-sfb-affine-pointed-word-map` are added to `stmt_deps`. The theorem
`lem-sfb-affine-pointed-map-generated-subgroup` is retained in `proof_deps`
and is not added to `stmt_deps`.

Source read: Milne, Algebraic Groups (2017), printed pp.129--130,
Definition 6.16, Propositions 6.17--6.18, Corollary 6.19, and Propositions
6.20--6.21. Corollary 6.19(a) gives arbitrary scalar extension; (b) gives
smoothness and connectedness, including after scalar extension. The affine
coordinate description and Proposition 6.20(a) give a positive finite word.
The latest blueprint direct-image proof (3) was also read; this is the
supporting derived-group input, not a restatement or change of that unit.

Hypotheses and clauses, in their order in the node:

- Any field k: `{k : Type u} [Field k]`, with no perfectness,
  characteristic, infinitude, or algebraic-closure assumption.
- G is a k-group scheme: `G : Grp (Over (Spec (.of k)))`. Its group object
  instance supplies precisely the multiplication, inverse and identity of
  `def-sc-group-scheme`.
- Smooth: `[Smooth G.X.hom]`.
- Geometrically connected: `[GeometricallyConnected G.X.hom]`. This is
  connectedness after all field extensions, including nonemptiness, rather
  than a rational-point or merely preconnected condition.
- Affine: `[IsAffine G.X.left]`.
- Finite type: `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Existence of the smallest closed subgroup carrying the commutator:
  `∃ (D : Grp (Over (Spec (.of k)))) (i : D ⟶ G),
  IsDerivedGroupScheme i.hom.hom ∧ ...`. The existing predicate is the
  conjunction of closed subgroup, factorization of the actual commutator
  morphism, and minimality by factorization of inclusions through EVERY
  closed subgroup containing that morphism. No normality, smoothness or
  finite-type condition is imposed on these competing subgroups.
- The actual commutator is the existing `groupSchemeCommutator G.X`, whose
  full definition is `fst * snd * fst⁻¹ * snd⁻¹`; it evaluates to
  xyx⁻¹y⁻¹ with the node's order and convention.
- Normality: `IsNormalSubgroupScheme i.hom.hom`, the existing predicate
  on every commutative k-algebra, including nonreduced algebras.
- Smooth and geometrically connected D:
  `Smooth D.X.hom ∧ GeometricallyConnected D.X.hom`.
- The ensuing affine and finite-type conjuncts for D express properties
  already forced by its closed immersion into affine finite type G; they
  retain the interface required by the quotient theorem.
- A positive finite commutator word with dense image:
  `∃ (n : ℕ) (w : (∏ᶜ fun _ : Fin (n + 1) ↦ G.X ⊗ G.X) ⟶ D.X),
  w ≫ i.hom.hom = affinePointedWordMap (groupSchemeCommutator G.X) n ∧
  DenseRange w.left`. Here r = n + 1, so precisely all integers r ≥ 1
  occur. The product has r ordered pairs, canonically the indicated power
  G^(2r). `affinePointedWordMap` is the ordered `List.ofFn ... .prod`
  of the r projection maps followed by the commutator. Products in the
  category `Over (Spec k)` are fibre products over k. `DenseRange w.left`
  refers to ALL underlying topological points, not only k-rational points.
- Every extension field K/k: `(∀ (K : Type u) [Field K] [Algebra k K], ...)`.
  Applying `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))`
  and then `.mapGrp.map i` retains the actual base-changed inclusion and
  group structure. `IsDerivedGroupScheme` on this inclusion says exactly
  that D_K is the smallest closed subgroup carrying the commutator of G_K;
  thus it identifies it with D(G_K) as a subgroup, without choosing another
  representative and an arbitrary isomorphism. The scheme and extension
  use the same ambient universe u, as in the recorded geometric and
  quotient interfaces; u is arbitrary and no independent smaller universe
  makes testing vacuous.
- Every homomorphism to a commutative affine finite type group:
  `∀ (C : Grp (Over (Spec (.of k)))) [IsCommMonObj C.X]
  [IsAffine C.X.left] [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]
  (f : G ⟶ C), i.hom.hom ≫ f.hom.hom = 1`. The group unit on this Hom
  type is the identity-valued morphism, so this is triviality on D as a
  morphism of schemes, not only on rational points.
- The represented fppf quotient is commutative: the existential Q and q
  satisfy `IsAffine Q.X.left`, `LocallyOfFiniteType Q.X.hom`,
  `QuasiCompact Q.X.hom`, `IsFppfGroupQuotient i q` and `IsCommMonObj Q.X`.
  The quotient predicate is exactly the recorded dependency's kernel
  square, local surjectivity for the actual fppf topology, sheaf condition,
  torsor isomorphism, and universal sheafification of the coset presheaf.
- The commutative and trivial cases: `IsCommMonObj G.X →
  IsIso (toUnit D.X)`. The monoidal unit in `Over (Spec k)` is the
  identity object Spec k. This is a scheme isomorphism through the
  canonical structure map, not just a singleton assertion for points.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  with their complete definitions and docstrings. It also documents the
  recorded Mathlib `CategoryTheory.GrpObj`, `Grp`, `IsCommMonObj` and
  `IsMonHom` interpretation; the group-object and bundled-group source
  signatures in `Mathlib.CategoryTheory.Monoidal.Grp` were read.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `groupSchemeCommutator` and `IsDerivedGroupScheme`, including the
  unrestricted field binder on these two declarations (the later
  semisimplicity predicate's algebraic-closure assumption is not inherited).
- `Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup`:
  `affinePointedWordMap`, its explicit ordered-product definition, and the
  generated-subgroup theorem and quotient-spectrum construction. The word
  helper is public because it occurs in the statement; the other
  declarations are the existing proof input and are not duplicated.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient` and `affine_normal_quotient_geometry`. Both full
  definitions/signatures and docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `GeometricallyConnected`, the geometric connectedness component of
  `def-pc-geometrically-irreducible`. The node's broader integral module
  already comes through the pointed-map import. `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic` includes nonemptiness.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`
  and projections, realized here by products and `Over.pullback`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` supplies the canonical
  group-object pullback functor.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` for extension fields;
  the `Field` Mathlib leaf supplies `def-weil-field`.

Every stated proof dependency's module is imported, publicly when its
notions occur in the signature, plainly otherwise: the proper/smooth
base-change module, smooth composition, geometric reducedness of smooth
schemes, geometric connectedness of products, generated subgroups,
`Mathlib.AlgebraicGeometry.Group.Smooth`, affine pullbacks, algebraic
closures, faithfully flat tensor base change, and faithfully flat
surjectivity on spectra. The proof dependency
`lem-sfb-pointed-word-kernel-stabilization` currently has no recorded
Lean declaration or Mathlib match, so its proof import is omitted; no
statement depends on such a declaration, and the docstring explicitly
retains this DAG proof step for stage 3.

Edge cases checked before writing: G = 1, any commutative smooth
geometrically connected affine group (including G_a and tori), r = 1,
finite fields, imperfect fields of positive characteristic, and
transcendental extensions. The trivial group has the length-one map
Spec k → Spec k; a commutative group's word is identity valued and its
D is the identity subgroup. No k-point generation claim is made: that
would fail over general fields. The empty scheme cannot satisfy the
group-object hypotheses. General nonreduced test algebras remain in
normality and closed-subgroup minimality. No statement fault or dispute
was found; no statement correction or dependency repair is needed.

Searches made (all before introducing a declaration):

- `msearch.py ... leanfinder` query "The derived subgroup of a smooth
  geometrically connected affine group scheme exists and is smooth with
  a dominant finite commutator word": 8 hits, including `derivedSeries`,
  `derivedSeries_one`, `commutator_def` and the absolute Galois commutator
  closure. These concern abstract groups and do not state this theorem.
- `msearch.py ... loogle` query `"commutator", "Group"`: 12 hits,
  including `Subgroup.commutator` and centralizer/normality lemmas.
  No affine group-scheme theorem.
- `msearch.py ... grep` query `derivedSubgroup|commutator|wordMap`,
  subdirectory `AlgebraicGeometry`: 5 hits, all in Mathlib's
  `Group/Abelian.lean`, about commutativity of proper groups.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for
  `commutatorWord|commutator_word|IsDerived|derivedSubgroup|derived_subgroup|pointedWord|wordMap`
  found the semisimple module's predicate and the algebraically closed
  `exists_smooth_connected_derived_subgroup`; its full statement was
  read. The latter requires an algebraically closed field and does not
  give this node's field-extension/finite-word/quotient package. This
  search also identified the existing predicate used here.
- Reading the generated-subgroup node's `lean` record and module found
  `affinePointedWordMap`, avoiding a second word-map definition.
- `rg -n 'lem-sfb-derived-commutator-word-arbitrary-field'
  lean/WeilConjectures` returned no match.
- The named repair-note path does not exist for this item.

Validation: prescribed `scompile.py N7
lem-sfb-derived-commutator-word-arbitrary-field <module>` passed both
its sandbox and named-library compilation (2.3 s and 2.4 s), with no
errors or warnings. Every variable/universe is explicitly bound and
`set_option autoImplicit false` is present. The only theorem proof is
`sorry`; there are no definitions with postponed data.

## Second reading by N7

This is a second pass by the same dispatched worker; the brief forbids
starting other agents. Independent review is left to the maintainer,
who reads this delivery. In this pass I reopened the node, the final
Lean file, and the three reused group-scheme modules. I checked all
hypotheses and each clause against the mapping above. In particular:
the existing derived predicate quantifies over every closed subgroup,
not only smooth ones; the commutator convention is xyx⁻¹y⁻¹; the word
uses a list product with r = n + 1, retaining the positive-length edge;
base change tests the pulled-back inclusion itself; finite type is
present on the commutative target; the quotient is the actual fppf
presentation; and triviality is the canonical isomorphism to Spec k.
No mismatch was found and no mathematical statement changed in the
second pass. All source imports are in module mode, and no file-local
notation, private abbreviation, additional axiom, or proof is introduced.


## Repair of returned delivery b7faaa8c0ec2

H2 was valid: the previous delivery added a theorem node as a statement
dependency just to use its plain helper definition. The helper has real data
and is not a choice from that theorem. I removed the added
`lem-sfb-affine-pointed-map-generated-subgroup` entry from `stmt_deps`,
retained it in `proof_deps`, and added the definition node
`def-sfb-affine-pointed-word-map` with an `existing: true` binding to
`AlgebraicGeometry.affinePointedWordMap`. The Lean file and full theorem
signature are byte-identical to the returned delivery. This is a dependency
metadata repair, not a statement correction. Compared with current main,
the item's only field changes are `lean` and the two definition additions
to `stmt_deps`; no other item or dependency fields were edited.

The reviewer's note about `IsFppfGroupQuotient` is respected: its owning
quotient theorem is already a statement dependency on the base, so its
existing predicate record is reused without any additional node or repair.

## New nodes

`def-sfb-affine-pointed-word-map` records the existing positive ordered
word-map construction, with source Milne, Section 2h, the displayed map
preceding Proposition 2.46, printed pp.54--55. Its Lean binding is
`Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup` /
`AlgebraicGeometry.affinePointedWordMap`, `existing: true`; no module or
new Lean declaration is added. The recorded signature was extracted verbatim
from the existing source. The definition only needs a field, X a k-scheme,
G a k-group scheme, a k-morphism φ, and n : ℕ. Its index means n + 1
factors, in increasing order. The formula itself needs no affine,
finite-type, chosen-point or homomorphism assumptions. These are needed
elsewhere for properties of the generated subgroup, not to define the word.
The new node's definition dependencies cite exactly the five references in
its self-contained statement. At n = 0 this is the length-one word;
there is no empty product ambiguity. Noncommutative targets retain the
order of the list product.

Searches for this new record: `blueprint_refs.py search word` found 14
blueprint matches, none the group-scheme word-map definition;
`blueprint_refs.py ancestor` confirmed the inherited null blueprint ancestor
for this created supporting item. `rg` of DAG nodes found only the helper
record on the generated-subgroup theorem and no existing definition node
for it; `rg` in WeilConjectures and Sheaf found its sole definition in the
module above. LeanSearch for "Ordered product word morphism from a finite
power of a scheme to a group scheme" returned 8 abstract word/product or
order-hom hits, without a scheme word-map construction. LeanFinder for
"Word morphism of schemes obtained by multiplying the images of the
projections in an internal group" returned 8 group-object/point/projection
hits, including `CategoryTheory.Hom.mul_def`; these support the general
product mechanism but do not define this finite word. Mathlib grep for
`wordMap|WordMap|pointedWord|word.*morphism` in AlgebraicGeometry returned
0 hits. The raw search output is recorded in `mathlib_searches`, including
the project and DAG grep output. This record reuses existing code rather
than making a second definition of the notion.

Second reading of the repair: reopened the final item and definition records,
the unchanged Lean file, and the existing word-map body. The definition
record's assumptions and index agree exactly with that body. Its source
formula is the displayed ordered product on Milne p.54. The consumer cites
the definition; the generated-subgroup theorem remains exclusively a proof
dependency added by neither the new record nor the repaired statement.
The mathematical clause checks in the earlier second reading still apply.
