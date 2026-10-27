## Worker report

Item: lem-sfb-locally-separated-group-space-scheme. The module
`Sheaf.AlgebraicGeometry.LocallySeparatedGroupSpaceScheme` states
`AlgebraicGeometry.AlgebraicSpace.exists_groupScheme_of_locallySeparated`.
The theorem has exactly one postponed proof (`sorry`); no new definitions or
axioms are introduced. The accepted natural-language statement, dependency lists,
and proof plan are unchanged. Only the item's `lean` record is supplied.

The inherited BLOCKED ending concerned a stage-1 attempt to resplit an accepted
split. The current assignment is stage 2, the current queue lists this item at
stage 2, and the node has no Lean record. The 2026-10-22 stage-handoff paragraph
of coord/brief-stage2.md explicitly says to proceed in this situation. There is
no repair note for this item. We preserve Q39's accepted split in full.

Source checked: literature/stacks-project/spaces-more-groupoids.tex,
lemma-group-scheme-over-field-separated (Tag 08BH), including its preceding
paragraph on locally separated spaces being decent, and
lemma-group-space-scheme-locally-finite-type-over-k (Tag 0B8F).
The former gives separatedness and the latter scheme representability.
The separatedness and local finite type of the representing scheme, and the
transport of the group operations, are the last step of the accepted node proof.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`. The universe is explicit throughout;
  all schemes and group-valued sections have the same existing size convention
  as AlgebraicSpace, with no independent smaller test-object universe.
- G an algebraic space over Spec k: `G : AlgebraicSpace (Spec (.of k))` is
  exactly the recorded full subcategory of big-fppf sheaves with representable
  diagonal and a representable surjective étale scheme atlas.
- Given multiplication, identity and inversion, natural on test schemes and
  satisfying every group identity: `F : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u}`
  together with `e : F ⋙ forget GrpCat ≅ G.obj.obj`. Each value of F is a
  group and every restriction is a group homomorphism. Transport through e
  gives the original natural operations on G, including on nonreduced test
  schemes. Conversely the operations in the node define exactly such an F
  and e, without an additional geometric assumption. These are maps of the
  underlying algebraic-space sheaves, since algebraic-space morphisms are
  natural transformations, and the operations' sources are the corresponding
  products and terminal sheaf. A group-valued functor is an encoding of the
  given structure, not a new definition of group algebraic space.
- Locally of finite type on étale scheme charts: `hlft` quantifies over every
  `U : Over (Spec (.of k))` and every `a : yoneda.obj U ⟶ G.obj.obj`, requiring
  `IsEtale a → LocallyOfFiniteType U.hom`. Here `IsEtale` includes relative
  scheme-test representability, exactly as in def-trf-algebraic-space. This is
  the absolute-over-k chart version of local finite type in the node; it does
  not impose quasi-compactness, a finite atlas, or representability of G.
- Locally separated: `hsep` uses the existing `IsRepresentableWith` with the
  scheme property `fun _ _ p ↦ IsImmersion p.left` on
  `prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj)`. This is the diagonal into the
  relative product of the two presheaves on k-schemes. Its every scheme base
  change is represented by an immersion, exactly the stated assumption.
- Represented by a k-scheme with group-scheme morphisms satisfying the group
  identities: the existential `P : Grp (Over (Spec (.of k)))` bundles an
  actual k-scheme `P.X` with Mathlib's `GrpObj P.X`, including morphisms for
  multiplication, unit and inverse and all their diagram identities.
- Separated over k: `IsSeparated P.X.hom`, the existing scheme-morphism
  separatedness predicate. As Spec k is separated, this also gives absolute
  separatedness of the underlying scheme; no extra conclusion is intended.
- Locally of finite type over k: `LocallyOfFiniteType P.X.hom`.
- These are the originally specified group operations: the last conjunct is
  `Nonempty (yonedaGrp.obj P ≅ F)`. This is an isomorphism of group-valued
  functors, so all its components preserve multiplication, identity and
  inversion. Forgetting the groups and composing with e supplies the
  representing isomorphism with G. Thus the theorem retains the given group
  law and does not merely assert existence of an unrelated group structure.

Dependencies inspected and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs (the full class and
  docstring were read; this mathlib leaf needs no Lean record).
- def-trf-algebraic-space: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, and `IsEtale`.
  The category and the complete scheme-test signatures were read in source.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType`. We use its all-affine-pairs
  definition for the scheme structure morphisms in the chart hypothesis and
  conclusion, not the stronger conjunction with QuasiCompact.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp,
  `CategoryTheory.Grp` and `CategoryTheory.GrpObj`, specialized to Over Spec k
  as the record requires. Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
  supplies `yonedaGrp`, `yonedaGrpObj`, and the representability interface.
  Its full group-valued Yoneda construction and docstrings were read, as
  was WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, which documents
  precisely this specialization. No dependency repair is needed.
- lem-trf-space-fibre-products-etale-covers:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers,
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. All three full signatures and docstrings
  were read; the public import retains these foundations for the product
  operations and the étale chart hypothesis.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`, and the record's specified immersion
  notion `AlgebraicGeometry.IsImmersion` in Morphisms.Immersion. The latter
  module is imported publicly and exposes the former. The immersion class
  is the closed-then-open factorization notion stated by the node, not just
  a preimmersion.

Proof dependencies already stated are retained in imports: Mathlib's finite
 type, closed immersion and étale modules (also transitively public through
statement imports), its Yoneda API, AlgebraicClosure, and
Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource.
The four sfb prerequisites that currently have no Lean records are not imported:
locally-separated-rational-point-closed-immersion,
separated-group-space-geometric-scheme, group-finite-points-affine, and
geometric-affine-neighbourhood-scheme-descent (all with prefix `lem-sfb-`).
They are proof dependencies only; none is assumed in this theorem's statement.
The docstring reproduces all six accepted proof steps with their node citations,
including the atlas descent argument in steps 3 and 6.

Edge cases checked before writing and rechecked against the final signature:

- The trivial group is allowed. No hypothesis demands positive dimension or
  a nontrivial group law.
- The empty algebraic space cannot carry the supplied group-valued functor:
  its value at Spec k would be empty, whereas every group has an identity.
  This is the actual consequence of the given group structure, not an added
  nonemptiness hypothesis.
- An infinite constant group, such as the constant integer group scheme, is
  allowed: the theorem uses local finite type and never quasi-compactness.
- Nonreduced groups such as mu_p in characteristic p are allowed; there is
  no smoothness, reducedness, or characteristic-zero assumption.
- Imperfect fields and fields without algebraic closedness are included.
- The identity field extension in the first proof step and the empty finite
  list of geometric points in the fourth proof step require no extra binder
  restrictions. The final statement has no finite-list or extension choices.
- The representation is on every scheme over k and on its group operations;
  it is not restricted to field-valued or geometric points.

Searches for an existing statement and notions:

- msearch.py / LeanFinder: "A locally separated group algebraic space locally
  of finite type over a field is a separated group scheme". Eight hits on
  scheme separatedness and morphism composition; none represents an algebraic
  space by a scheme.
- msearch.py / LeanSearch: "A locally separated group algebraic space locally
  of finite type over a field is representable by a scheme". Eight hits:
  general local representability and existing scheme definitions and
  separatedness, no group algebraic space representability theorem.
- msearch.py / Loogle: "CategoryTheory.GrpObj, AlgebraicGeometry.AlgebraicSpace".
  Zero hits; AlgebraicSpace is project-specific and unknown to Mathlib Loogle.
- msearch.py / grep: "AlgebraicSpace|group_space|groupSpace" in Mathlib's
  AlgebraicGeometry. Zero hits.
- Direct rg in lean/WeilConjectures and lean/Sheaf, for this node id,
  `group_space|groupSpace|[Gg]roup algebraic space`, and the proposed full
  declaration name: no existing target theorem. The only group-space text
  match is the distinct DmPointStabilizer theorem; group-scheme theorems
  already presuppose a scheme. The same node id has no upstream attachment.
- Read the existing group-object and group-valued-Yoneda APIs in
  Mathlib.CategoryTheory.Monoidal.Grp and
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp rather than adding a private
  group-scheme or group-space definition.

No statement correction, missing notion, unusable dependency, or
STATEMENT-DISPUTED issue was found.

Validation: the prescribed scompile.py compiled this delivered file both as a
sandbox and under its final library module name, cleanly (1.8 s and 1.5 s).
No diagnostic commands remain in the delivered source. The node signature is
copied verbatim from the theorem keyword up to its assignment.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
