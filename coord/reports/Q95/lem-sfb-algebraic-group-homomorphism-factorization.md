## Worker report

The delivery states `AlgebraicGeometry.algebraicGroup_homomorphism_factorization`
in `Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization`.
It has one theorem, with proof `sorry`, and introduces no definitions or helper
axioms. The natural-language statement and all proof steps are unchanged.
The existing definition `AlgebraicGeometry.IsFppfGroupQuotient` is used rather
than creating another quotient notion. Its new definition node,
`def-sfb-fppf-group-quotient-presentation`, and the existing definition nodes
`def-pc-fppf-site` and `def-weil-pbc-sheafification` are added to `stmt_deps`.
The new node records the exact existing predicate with `existing: true`.
It is defined over arbitrary base schemes and arbitrary group schemes;
the affine-quotient theorem is not a statement dependency.

Sources read: the node and all statement dependency records and their recorded
interfaces; `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, the upstream
cartesian group-object kernel implementation; the full definition and docstring
of `IsFppfGroupQuotient`; Mathlib's morphism classes and group-object constructors.
The local Milne PDF was opened with pdftotext: Theorem 5.39, printed p.108,
Theorem 5.28 and the following paragraph, Corollary 5.27, printed p.105.
They give precisely the faithfully flat quotient by the kernel, quotient group
law and closed immersion used here. The sheaf clause follows the node's
Example 5.71 interpretation, rendered by the existing quotient definition.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
|---|---|
| Field k | `{k : Type u} [Field k]` |
| k-group schemes G,H | `G H : Grp (Over (Spec (.of k)))`; `Grp.grp` supplies their group-object structures |
| Separated G,H | `[IsSeparated G.X.hom]`, `[IsSeparated H.X.hom]` |
| Finite type G,H over k | `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism |
| k-group-scheme homomorphism f | `f : G ⟶ H`, a bundled group-object morphism, whose underlying over-map is `f.hom.hom` |
| Scheme-theoretic kernel N | `GrpObj.ker f.hom.hom`, the existing pullback of f and the unit, not a reduced subscheme or a kernel on rational points alone |
| Closed subgroup N of G | `IsClosedSubgroupScheme (GrpObj.kerι f.hom.hom)` |
| Normal subgroup N of G | `IsNormalSubgroupScheme (GrpObj.kerι f.hom.hom)` |
| N finite type | `LocallyOfFiniteType (GrpObj.ker f.hom.hom).hom` and `QuasiCompact` of that same map |
| Existence of k-group scheme I | `∃ I : Grp (Over (Spec (.of k)))` |
| I separated and finite type | `IsSeparated I.X.hom ∧ LocallyOfFiniteType I.X.hom ∧ QuasiCompact I.X.hom` |
| Homomorphisms q:G→I, i:I→H | Bundled morphisms `q : G ⟶ I`, `i : I ⟶ H` |
| f=i∘q | `q ≫ i = f`, in Lean's diagrammatic composition order |
| i closed immersion | `IsClosedImmersion i.hom.hom.left` |
| q faithfully flat | `Flat q.hom.hom.left ∧ Surjective q.hom.hom.left`, the exact scheme conditions specified in the node |
| q finitely presented | `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` on `q.hom.hom.left`, all three explicitly |
| q has the same scheme-theoretic kernel N | The first conjunct of `IsFppfGroupQuotient (Grp.ofHom (GrpObj.kerι f.hom.hom)) q` is the cartesian square with the original inclusion, q, and the unit of I |
| I with q identifies the fppf quotient G/N | The remaining conjuncts of that same existing predicate, detailed below |

The quotient predicate uses the specified inclusion N→G and the specified q.
Its torsor isomorphism is G×N→G×_I G with projections g and gn. Its pointwise
coequalizer of the Yoneda maps g and gn is exactly the presheaf of right cosets.
It supplies a map ηq from that coequalizer to `yoneda.obj I.X` satisfying
`coequalizer.π _ _ ≫ ηq = yoneda.map q.hom.hom`. Thus the identification retains
q, rather than asserting an unrelated abstract isomorphism. The represented
presheaf is required to be an fppf sheaf, and for every sheaf Z precomposition
with ηq is bijective on natural transformations. This is precisely the
sheafification universal property of `def-weil-pbc-sheafification`.
Its local-surjectivity clause uses `Scheme.fppfTopology.over (Spec (.of k))`.
The extra presentation data in this existing predicate are equivalent to the
node's kernel-and-quotient assertion: a homomorphism with this kernel has
(g,n)↦(g,gn) as its kernel-pair isomorphism; a flat surjective locally finitely
presented q is itself an fppf cover. They impose no additional hypothesis.

On affine tests Spec R the pointwise coequalizer is G(R)/N(R), including
nonreduced R. The big fppf site's affine basis gives the same sheafification as
the algebra site: every scheme has an affine open cover, and covers of an
affine admit finite affine refinements (the recorded proof dependency
`lem-pc-fppf-affine-refinement`, whose module is imported). Between affine
schemes the maps are quasi-compact and quasi-separated automatically, so local
finite presentation is finite presentation. These are the coverings in the
node's algebra formulation. No algebra-closure or rational-point replacement
is made. The existing predicate quantifies over `Type u`-valued sheaves,
the universe of the Hom sets on `Over (Spec k)`; it expresses the universal
property directly and does not assume existence of a large-site sheafification
functor in a smaller universe.

Dependency declarations used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Grp.ofHom` and its
  bundled homomorphisms; this is the group-scheme node's recorded encoding.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`:
  `GrpObj.ker`, `GrpObj.kerι`; these are actual pullbacks. The module is
  imported directly as the recorded kernel proof dependency.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`; their inherited
  `IsSubgroupScheme` quantifies over every commutative k-algebra in the same
  universe, and normality is normality of the pointwise range.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded proper/separated
  interface, with `IsSeparated` from its separated-morphism import. Properness
  itself is not a hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `QuasiCompact` is the recorded companion class from Morphisms.QuasiCompact.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the recorded
  `pullback`, `pullback.fst` interfaces underlying the kernel construction.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`; its definition has no affine or finite-type premise.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`: its slice site, used inside the existing
  quotient predicate.
- `Mathlib.CategoryTheory.Sites.Sheafification`: the recorded universal
  property, used by the predicate's bijective precomposition clause.

All recorded proof-dependency modules available in the read repository are
imported, including Mathlib compactness, Precoverage, Fpqc, Yoneda,
FppfAffineRefinement and Sheafification. The two statement nodes
`lem-sfb-algebraic-group-homogeneous-quotient` and
`lem-sfb-algebraic-group-monomorphism-closed-immersion` have neither a Lean
record nor a Mathlib match in the read repository, so there is no module for
them to import. They are only proof dependencies, and no hypothesis about their
conclusions is added to this statement. Stage 3 can use their future modules.

Edge cases checked mathematically before finalization:

- The identity homomorphism: N is the unit subgroup and I=G, q=id, i=id.
- The trivial homomorphism: N=G and I is the unit group; its unit inclusion
  in H is closed and the structural map G→Spec k is faithfully flat.
- G or H trivial is included by these two cases; a group scheme over a field
  cannot be empty because it has its identity section.
- Infinitesimal kernels: Frobenius of G_a in positive characteristic has
  kernel α_p. No reducedness, smoothness or etaleness is imposed on N, and no
  assumption excludes this example or imperfect fields.
- Nonaffine examples, such as homomorphisms of abelian varieties, are retained:
  there is no `IsAffine` binder anywhere in the theorem or quotient predicate.
- Noncommutative and disconnected group schemes are retained; the kernel's
  normality is stated rather than replacing all groups by commutative groups.
- Zero test algebra: its spectrum is empty and all point groups are trivial;
  the coset and sheafification formulations still include this test.
- The explicit universe u is shared by k and its schemes and test algebras;
  no independent too-small universe makes a test-algebra quantifier vacuous.

Searches (2026-10-24; exact launcher responses are in searches.jsonl):

- msearch leanfinder: "A homomorphism of separated finite type group schemes
  factors as a faithfully flat finitely presented quotient by its kernel
  followed by a closed immersion". Eight hits: closed-immersion lift,
  flatness and separatedness results, no group-scheme homomorphism theorem.
- msearch loogle: "GrpObj.ker, IsNormalSubgroupScheme, presheafToSheaf".
  No hits; Loogle does not know the upstream identifier GrpObj.ker. The
  declarations were located and read directly in the upstream source.
- msearch grep: "quotient|Quotient|[Kk]ernel|factor" in
  AlgebraicGeometry/Group. Three hits in affine/abelian group files, no match.
- msearch leansearch: "Homomorphism theorem for finite type algebraic group
  schemes with fppf quotient by the kernel". Eight hits, all abstract
  group/ring quotient isomorphism results, not the scheme theorem.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, homomorphism
  factorization, kernel and fppf quotient terminology. Found consumers of the
  item, the existing upstream kernel/subgroup interfaces, and the general
  `IsFppfGroupQuotient` above. Compared also the weaker quotient predicate in
  SolvableGroupStructure and the additive-specialized quotient construction;
  reused the general predicate instead of either specialized construction.
- Exact declaration-name search in Mathlib, WeilConjectures and Sheaf found
  no existing `algebraicGroup_homomorphism_factorization`.

No mathematical statement correction or dependency modules are needed.
The metadata ownership repair adds the one definition node described below.
No STATEMENT-DISPUTED issue was found. The single delivered theorem is the only
postponed proof; it has the matching original DAG node and a six-step proof
docstring. No proof has been supplied in this stage.

Validation: scompile.py compiled the module in both sandbox and library modes
without errors or warnings (4.1 s and 2.3 s respectively). The required delivery
dry run and final delivery are run after the record and report are written.

## Second reading by Q95

The dispatcher explicitly prohibits starting other agents; this is the author's
second pass, not a claimed independent review. The maintainer's independent
review remains the acceptance check. I reopened the module, the node, and the
full existing quotient definition and matched them using the table above.
I checked especially that the four kernel conjuncts precede the existential,
that finite presentation includes both global conditions, that G and H are
separated but not proper or affine, and that the quotient's unit equation uses
the same q as the factorization. The kernel square uses the original kernel
inclusion via `Grp.ofHom`, not an arbitrary normal subgroup. The existing
predicate's torsor and local-surjectivity clauses are consequences of this
same quotient assertion, and introduce no restriction. No mismatch or edit
was required in this second pass. The Lean record copies the complete theorem
signature verbatim, and only lean plus the three permitted definition statement dependencies
change in the item node copy.

## New nodes

`def-sfb-fppf-group-quotient-presentation` registers the exact existing
`AlgebraicGeometry.IsFppfGroupQuotient` from
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`.
Its `lean.declarations` contains only that definition and `existing` is true;
no Lean definition is moved, copied or added. Source: Milne 5.24--5.27 and
5(j), especially 5.68 and 5.71. I reread these source passages and the entire
definition at lines 60--77. The definition is general over a base scheme;
the node states its kernel square, local surjectivity, represented sheaf,
torsor with the actual projections, pointwise coequalizer and universal unit.
The definition dependencies are the scheme, group-scheme, fibre-product,
fppf-site and sheafification nodes. The universal property quantifies over
Type u valued sheaves, matching the common test-object universe.
The empty base and identity/trivial quotient presentations are allowed.
The predicate imposes no affine, smooth, finite-type or field hypothesis.

New searches run in this repair (all 2026-10-24, exact launcher results in
searches.jsonl and the node's mathlib_searches): LeanSearch, “A group scheme
quotient presentation is the fppf sheafification of the right coset presheaf
with specified kernel and quotient map” (8 abstract quotient/module
presentation hits); LeanFinder, “Presentation of the fppf quotient of a group
scheme by a kernel with canonical torsor isomorphism and sheafification
universal property” (8 Galois/module presentation hits); msearch grep,
“IsFppfGroupQuotient|fppf.*quotient|coset.*presheaf” in AlgebraicGeometry
(0 Mathlib hits). Direct rg over WeilConjectures and Sheaf finds the exact
existing definition in AffineNormalQuotientGeometry.lean:60. DAG search
finds theorem consumers and specialized definition nodes but no definition
node owning this declaration. blueprint_refs.py search “fppf quotient”
returns 0 matches. Its ancestor command reports the inherited null ancestor;
the new node retains that recorded ancestor and prepends this item to via.
The inherited place identifies det-thm-sf-ctf-stability-direct-images proof (3),
as the prior maintainer review notes.

## Repair of returned delivery

H2 (returned head 2c4ce78e04a2): replaced the item's added theorem dependency
`lem-sfb-affine-normal-quotient-geometry` with the new definition node
`def-sfb-fppf-group-quotient-presentation`. Kept `def-pc-fppf-site` and
`def-weil-pbc-sheafification`. The theorem node and its source module are
unchanged. The delivered HomomorphismFactorization.lean is byte-for-byte
unchanged from the saved packet. No other numbered return points were given.

Second reading of the repair by Q95: reopened the existing definition and
matched all five conjunctions with the new node, including the exact torsor
coordinates and the condition that the sheafification unit composes to h_q.
The new lean.statement is the exact def signature and its declarations list
contains only IsFppfGroupQuotient. The item's statement, Lean signature,
proof and proof dependencies are unchanged; compared with current main, its
only changed fields are lean and stmt_deps. The original hypothesis and edge
case review above still applies. The initial saved-packet dry run passed as
78cf1d7533a; it did not detect the semantic ownership issue, so this repair
addresses the maintainer's explicit H2 instruction before redelivery.

Repair validation: scompile.py compiled the unchanged theorem module cleanly
in sandbox and library modes (4.1 s and 2.3 s). The first repaired-packet
dry run required the standard empty import_flags field on the new node;
added that field and reran the prescribed preflight wrapper.
