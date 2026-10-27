## Worker report

The module `Sheaf.AlgebraicGeometry.FlatSubgroupIdentityNeighbourhoodOpen` states
`AlgebraicGeometry.isOpenImmersion_of_flat_subgroup_identity_neighbourhood`.
Its only proof is `by sorry`; it introduces no definitions. The node's mathematical
statement, dependencies and proof remain unchanged. No new nodes or dependency repairs
are needed. Automatic implicit variables are disabled explicitly.

Clause-by-clause correspondence:

| Node data or hypothesis | Lean rendering |
| --- | --- |
| An arbitrary scheme S | `{S : Scheme.{u}}`, with explicit universe `u` |
| H and G are schemes over S | `(H G : Over S)`; `H.left`, `G.left` are the schemes and `H.hom`, `G.hom` their structure maps |
| Group objects, including identity, multiplication and inverse with all group laws | `[GrpObj H] [GrpObj G]` in the cartesian monoidal category `Over S` |
| An S-group homomorphism i | `(i : H ⟶ G) [IsMonHom i]`; its underlying scheme map is `i.left` |
| i is a closed immersion | `[IsClosedImmersion i.left]` |
| H → S is flat | `[Flat H.hom]` |
| H → S is locally of finite presentation | `[LocallyOfFinitePresentation H.hom]` |
| A scheme V over S and an open immersion v:V → G | `(V : Over S) (v : V ⟶ G) [IsOpenImmersion v.left]` |
| e_V:S → V over S | `(eV : 𝟙_ (Over S) ⟶ V)`; the tensor unit is literally `Over.mk (𝟙 S)` |
| b:V → H over S | `(b : V ⟶ H)` |
| v e_V = e_G | `(heV : eV ≫ v = MonObj.one (X := G))` |
| i b = v | `(hb : b ≫ i = v)` |
| Conclusion: i is an open immersion | `IsOpenImmersion i.left` |
| No smoothness or connectedness assumptions | There are no such binders, and no assumption on the structure map of G |

Composition `≫` is in diagrammatic order. Equality in `Over S` is equality of its
underlying scheme maps, by `Over.OverMorphism.ext`, since the over-base proofs are
propositions. Consequently the two displayed equalities are exactly the node's two
scheme-morphism equations. Encoding the given witnesses as theorem arguments expresses
the conditional assertion for every specified neighbourhood and witnesses, equivalently
to an implication from their existence.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 42 and 74. Its local-affine definition and
  underlying locally ringed space are the standard scheme notion.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, line 45: closed embedding
  and surjective stalk maps.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, line 42; the stalk interpretation is
  `Flat.iff_flat_stalkMap`, line 106.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, line 45, the affine-local
  finite-presentation condition.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, line 38, the usual locally ringed space
  open immersion.

The group-object declarations are the existing `CategoryTheory.GrpObj` in
`Mathlib.CategoryTheory.Monoidal.Grp`, line 43; `MonObj.one` and `MonObj.mul` in
`Mathlib.CategoryTheory.Monoidal.Mon`, lines 75 and 77; and `IsMonHom`, line 213,
which preserves unit and multiplication. In a group object such a map preserves
inverse, as established in the same group-object API. The `Over` cartesian monoidal
structure in `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`, lines 33–38, has unit
`Over.mk (𝟙 S)` and tensor product the fibre product. `Mathlib.AlgebraicGeometry.Pullbacks`
supplies scheme pullbacks and the global cartesian structure on `Over S`. The existing
upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents precisely this
representation over a field; this statement uses the general Mathlib representation
over an arbitrary scheme and does not impose the field specialization.

The proof docstring carries all five steps of the node, with the node ids and Stacks
tags: shear and base change, flat/lfp composition, equality of the open image with H,
faithfully flat local stalk injection together with closed-immersion surjection, and
the stalk criterion for the structure sheaf. Private proof imports provide the
recorded Mathlib proof dependencies: pullbacks, étale morphisms, quasi-separated
morphism permanence, universally open morphisms, faithfully flat algebras and sheaf
stalks. Public imports provide the five statement dependencies and the group-object
and over-scheme interfaces.

Source check: opened Conrad's [Reductive group schemes](https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf),
Theorem B.3.2(2), printed pp. 288–290, especially the final argument on p. 289
(PDF page index 288). It motivates the group-translation argument; the paper does
not state this general arbitrary-base lemma. This distinction is already explicit
in the node's `source` and `proof_origin`, and is retained in the module docstrings.
The actual general five-step argument is the reviewed agent proof in the DAG;
no source-based statement correction is required.

Edge cases checked before writing:

- Empty S is permitted. Over the empty base the total schemes are empty; no
  nonemptiness binder excludes this case.
- If S is nonempty, the identity sections already supply base points in the group
  fibres. The neighbourhood is not assumed nonempty separately: `eV` provides
  exactly the required section.
- H = G and i the identity is included, taking V = G, v and b the identity, and
  eV the group identity section.
- The trivial group and disconnected groups/bases are included. No commutativity,
  affineness, separatedness of either structure map, Noetherianness, quasi-compactness,
  characteristic, reducedness or smoothness is imposed.
- Nilpotent group schemes are allowed. For example the identity subgroup in alpha_p
  has the same underlying point as alpha_p, but its inclusion is not open: the
  neighbourhood factorization here is a scheme-morphism equation and cannot be
  supplied merely from that point-set containment.
- Flatness and local finite presentation concern `H.hom`, not `i.left` or `G.hom`.
  They are substantive hypotheses, not properties inferred for every group object.
- One explicit scheme universe suffices for S, H, G, V and their maps. No quantifier
  over test schemes in an artificially smaller universe occurs.

Searches made in this session (all searches actually ran):

- `msearch.py ... leanfinder`: “A flat closed subgroup scheme containing an open
  neighbourhood of the identity section is an open immersion”. Eight hits, including
  `IsOpenImmersion.of_flat_of_mono`, open-immersion consequences and the definition;
  no exact theorem. Read `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`, lines 38–39:
  its theorem assumes flatness and local finite presentation of i itself, whereas
  this node assumes them of H → S. It cannot be recorded as an exact match.
- `msearch.py ... loogle`: `"IsOpenImmersion", "GrpObj"`. Successful, zero hits.
- `msearch.py ... grep` in `AlgebraicGeometry`:
  `(subgroup|GrpObj).*(isOpenImmersion|IsOpenImmersion)|(isOpenImmersion|IsOpenImmersion).*(subgroup|GrpObj)`.
  Successful, zero hits.
- `msearch.py ... leansearch`: “A closed subgroup scheme flat and locally of finite
  presentation over the base is open if it contains an open neighbourhood of the
  identity”. Eight hits: topological subgroup openness, the same flat-monomorphism
  theorem, and universal openness. Topological subgroup openness does not give an
  isomorphism on scheme structure sheaves.
- `rg -n` in `lean/WeilConjectures` and `lean/Sheaf` for
  `(identity.*neigh|neigh.*identity|flat.*subgroup|subgroup.*flat)`, case insensitive:
  unrelated étale-neighbourhood statements and flat torsion subgroup results;
  no declaration of this theorem.
- Search by the complete item id in `lean/WeilConjectures`: no hits.
- Search for the proposed full theorem basename in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no hits.
- Searched the existing `GrpObj` / `IsMonHom` interfaces in Mathlib and the project;
  reused the existing definitions instead of introducing a group-scheme wrapper.

No `STATEMENT-DISPUTED` flag or unresolved node fault was found. The illustrative
CompactObject Sheaf module has been withdrawn in the current clone; its node points
to `WeilConjectures.CategoryTheory.CompactObject`, whose module/header was read instead.

Validation: the initial `scompile.py` server run passed both the sandbox and canonical
library-module compilations with no errors or non-sorry warnings. The final module
is additionally checked by the required delivery dry run and delivery compile.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
