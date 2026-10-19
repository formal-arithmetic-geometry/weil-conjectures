## Worker report

This repairs the returned delivery at immutable head 13be1ff0a3d2. The retained
sandbox contained only brief markers: no Lean module, node copy, or report.
The current shared DAG still has no Lean record for this item. This delivery
supplies the missing formal statement and complete record (H3/H2), source and
proof docstrings (H8), a clause-by-clause second reading (H1/H11), and compilation
evidence. Delivery is rebuilt by the prescribed wrapper on current newtargets-dag;
no direct Git operation or change to the shared checkout was made.

The module `Sheaf.AlgebraicGeometry.EtaleAtlasPresentation` states
`AlgebraicGeometry.AlgebraicSpace.etale_atlas_presentation`, with `sorry` as its
entire proof. Its only other declaration, `etaleAtlasPresentationMap`, constructs
the canonical comparison using actual universal-property data. No new nodes,
dependency repairs, statement correction, or disputed statement are needed.
Only the item's `lean` field changes.

Every hypothesis of the natural statement is rendered as follows:

| Natural statement | Lean |
| --- | --- |
| A scheme S | `{S : Scheme.{u}}` |
| An algebraic space X over S | `(X : AlgebraicSpace S)`; its underlying fppf sheaf is `X.obj` |
| An S-scheme U | `(U : Over S)` |
| A map h_U to X | `(p : yoneda.obj U ⟶ X.obj.obj)` |
| Representable and étale | `(hp : IsEtale p)`; the recorded `IsEtale` includes scheme-test representability |
| Surjective in every scheme base change | `(hsur : IsSurjective p)` |
| A scheme R representing U times_X U, with its two projections | `(R : Over S) (s t : R ⟶ U)` and `hR : IsPullback (yoneda.map s) (yoneda.map t) p p` |
| Big fppf site over S | `Scheme.fppfTopology.over S`, exactly the topology used in the recorded algebraic-space definition |
| Q is the sheafification of the presheaf relation quotient | `Q : Sheaf (Scheme.fppfTopology.over S) (Type u)`, the unit `η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ Q.obj`, and `hη`, the bijection given by precomposition with that unit into each sheaf G |

Every conclusion is rendered as follows:

| Natural statement | Lean |
| --- | --- |
| (s,t) embeds R as a relation in U times_S U | `Mono (prod.lift s t)` in `Over S`; product in this category is fibre product over S |
| It is an equivalence relation on every T | The `Equivalence` clause for `fun a b : T ⟶ U ↦ ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b` |
| R(T) identifies with exactly the pairs having equal images in X(T) | For all `T`, `a`, `b`, existence of that r is equivalent to `p.app (op T) a = p.app (op T) b`; monicity makes r unique |
| Both projections are surjective and étale | `Etale s.left ∧ Surjective s.left ∧ Etale t.left ∧ Surjective t.left` |
| The canonical comparison Q to X is an isomorphism | `IsIso (etaleAtlasPresentationMap p s t hR Q η hη)`; this is a morphism of the given sheaves |
| It identifies the quotient map with p | `(coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ≫ (etaleAtlasPresentationMap p s t hR Q η hη).hom = p` |

The presheaf coequalizer is computed sectionwise by the functor-category
colimit API. Since the represented relation is an equivalence relation, its
coequalizer set on T is U(T)/R(T), including the canonical quotient projection.
This is the same encoding used by the published
`Sheaf.AlgebraicGeometry.EtaleRelationQuotient` and
`Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`; neither already states
this item. The sheafification interface is the universal property of
`def-weil-pbc-sheafification`, not an assumption that every presheaf on this large
site has a small-valued sheafification. This preserves the `Type u` values of the
recorded algebraic-space definition, without imposing a new universe equality.

The comparison definition first forms `coequalizer.desc p hR.w`. It then applies
`(Equiv.ofBijective ... (hη X.obj)).symm` and bundles the resulting natural
transformation as a sheaf morphism. Bijectivity uniquely determines this data.
There is no arbitrary map, unspecified Nonempty choice, postponed existence
statement, or sorry in this definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `IsSurjective`, `IsRepresentableWith`. I read the full
  source and docstrings. `IsEtale` and `IsSurjective` quantify over all scheme
  tests with representing pullback squares; X is the full subcategory of fppf
  sheaves having representable diagonal and an atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. I read all three signatures and docstrings.
  Here a chosen representing scheme is supplied with its Yoneda pullback square,
  so no representative is chosen from a postponed existence theorem.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  the affine-locally étale property recorded by def-weil-etale-morphism.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.AlgebraicGeometry.Sites.Small`:
  `Scheme.overGrothendieckTopology`. Their definitions agree with the `.over S`
  fppf topology used here. The recorded Mathlib match, not a missing Lean record,
  is used for def-pc-fppf-site.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, and `sheafificationAdjunction`. The module is publicly imported;
  their hom-set universal property is expressed directly by η and hη at the
  specified presheaf, with no assumption on unrelated presheaves.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` and the universal-property interface.
  The corresponding arbitrary representing square is `IsPullback` from the
  publicly imported algebraic-space interface.

Proof-only dependencies are imported: `Sites.Limits` gives
`Sheaf.createsLimitsOfShape` and `Sheaf.isSheaf_of_isLimit`;
`Sites.LocallySurjective` gives `Sheaf.isLocallySurjective_iff_epi`;
`Sites.RegularEpi` supplies the regular-epimorphism interface; and
`Limits.Shapes.KernelPair` gives `IsKernelPair.toCoequalizer'`.
These are the recorded Mathlib matches for all three theorem dependencies.
The proof docstring includes all five DAG proof steps. At these small-valued
large-site universes, stage 3 can use the forward local-surjectivity implication
(which needs no general sheafification instance), and prove the coequalizer
factorization by gluing the explicit local lifts. It must not assume
`HasSheafify` for every small-valued presheaf merely to instantiate the most
general regular-epi theorem. This is the same sheaf coequalizer argument as
Stacks Tag 086K; it does not change this statement.

Sources opened: `literature/stacks-project/spaces.tex`,
`lemma-space-presentation`, its whole statement and proof; and
`literature/stacks-project/sites.tex`, `proposition-sheafification-adjoint` and
`lemma-coequalizer-surjection`, their statements and proofs. The quotient and
map agree with those sources; the extra surjectivity of both projections in the
node follows by base change of the surjective atlas.

Edge cases checked before writing:

- Identity atlas: R is the diagonal; its relation is equality and Q identifies
  with X. No nonempty or positive-dimensional hypothesis is imposed.
- Disjoint-union atlas: distinct lifts of the same section are related, so this
  is a relation quotient and does not incorrectly assert U equals X.
- A section with no global lift: only local lifts are used; no componentwise
  surjectivity of p on all sections is assumed.
- Empty space and empty atlas: maps from empty test schemes, equivalence
  relations on empty section sets, and the quotient unit are all admitted.
  Neither a nonempty underlying scheme nor a chosen atlas point is required.
- Arbitrary S and arbitrary representing R: no separation, quasi-compactness,
  finiteness or Noetherian assumptions are introduced. The site, scheme and
  value universes are exactly those of the recorded dependency.

Searches made in this repair, using the prescribed msearch.py wrapper:

- LeanFinder: `A surjective etale atlas of an algebraic space presents it as
  the sheafification of its kernel relation quotient`: eight hits about standard
  étale algebra presentations and scheme étale categories; no algebraic-space
  presentation theorem.
- LeanSearch: `An algebraic space is the sheaf quotient of any surjective etale
  atlas by its kernel pair`: eight hits concerning ring étaleness, locally ringed
  space coequalizers, and scheme étale sites; no exact statement.
- Loogle: `Setoid.ker, Quotient.map, presheafToSheaf`: zero hits and unknown
  identifier `presheafToSheaf` in the service. The actual Mathlib declaration was
  then read directly in Sites/Sheafification.lean.
- Loogle: `"IsKernelPair"`: twelve hits, including the kernel-pair definition
  and general pullback lemmas; they require an epimorphism/coequalizer interface
  and do not prove that this atlas gives the quotient.
- Grep through msearch.py: `AlgebraicSpace|atlas.*quotient|quotient.*atlas`:
  zero Mathlib hits.
- Direct rg in the upstream WeilConjectures tree, side-project lean/Sheaf, and
  dag/lean_names_upstream.json: node id, atlas/quotient patterns, and both proposed
  declaration names. No upstream statement of this item and no name collision.
  The side-project hits include the converse étale-relation quotient theorem
  and its restriction theorem; their full signatures were read and do not state
  the atlas-presentation theorem.

## Second reading by NY

I reopened the complete node, the complete finished module, the dependency
interfaces and the cited Stacks statements for a second, separate pass. This
is the delivering worker's second reading; the maintainer performs the
independent review under the current direct-delivery brief.

I checked every binder: S is unrestricted; X is the existing algebraic-space
object; U and R are S-schemes; p has precisely representable étaleness and
surjectivity; hR identifies the given projections with the sheaf fibre product;
Q, η and hη specify precisely the sheafification required by the node.
No étale or surjective property of s or t is assumed.

I checked every clause against the displayed Lean signature: monicity of
`prod.lift s t` gives uniqueness of relation witnesses, the pointwise
existential iff gives exactly the equal-image pairs, and the `Equivalence`
conjunct explicitly covers reflexivity, symmetry and transitivity. Both
scheme projections have both required properties. The final two conjuncts
assert that the constructed sheaf morphism is an isomorphism and that its
composite with the actual quotient projection equals the original p.

I also reread the comparison definition: the hom-set bijection uses the
specific target sheaf `X.obj`, its argument is `coequalizer.desc p hR.w`, and
its inverse gives a natural transformation `Q.obj ⟶ X.obj.obj` which is bundled
as a sheaf morphism. It does not select an unrelated isomorphism. The
presheaf coequalizer quotient and the sheafification universal property have
exactly the orientation required for the final equality.

No mathematical mismatch was found on this second pass. The earlier returned
packet's missing statement, record and docstrings are supplied in full rather
than re-pushed unchanged. No other DAG statement is changed. The sole
postponed theorem has the matching DAG node and complete proof docstring.

## Compilation and delivery checks

On 2026-10-18 UTC I ran the required command:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py NY lem-a1-etale-atlas-presentation \
  /home/ubuntu/weil-newtargets-stage2-sandbox/NY/lem-a1-etale-atlas-presentation/lean/Sheaf/AlgebraicGeometry/EtaleAtlasPresentation.lean
```

It exited 0 with no errors or warnings. The wrapper checked both its sandbox
copy and the actual library module separately. Output:

```text
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into the private overlay) [251.9 s]
library Sheaf/AlgebraicGeometry/EtaleAtlasPresentation.lean
[2.8 s]
```

The longer sandbox elapsed time includes compiler-slot acquisition; the
wrapper retained its unchanged 60-second Lean-process limit. There is one
Lean module in this delivery, and it compiled cleanly.

Dry run on 2026-10-18 UTC:

```text
python3 /home/ubuntu/weil-launcher-nt/deliver2.py NY lem-a1-etale-atlas-presentation --no-push
OK (dry run): commit fcafce3151 passes the preflight and compiles; nothing pushed
```

The wrapper staged exactly the item module, item node record, and worker report.
No preflight failure or compiler warning remained.
