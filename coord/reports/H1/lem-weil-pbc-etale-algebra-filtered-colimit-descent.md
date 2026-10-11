## Worker report

Module: `Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`.
Declaration: `AlgebraicGeometry.exists_etale_algebra_of_filteredColimit`.
The theorem has `sorry`; no definition is added and no theorem is proved.
The original statement and dependencies are unchanged.

Hypothesis and clause correspondence:

- Small filtered category I: `{I : Type w} [Category.{v} I] [IsFiltered I]`.
  The object and arrow universes are explicitly bound and independent of the rings.
  Mathlib's filteredness includes nonemptiness and equalization of parallel arrows.
- Diagram of commutative rings: `F : I ⥤ CommRingCat.{u}`.
- Chosen colimit A and its coprojections: `[HasColimit F]`, `colimit F`,
  and `colimit.ι F i`. The local name `A` is its underlying type, with the
  inherited commutative ring instance.
- Commutative ring B and ring map A → B: `(B : Type u) [CommRing B]`
  and `f : (colimit F : CommRingCat.{u}) ⟶ CommRingCat.of B`.
- Spec B → Spec A etale: `hf : Etale (Spec.map f)`.
- Existence of a stage: `∃ (i : I)`.
- A commutative ring B_i and map A_i → B_i: existential binders
  `(Bi : Type u) (_ : CommRing Bi) (g : F.obj i ⟶ CommRingCat.of Bi)`.
- Spec B_i → Spec A_i etale: `Etale (Spec.map g)`.
- A_i acts on A through the required coprojection, and on B_i through g:
  the two `letI : Algebra (F.obj i) ...` use respectively
  `(colimit.ι F i).hom.toAlgebra` and `g.hom.toAlgebra`.
- A acts on B through f: `letI : Algebra A B := f.hom.toAlgebra`.
- Isomorphism of A-algebras B ≅ A ⊗[A_i] B_i:
  `Nonempty (B ≃ₐ[A] (A ⊗[F.obj i] Bi))`, with Mathlib's canonical
  left-factor A-algebra structure on this tensor product.

Dependencies used:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, its coprojections `colimit.ι`, and
  `HasColimit`; filteredness is `CategoryTheory.IsFiltered` from
  `Mathlib.CategoryTheory.Filtered.Basic` (imported transitively).
  The generated colimit signature and docstrings were read in HasLimits.lean,
  and the full IsFiltered signature/docstring in Filtered/Basic.lean.
- `def-weil-etale-morphism`: Mathlib leaf `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Its full class signature,
  affine-local docstring, and ring-map bridge instance were read.

Source check: the local Stacks .tex files are absent on this machine.
Opened https://stacks.math.columbia.edu/tag/00U2, statement (9) and its proof.
The source has precisely the filtered-colimit descent conclusion used here.
The four proof steps from the DAG are carried in the theorem docstring,
including the names of their four proof dependencies.

Edge cases checked: an empty category is correctly excluded by IsFiltered,
which is nonempty; parallel arrows need not be unique (no poset restriction).
Zero rings, zero target algebra, identity diagram with one object, and arbitrary
characteristic require no extra hypothesis. All rings share the universe of
CommRingCat and Spec; `u` is arbitrary, so rings originally represented in different
universes can be placed in their common universe. No nontriviality, injectivity,
Noetherian, finite diagram, or finite base-ring hypothesis is added.

Searches on 2026-10-11:

- msearch LeanSearch: "etale algebra descends to a stage of a filtered colimit
  of commutative rings": service unavailable (Internal Server Error);
  no verdict drawn from this unavailable search.
- msearch LeanFinder: "etale algebra over a filtered colimit of commutative
  rings descends to some stage": eight hits, including
  Algebra.Etale.exists_subalgebra_fg, Etale.comp, RingHom.Etale.toAlgebra.
  No exact statement: the subalgebra lemma is descent to a finitely generated
  subalgebra, rather than an arbitrary filtered diagram stage.
- msearch Loogle: "Algebra.Etale, CategoryTheory.Limits.IsColimit": no hits.
- msearch grep: "IsColimit|IsFiltered|DirectLimit", RingTheory/Etale: no hits.
- Direct rg of the same pattern in Mathlib RingTheory/Etale and
  RingTheory/Smooth: no hits.
- Direct rg in WeilConjectures and lean/Sheaf for etale/colimit combinations,
  the node id and the chosen declaration name: no duplicate.
  EtaleDirectedColimitDescent is descent of etaleness of a given algebra map,
  not existence of an algebra model. The upstream
  isFinite_and_etale_of_isColimit is a finite-monoid quotient theorem,
  as verified by opening its signature and docstring, not filtered-ring descent.
- tools/lean_names_upstream.py show for the item and direct name/id search:
  no matching declaration for this node.

Server compile: scompile.py compiles the final file cleanly (exit 0).
No node fault or STATEMENT-DISPUTED issue found. No new nodes or dependency
modules are needed. The independent second reading remains for the next worker.

## Second reading by H1

Independent second reader, 2026-10-11. I opened the sandbox node and Lean
module, both statement-dependency nodes and their Mathlib declarations, and
Stacks algebra.tex at its conventions, lemma-etale (00U2), items (8), (9),
and proof of (9). The local Stacks checkout is absent, so I retrieved the
upstream .tex into this item's scratchpad from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex;
I also opened https://stacks.math.columbia.edu/tag/00U2.
The conventions say rings are commutative with 1 and permit the zero ring.
Item (9) assumes only a filtered ring colimit and an etale ring map; there
is no standing field, Noetherian, injectivity, or characteristic hypothesis.

Object, hypothesis and conclusion inventory, matched individually:

1. Small filtered category I: `{I : Type w} [Category.{v} I] [IsFiltered I]`.
   PASS. Both universes are explicit. I read Filtered/Basic.lean:82-98:
   IsFiltered includes the common-object and parallel-arrow equalization
   clauses and Nonempty I. No poset or unique-arrow restriction occurs.
2. Diagram i ↦ A_i of commutative rings: `(F : I ⥤ CommRingCat.{u})`.
   PASS. Objects and transition maps are the actual ring diagram, without
   assumptions on the maps or rings beyond CommRing.
3. Chosen colimit A and coprojections ι_i: `[HasColimit F]`, `colimit F`,
   `colimit.ι F i`. PASS. I opened def-weil-pbc-category-colimit and read
   HasLimits.lean:168-189, including the to_dual-generated colimit and ι
   definitions. These are precisely its recorded declarations. HasColimit
   expresses the colimit already assumed in the node; it adds no property.
4. Ring B and A → B: `(B : Type u) [CommRing B]` and
   `(f : (colimit F : CommRingCat.{u}) ⟶ CommRingCat.of B)`.
   PASS. A category morphism is the required unital ring homomorphism.
5. Hypothesis Spec B → Spec A etale: `(hf : Etale (Spec.map f))`.
   PASS. Spec.map reverses this ring map, as required. I opened
   def-weil-etale-morphism and Etale.lean:36-57 and :140-145: its class is
   affine-local ring-map etaleness, with the recorded equivalence to flat,
   formally unramified and locally finite presentation. It is the node's
   notion, not finite etale or etale at a point.
6. There exists an index i: `∃ (i : I)`. PASS, after all original objects
   and hypotheses, with no prescribed initial stage or extra domination.
7. There exists a commutative ring B_i and A_i → B_i:
   `(Bi : Type u) (_ : CommRing Bi) (g : F.obj i ⟶ CommRingCat.of Bi)`.
   PASS. The existential ring structure binds the one used by g and the
   tensor product; there is no extra finiteness assumption on its carrier.
8. Spec B_i → Spec A_i etale: `Etale (Spec.map g)`. PASS, the same notion
   as the original hypothesis; not merely smooth or formally etale.
9. Tensor product via ι_i and g: the local A is the colimit's carrier;
   the local CommRing is inherited. The two local Algebra instances are
   `(colimit.ι F i).hom.toAlgebra` on A and `g.hom.toAlgebra` on Bi.
   PASS. Neither an arbitrary action nor a private base-change notion is
   substituted for the maps specified by the node.
10. Isomorphism of A-algebras B ≅ A ⊗[A_i] B_i:
    `letI : Algebra A B := f.hom.toAlgebra` followed by
    `Nonempty (B ≃ₐ[A] (A ⊗[F.obj i] Bi))`. PASS. Nonempty is the
    existence of an isomorphism, not a chosen additional object or merely
    a ring isomorphism. I read TensorProduct/Basic.lean:270-290:
    leftAlgebra's algebraMap is includeLeftRingHom composed with the
    left-factor algebraMap, so the tensor product has exactly the canonical
    A-algebra structure. The order of existential choices agrees with the
    node and every conclusion clause is present.

Edge cases: empty I is excluded by the source's filteredness and by
IsFiltered, rather than silently by the conclusion. The one-object diagram
and categories with multiple parallel arrows are allowed. Zero A_i, A or B
and their empty affine spectra are allowed: no Nontrivial or Nonempty
spectrum instance is required; in particular B = 0 can have B_i = 0.
No n parameter occurs; presentations with zero generators are not excluded.
All characteristics are permitted. Universes u, w, v are explicitly bound
and independent for ring carriers, index objects and index arrows. Spec and
CommRingCat use one arbitrary ring universe u; differently sized set-level
rings can be represented in their common universe, so this excludes no
source ring diagram. HasColimit states exactly existence of the colimit in
that universe, which the node assumes. No unbound variable remains.

Independent searches used different wording from the first worker:

- msearch LeanFinder: "An etale morphism over the direct limit of a ring
  diagram admits an algebra model at one index". Eight hits, including
  Algebra.Etale.exists_subalgebra_fg, RingHom.Etale.toAlgebra,
  Algebra.Etale.comp and polynomial factorization results; none has the
  arbitrary filtered-stage existence conclusion. I opened
  Smooth/NoetherianDescent.lean:287-299: exists_subalgebra_fg chooses a
  finitely generated subalgebra of A, not an index of F.
- msearch Loogle: `"Etale", "colimit"`: zero hits.
- msearch LeanSearch: "An etale algebra over a direct limit has an etale
  model over one index ring": Internal Server Error, recorded unavailable;
  no negative verdict is inferred from the unavailable service.
- msearch grep: `Etale.*colimit|colimit.*Etale|Etale.*DirectLimit|DirectLimit.*Etale`:
  zero hits. Direct rg searched etale with filtered, colimit and direct-limit
  variants in Mathlib RingTheory and Algebra/Category/Ring, the source
  WeilConjectures tree and repository lean/Sheaf. RingTheory/Etale and
  RingTheory/Smooth contain no IsColimit, IsFiltered, DirectLimit or
  IsDirected occurrence. Name/id search in WeilConjectures and
  dag/lean_names_upstream.json found no existing declaration for this node.
- I opened the two superficially similar project/source hits:
  Etale.exists_stage_of_directedColimit in EtaleDirectedColimitDescent.lean
  descends etaleness of an already given finitely presented map, whereas
  this item constructs an algebra model of B. The upstream
  isFinite_and_etale_of_isColimit in ColimitsOver.lean:477 concerns a
  finite monoid quotient of a finite etale scheme. Neither replaces this
  statement. Other hits concern sheaf colimits and stalks.

H4/H12/H13: the two recorded statement dependencies are usable exactly as
recorded. All other notions are standard Mathlib ring morphisms, Spec,
algebra structures, tensor products and AlgEquiv. There are no new nodes,
dependency modules or private definitions to review or repair.
H5/H6/H8/H9: no definitions, hollow data or proofs have been added; the
only theorem has proof `sorry`. Module and declaration docstrings contain
the source and exact blueprint id. The declaration docstring carries all
four DAG proof steps with their four dependencies, ending in the inverse
cancellation isomorphism composed with the finite-type model isomorphism.
The three imports serve the ring colimit, etaleness and tensor product.
Header, namespace, declaration name and line lengths meet the conventions.

No mismatch found. I changed only this report, leaving the correct Lean
and node record unchanged. There is no statement_change and no citer
verdict to audit. The node's lean.statement agrees verbatim with the file's
signature. Server scompile.py on the absolute sandbox module path passed
(exit 0, 1.8 seconds), with no errors or warnings. The first invocation
used a relative path from the repository and could not find the sandbox
file; rerunning on its absolute path resolved that invocation error.

## Reviewer fix (R-efc0959, stage 2)

The node says "small filtered category"; the delivery bound
`[Category.{v} I]` with an independent arrow universe, which is a
generalisation beyond the node and not the landed filtered-colimit form
(K1 ccd06d885, FlatColimitRings). Replaced by
`{I : Type w} [SmallCategory I] [IsFiltered I]` and dropped universe `v`.
Everything else (HasColimit/colimit/colimit.ι, Spec-form Etale on both maps,
algebra structures via colimit.ι, g and f, Nonempty A-algebra isomorphism
with the tensor product's left algebra structure) matches the node.
