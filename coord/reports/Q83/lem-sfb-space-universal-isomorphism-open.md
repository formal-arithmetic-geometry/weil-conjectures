## Worker report

Stage 2 statement of Stacks Project Tag 05XD, spaces-more-morphisms.tex,
lemma-where-isomorphism (lines 11792–11832 in the read clone). The theorem is
AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_universal_isomorphism in
Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversalIsomorphismOpen. Its only proof is sorry;
no definitions, helper axioms, or new nodes are introduced. The accepted stage-1 split
is preserved. The item node changes only in lean.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Scheme S, in the fixed size convention | Explicit universe u and {S : Scheme.{u}}; autoImplicit false. |
| Algebraic spaces A, C, B over S | (A C B : AlgebraicSpace S), the recorded full subcategory of fppf sheaves. |
| Maps p:A→B, q:C→B, f:A→C | (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C). |
| Commutativity q∘f=p | (w : f ≫ q = p). |
| p locally of finite presentation | hp_lfp : MapIsLocallyOfFinitePresentation p. |
| p flat | hp_flat : MapIsFlat p. |
| p universally closed | hp_closed : MapIsUniversallyClosed p, quantifying over all algebraic-space base changes. |
| q locally of finite type | hq_lft : MapIsLocally (@LocallyOfFiniteType) q. |
| q closed | hq_closed : IsClosedMap (mapPoint q.hom.hom), using the established point topology. |
| q separated | hq_sep : MapIsSeparated q, whose diagonal is representable by closed immersions. |
| Open subspace U of B | ∃ U : OpenSubspace B, using the existing subfunctor and representable-open-inclusion predicate. |
| Every algebraic space B' over S and h:B'→B | ∀ (B' : AlgebraicSpace S) (h : B' ⟶ B). |
| h factors through U | ∃ l : B'.obj.obj ⟶ U.val.toFunctor, l ≫ U.val.ι = h.hom.hom. |
| If and only if f after base change is an isomorphism | The displayed ↔ IsIso (pullback.map ...), with source map f.hom and identity maps on B' and B. |
| Fibre products are sheaf fibre products | pullback.map is taken in the category of fppf sheaves, on p.hom, q.hom, h.hom. |
| When B is a scheme, U is represented by an open subscheme | For each T : Over S and e : B.obj.obj ≅ yoneda.obj T, there exist V : Over S, j : V ⟶ T with IsOpenImmersion j.left, and eU : U.val.toFunctor ≅ yoneda.obj V compatible with the inclusions. |

The factorization uses a presheaf natural transformation because U is recorded as a
subfunctor; it is automatically a sheaf and algebraic space. The full inclusions of
sheaves and of algebraic spaces identify this with the requested algebraic-space
factorization. Likewise the sheaf pullbacks are algebraic spaces by the recorded
fibreProduct_isAlgebraicSpace theorem. Their isomorphism as sheaves is equivalent to
their isomorphism as algebraic spaces. The two small by proofs inside pullback.map
only supply its commuting-square arguments, not additional mathematical hypotheses.
They express w and identity compatibility.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.IsAlgebraicSpace, IsRepresentableWith, IsEtale and IsSurjective.
- def-weil-size-convention is a convention record with no declaration: use explicit
  universe u throughout, as in the recorded AlgebraicSpace interface. There is no
  independent smaller test universe and no extra universe equality hypothesis.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally,
  MapIsFlat, MapIsLocallyOfFinitePresentation, MapIsUniversallyClosed and MapIsSeparated.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace: OpenSubspace.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback and etale_fibreProduct_isScheme;
  source read in full, statement import public.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: mapPoint (through morphism properties).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType.
- The stated proof dependencies in Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  FiniteType and ClosedImmersion are imported without public. The proof dependencies
  lem-sfb-space-universal-surjective-flat-open,
  lem-sfb-space-universal-closed-immersion-open,
  lem-sfb-space-surjective-flat-closed-immersion-isomorphism and
  lem-sfb-space-local-properties-chart-test have no Lean record in the read DAG;
  there is consequently no recorded module to import for them yet. Their uses are
  preserved in the theorem's complete six-step proof docstring. They are proof inputs,
  not missing notions needed to state this item.

Edge cases checked mathematically before recording the signature:

- f an isomorphism: the required open is the whole base, with every test factoring.
- Empty base or empty test space: no nonemptiness assumptions occur, and the unique
  map from an empty test factors through every open; its pullback morphism is an iso.
- A=C empty over any B: the whole base works, not merely the empty open.
- A empty and C=B with q identity, p the empty map: the locus is the empty open;
  a nonempty test cannot turn the empty-to-test map into an isomorphism.
- Nonreduced test spaces and bases, including Spec(k[epsilon]/epsilon^2), are retained.
  There is no reducedness, Noetherian, quasi-compactness, or characteristic restriction.
- Algebraic spaces which are not schemes are allowed as B and B'. The final conjunct
  is only conditional on an actual scheme representation of B; it does not require one.

Searches (preserved sandbox searches.jsonl and additional read-only source searches):

- msearch.py leanfinder, “The universal isomorphism locus of a diagram of algebraic
  spaces is an open subspace of the base”: 8 hits, including UniversallyOpen.eq and
  scheme open immersions; none states this result.
- msearch.py loogle, '"AlgebraicGeometry", "isomorphism", "open"': one hit,
  AlgebraicGeometry.isomorphisms_eq_isOpenImmersion_inf_surjective, which is a scheme
  morphism criterion, not an open parameter locus for arbitrary algebraic spaces.
- msearch.py grep, 'whereIsomorphism|where_isomorphism|AlgebraicSpace|isomorphism.*locus|locus.*isomorphism'
  in Mathlib/AlgebraicGeometry: zero hits.
- msearch.py leansearch, “The isomorphism locus of a morphism between algebraic spaces
  over a base is represented by an open subspace under flat locally finitely presented
  universally closed source and separated closed locally finite type target”: 8 hits
  on scheme open immersions, universal openness and universal closedness; no match.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  whereIsomorphism, where_isomorphism, exists_openSubspace_universal_isomorphism and
  this node id: no existing declaration. Broader universal/isomorphism searches give
  scheme-only UniversalIsomorphismOpen and vector-bundle results, not this statement.

No statement correction or disputed statement. No released repair note names the item.
The inherited stage-1 unchanged-node refusal is superseded by the explicit stage-2
handoff in coord/brief-stage2.md §0, and the current queue lists stage 2 for this item.

Validation: prescribed scompile.py compiled this file both as Sheaf.Stage2.Sandbox0
(5.8 s) and under its library module name (9.7 s), clean, using the 60-second limit.

## Second reading by Q83

A separate rereading of the node, Stacks 05XD and the file checked the six assumptions,
the orientation f ≫ q = p, both directions of the universal property and the final
scheme-base clause. The induced pullback map has f on A→C and identity on the test
object, so the isomorphism is imposed on the requested canonical map. A scheme-base
representation e transports the inclusion, and the equation
U.val.ι ≫ e.hom = eU.hom ≫ yoneda.map j makes j the inclusion of this same U.
No mismatch was found, and the candidate Lean file required no changes. This is the
worker's own rereading; no additional agent was started, as the dispatcher forbids it.
The maintainer's independent review remains the delivery review.
