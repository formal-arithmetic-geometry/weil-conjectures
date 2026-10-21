## Worker report

The delivery states `DerivedCategory.split_fibre_projections` in
`Sheaf.CategoryTheory.DerivedCategory.SplitFibreProjections`. There are no new
definitions or dependency modules, and no change to the natural-language node.
The sole theorem has proof `sorry`. Its docstring gives all eight proof steps
from the node, including the two degree-adjacent connecting maps, both graph
kernel calculations, detection of derived isomorphisms, and transport.

For the following correspondence, write H for `homologyFunctor A n`, f for
`T.mor₁`, d for `T.mor₂`, p for `f ≫ β.hom ≫ biprod.fst`, and q for
`f ≫ β.hom ≫ biprod.snd`. These are explanatory names only; no private definitions,
local notation, or `let` binders are used in the Lean signature.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| An arbitrary abelian category A | `(A : Type u) [Category.{v} A] [Abelian A]` |
| Its ordinary derived category, with the chosen morphism universe | `[HasDerivedCategory.{w} A]` and `DerivedCategory A`; u, v, w are explicit independent universes |
| A distinguished triangle G → M → Z → G[1] | `T : Triangle (DerivedCategory A)` with `hT : T ∈ distTriang (DerivedCategory A)`; G, M, Z are its three vertices and the first two maps are f and d |
| Middle vertex X ⊕ Y, literally or by a specified identification | `(X Y : DerivedCategory A) (β : T.obj₂ ≅ X ⊞ Y)` |
| First case: Z = Y and d = (h, -1) | First conjunct quantifies over every `h : X ⟶ Y` and `γ : T.obj₃ ≅ Y`, with hypothesis `T.mor₂ ≫ γ.hom = β.hom ≫ biprod.desc h (-𝟙 Y)` |
| p is an isomorphism | `IsIso (T.mor₁ ≫ β.hom ≫ biprod.fst)` |
| q = h ∘ p | `T.mor₁ ≫ β.hom ≫ biprod.snd = (T.mor₁ ≫ β.hom ≫ biprod.fst) ≫ h`; Lean composition is diagrammatic |
| For every integer n, Hⁿ(d) is split epic | `∀ n : ℤ, IsSplitEpi ((homologyFunctor A n).map T.mor₂) ∧ ...` |
| Hⁿ(f) identifies Hⁿ(G) with the kernel subobject | `Mono (H.map T.mor₁)` together with equality of the image of `H.map (f ≫ β.hom) ≫ Functor.biprodComparison H X Y` and `kernelSubobject (biprod.desc (H.map h) (-𝟙 (H.obj Y)))` |
| This kernel is the graph, namely the image of (1, Hⁿ(h)) | The second image equality has right side `imageSubobject (biprod.lift (𝟙 (H.obj X)) (H.map h))` |
| Second case: Z = X and d = (1, -r) | Second conjunct quantifies over every `r : Y ⟶ X` and `γ : T.obj₃ ≅ X`, with hypothesis `T.mor₂ ≫ γ.hom = β.hom ≫ biprod.desc (𝟙 X) (-r)` |
| q is an isomorphism | `IsIso (T.mor₁ ≫ β.hom ≫ biprod.snd)` |
| p = r ∘ q | `T.mor₁ ≫ β.hom ≫ biprod.fst = (T.mor₁ ≫ β.hom ≫ biprod.snd) ≫ r` |
| In every degree Hⁿ(d) is split epic and Hⁿ(f) identifies the source with the graph kernel | The same `IsSplitEpi`, `Mono`, and image/kernel equality, now with normalized arrow `biprod.desc (𝟙 (H.obj X)) (-(H.map r))` |
| The second graph is the image of (Hⁿ(r), 1) | The last equality has right side `imageSubobject (biprod.lift (H.map r) (𝟙 (H.obj Y)))` |
| All assertions hold after specified isomorphisms of vertices and arrows | T is arbitrary; β and γ are specified, and the displayed hypothesis is exactly commutativity for the second arrow. The first arrow is used as `f ≫ β.hom`, so the source triangle itself is covered. No identification of its first vertex is needed: for an additional α : G₀ ≅ G commuting with the first arrow, instantiate the theorem on the source triangle with first vertex G₀. Its actual projections are p ∘ α and q ∘ α. Identity β and γ recover the literal displayed triangles. |

The normalization of H(d) in the kernel clauses is canonical, not an arbitrary
substitute arrow. Additivity and functoriality carry the assumed square for d
through H; `Functor.biprodComparison H X Y` identifies H(X ⊞ Y) with
H(X) ⊞ H(Y), and H(γ) identifies its target. The normalized arrow is therefore
exactly `(H(h), -1)` or `(1, -H(r))`. Monicity of H(f) and equality of its image
with that kernel mean that its source is isomorphic to the kernel by H(f),
not merely that it maps onto the same subobject. The second equality expresses
the graph in the actual biproduct of cohomology objects.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` from `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors` from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
  These are exactly the recorded interface, with no replacement definition.
- The proof leaves `lem-sf-derived-homology-long-exact` and
  `lem-weil-pbc-unbounded-derived-iso-cohomology` use
  `DerivedCategory.HomologySequence.exact₁`, `exact₂`, `exact₃` and
  `DerivedCategory.isIso_iff` from the same imported HomologySequence module.
- The proof leaf `lem-weil-pbc-hom-into-triangle-exact` uses
  `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂` and
  `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂` / `coyoneda_exact₁`
  from `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, already imported
  through Basic. No separate redundant proof import is needed.
- `Mathlib.CategoryTheory.Subobject.Limits` supplies `imageSubobject` and
  `kernelSubobject`. `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`
  supplies `CategoryTheory.Functor.biprodComparison`, with its actual signature
  and canonical projection equations inspected in the source.

Sources opened: Stacks `cohomology.tex`, lemma-glue, lines 11071–11125 (Tag
08DG), and `derived.tex`, lemma-cohomology-homological and the following long
exact sequence, lines 3618 onward (Tag 05RS). The signed formulas in the node
are the abstract split-map calculation extracted from that restriction
argument. The two sections are (0, -1) and (1, 0), respectively.

Edge cases checked mathematically before drafting: zero objects in either
summand, h = 0 and r = 0, identity maps when X = Y, characteristic two (where
minus and plus coincide), all negative and nonnegative degrees including zero,
and arbitrary unbounded complexes. The formula with h = 0 has horizontal graph;
the formula with r = 0 has vertical graph. Arbitrary β and γ, including identity
and sign-changing isomorphisms, are retained. There is no boundedness,
nonzero-object, characteristic, smallness, or same-universe restriction.
`HasDerivedCategory` records the chosen localization universe as required by the
dependency node, rather than assuming any extra mathematical property of A.
No statement dispute or node fault was found.

Searches (all performed through the prescribed wrappers or read-only rg):

- LeanFinder via msearch.py: "A distinguished triangle G to X biproduct Y to Y
  with second map (h,-identity) has first projection G to X an isomorphism and
  cohomology equal to the graph". Eight hits, including
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`,
  mapping-cone triangle comparisons, and short-exact-sequence triangles;
  none is the prescribed projection and graph assertion.
- LeanSearch via msearch.py: "In a distinguished triangle the fibre of
  (h,-identity) from X direct sum Y to Y is isomorphic to X by the first
  projection". Eight hits, including the binary biproduct triangle,
  `exists_iso_binaryBiproduct_of_distTriang`, and `ShortExact.singleTriangle`;
  none states these fixed projections with their graph identifications.
- Loogle via msearch.py:
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`.
  One exact name hit. Read the theorem: it assumes a zero third arrow and gives
  an unspecified splitting with a different middle-object decomposition.
  It does not itself assert either prescribed fibre projection or cohomology
  graph formula.
- Mathlib grep via msearch.py: `split.*epi|IsSplitEpi|SplitEpi` in
  `CategoryTheory/Triangulated`. Three hits, the split-epi-category instance and
  the splitting theorem proof; no exact match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for split-fibre/projection names,
  graph-kernel phrases, and the exact node id. General split-projection or
  graph-kernel hits concern different statements; no match for this node.
  A narrower rg of their CategoryTheory subtrees and `dag/lean_names_upstream.json`
  for `split_fibre_projections|splitFibreProjections|derived.*split.*fibre|graph.*kernel`
  returned no hits. The new declaration name does not occur in those sources.

Validation: the module is compiled separately on the server using scompile.py.
The initial namespace error for the canonical comparison was corrected to
`Functor.biprodComparison`; the final file has explicit universe and variable
binders, one sorry-only theorem, no local notation or instances, and lines at
most 100 characters. The signature in the node's `lean.statement` is copied
verbatim from `theorem` through the text before `:=`.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
