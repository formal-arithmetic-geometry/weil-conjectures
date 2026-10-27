## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSectionUniversalJetDensity` states
`AlgebraicGeometry.Smooth.isIso_of_section_jets_factor`, with its entire proof
postponed by `sorry`. It introduces no definitions or auxiliary theorems.
The node is unchanged except for `lean`.

Source read: Conrad, *Reductive group schemes*, author PDF
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
Definition 2.1.7, printed p.61, and proof of Proposition 2.1.6,
printed pp.62--63 (PDF pages 61--63, zero-based 60--62).
The definition says that the only closed subscheme containing the family is
the whole scheme; the proof explicitly asserts persistence after arbitrary
base change, and its affine reduction supplies precisely the present assertion.

Hypotheses and clauses, read against the node:

- Noetherian commutative ring A: `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`. No nontriviality assumption is made on A.
- `S = Spec A` is written `Spec (.of A)` everywhere. Likewise
  `(B : Type u) [CommRing B]` and `Spec (.of B)` implement the specified
  affine presentation `Y = Spec B`.
- The given smooth affine morphism is
  `(p : Spec (.of B) ⟶ Spec (.of A)) [Smooth p]`.
  A morphism between affine schemes is affine, hence quasi-compact and
  quasi-separated. `[LocallyOfFinitePresentation p]` therefore renders
  finite presentation exactly; it imposes no extra condition beyond the
  node (and also follows from smoothness).
- The section and its ring retraction are `(ε : B →+* A)` and
  `hε : Spec.map (CommRingCat.ofHom ε) ≫ p = 𝟙 (Spec (.of A))`.
  Thus `e` is literally `Spec.map ε`. The anti-equivalence for affine
  schemes identifies this equation with the retraction equation for the
  ring map inducing p, so no extra algebra structure or compatibility
  hypothesis is being assumed or omitted. Every section of this p has
  this form by `Spec.map_surjective`.
- Nonempty geometrically connected fibers: `hgeom` quantifies over
  `s : Spec (.of A)` and asserts `ConnectedSpace` of the pullback of p
  along `Spec (AlgebraicClosure (S.residueField s)) → S`.
  That map is `Spec.map (algebraMap _ _) ≫ S.fromSpecResidueField s`.
  By associativity this is the fiber over s extended to its algebraic
  closure, precisely the explicit convention in the node. `ConnectedSpace`
  includes nonemptiness; there is no separate reducedness assumption.
- The ideal J is directly `RingHom.ker ε`; its (n+1)-st power is
  `RingHom.ker ε ^ (n + 1)`, with `n : ℕ`, including zero.
  `Ideal.Quotient.mk` is the actual quotient homomorphism B → B/J^(n+1),
  and `Spec.map (CommRingCat.ofHom ...)` is its closed immersion into Y.
- Any S-scheme T is `{T : Scheme.{u}} (g : T ⟶ Spec (.of A))`.
  There is no Noetherian, reducedness, affineness, or nonemptiness
  assumption on T. The ambient base change is exactly `pullback p g`.
- Any closed subscheme is represented by
  `{Z : Scheme.{u}} (i : Z ⟶ pullback p g) [IsClosedImmersion i]`.
- For each n, `hjets` gives a morphism `l` from
  `pullback (Spec.map (Ideal.Quotient.mk ...) ≫ p) g` to Z.
  This domain is exactly Y_n ×_S T, with its induced structure map to S.
  The first equality specifies the Y-component of `l ≫ i` as the
  projection to Y_n followed by the actual quotient immersion into Y;
  the second equality specifies its T-component as the T-projection.
  By uniqueness in the pullback, these two equalities are equivalent to
  `l ≫ i` being the canonical base-changed quotient immersion. Thus this
  is exactly the requested factorization, with no arbitrary replacement
  map and no forgotten compatibility with T.
- `IsIso i` expresses that this closed subscheme is the whole ambient
  scheme, with its full scheme structure. In the poset of closed
  subschemes it is equality to the top element. Equality of underlying
  sets alone would be insufficient; the asserted isomorphism is over the
  ambient scheme because it is the very immersion i that is invertible.
  The node's final “in particular” sentence repeats this same conclusion
  and needs no additional conjunct or second theorem.

All universe parameters and variables are explicit. A, B, T and Z are in
one common arbitrary scheme universe u, as in the dependency declarations;
this permits the common enlargement used for arbitrary schemes and rings.
The algebraic closure and residue field remain in that same universe.
There is no independently smaller universe of test objects.

Statement dependencies used, after reading the recorded signatures/docstrings:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  the scheme pullback instance is supplied by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-connected-scheme`: the Mathlib match `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic` (the record is a mathlib_match,
  so no replacement Lean record is needed).
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.

Additional standard constructions are `Scheme.residueField` and
`Scheme.fromSpecResidueField` from `Mathlib.AlgebraicGeometry.ResidueField`,
`AlgebraicClosure` from `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
and the existing ideal quotient construction. None is redefined.

Proof dependencies that have recorded declarations or Mathlib matches are
imported with plain `import`: the algebraic-closure connectedness criterion,
Slicing's `Smooth.exists_geometricallyIrreducible_of_section`, the geometric
integrality module, `pullbackSpecIso` (already a public statement import),
`Scheme.Hom.IsFiniteLocallyFree`, `Flat.SpecMap_iff`, smooth-flatness,
`smooth_at_point_pullback_snd_iff_of_flat`, source-locality of smoothness,
`finitePresentation_appLE` (already public), `TensorProduct`,
`Algebra.FiniteType.isNoetherianRing`,
`RingTheory.krull_intersection_localization`, and
`Module.Flat.lTensor_exact` / `rTensor_exact`.
`lem-sfb-smooth-section-finite-jets` and
`lem-sfb-smooth-fibrewise-dense-open-base-change` currently have neither
Lean records nor Mathlib matches in the read clone, so there is no module
of either to import. They are proof-only prerequisites; the present statement
uses neither theorem's interface. Both remain named in the proof docstring
and in the unchanged DAG proof dependencies. No statement prerequisite is missing.

Edge cases checked before drafting:

- Empty Spec A, including the zero ring: hε forces Y empty too;
  the fiber hypothesis has no points and the conclusion is valid.
- Empty T: its pullback is empty and every closed subscheme is the whole
  empty scheme. No `Nonempty T` was added.
- The identity section Y = S: J = 0, every quotient is B itself, so already
  the n = 0 factorization forces i to be an isomorphism.
- The affine line with its zero section: the quotients are B/(t^(n+1)),
  exactly the intended finite jets. n = 0 is retained.
- Nonreduced A or T (e.g. dual numbers), and a non-Noetherian base change
  such as an infinitely generated polynomial algebra: both are allowed.
  The proof uses flatness of the finite jets to descend an individual
  element to one finite-type subalgebra, not commutation of an infinite
  intersection with tensor product.
- Disconnected fibers cannot be admitted: for Y = S disjoint-union S and
  a section in the first component, that component contains every jet
  and is a proper closed subscheme. hgeom correctly excludes this case.
- No characteristic, relative-dimension, or bound on n is imposed.

Searches actually run:

- `msearch.py ... leanfinder`, query “Infinitesimal neighborhoods of a
  section of a smooth affine scheme with geometrically connected fibers
  are universally weakly schematically dense”: 8 hits on formally
  unramified morphisms, étale morphisms and smooth charts; no match.
- `msearch.py ... loogle`, query `AlgebraicGeometry.Smooth, Ideal`:
  0 hits; no match.
- `msearch.py ... grep`, query `weakly.*schem|jet.*dens|iInf_pow`:
  11 hits, on weakly étale morphisms and adic/Noetherian intersection
  lemmas; none states the relative universal density assertion.
- `msearch.py ... leansearch`, query “The infinitesimal neighborhoods of a
  section of a smooth affine morphism with connected geometric fibers
  are weakly schematically dense after every base change”: 8 hits,
  concerning smoothness, formal unramifiedness and a dense subsite;
  no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for jets,
  weak schematic density and the proposed declaration name: no matching
  statement. Other jet results concern tangent cones, distributions,
  singularities or finite-jet smoothness, not this assertion.
- `rg` for the item id in `lean/WeilConjectures`: no hits.
- Searched `dag/lean_names_upstream.json` for geometric/jet/schematic
  declarations; no exact existing universal section-jet density statement.

No statement dispute, correction, new node, or dependency repair is needed.
The module passed `scompile.py` in both sandbox and final-library module mode
(3.6 s and 10.1 s respectively), with no errors or unexpected warnings.

## Second reading by Q154

This is a single-worker rereading of the node and the completed Lean file;
the delivery receives its independent review from the maintainer.
I reread the displayed signature against each clause above. In particular:
`hgeom` uses the algebraic closure of each residue field, not merely the
ordinary fiber; `hε` is a section of the actual p; the power is n+1;
the base-changed domain is the original jet pulled back along the actual g;
both projections of the factorization are fixed; and the conclusion is
invertibility of the actual closed immersion, not only surjectivity on
points or an unrelated isomorphism of schemes. Affine presentation and
finite presentation have their full stated scope. No mismatch was found,
and no node statement or dependency list was changed. The only postponed
proof is the one theorem attached to the item.
