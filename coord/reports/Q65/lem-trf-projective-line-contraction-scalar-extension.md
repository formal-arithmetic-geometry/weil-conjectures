## Worker report

Item: lem-trf-projective-line-contraction-scalar-extension. The module
`Sheaf.AlgebraicGeometry.ProjectiveLineContractionScalarExtension` states three clauses
of this one node, with a `sorry` proof for each. It introduces no definitions or axioms.
The item JSON changes only in `lean`. No statement correction, new node, or dependency
repair is needed.

Sources read: the entire node and its five proof steps; all eight statement-dependency
nodes and their recorded interfaces; the proof-dependency records; Stacks
`schemes.tex`, Tag 01JE (`example-projective-line`, especially the explicit calculation
Γ(P¹, O) = k), Tag 01I1 (`lemma-morphism-into-affine`); `morphisms.tex`, Tag 01S1
(`lemma-base-change-surjective`). The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
was also read. This item is an auxiliary contraction assertion, not that unit's own
statement. The source's note that the Temkin PDF is unavailable does not prevent
stating this elementary application of the supplied Stacks sources.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| k algebraically closed field | `(k : Type u) [Field k] [IsAlgClosed k]` in all three declarations |
| L/k field extension | `(k L : Type u) [Field L] [Algebra k L]` in the scalar-extension and component declarations |
| Any k-scheme X | `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; its structure map is `X ↘ Spec (.of k)` |
| Projective line, with its existing standard cover | `ProjectiveLine (Spec (.of k))`; import `ProjectiveSpace.TransitionUnits`, whose `ProjectiveLine.TwistData` uses exactly this relative model and its standard opens |
| r a k-morphism | `(r : ProjectiveLine (Spec (.of k)) ⟶ X) [r.IsOver (Spec (.of k))]` |
| Image is the particular singleton {x} | `(x : X) (hx : Set.range r = {x})` |
| x is k-rational | Existential `a : Spec (.of k) ⟶ X`, with `a ≫ X ↘ Spec (.of k) = 𝟙 _` and `Set.range a = {x}` |
| r factors through the structure morphism and that point | `(ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ a = r` in `exists_rationalPoint_of_range_singleton` |
| Canonical scalar extension r_L | `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map (r.asOver (Spec (.of k)))).left` |
| Target X ×_k L | `pullback (C := Scheme.{u}) (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k L)))` |
| Scalar extension has singleton image, and conversely | The two directions of `range_singleton_scalarExtension_iff`, each side existentially quantifying the singleton's point |
| Any k-morphism f : C → X | `C X : Scheme.{u}`, their `Over` instances, and `(f : C ⟶ X) [f.IsOver (Spec (.of k))]` |
| Reduced closed component R ⊆ C | `R : Scheme.{u}`, `[IsReduced R]`, `(i : R ⟶ C) [IsClosedImmersion i]`, `hi : Set.range i ∈ irreducibleComponents C` |
| Component is isomorphic to P¹_k over k | `(e : ProjectiveLine (Spec (.of k)) ≅ R) [e.hom.IsOver (Spec (.of k))]`, with R's structure and `[i.IsOver (Spec (.of k))]` |
| Assertions apply to f restricted to R | `component_range_singleton_scalarExtension` asserts both the rational-point factorization for `i ≫ f` and the singleton-image equivalence for its canonical scalar extension |
| No properness, separatedness, finite type or reducedness on X | None of those instances or hypotheses is present on X |

The source of the canonical scalar extension is literally P¹_k ×_k Spec L. This
is precisely the node's P¹_L: the recorded relative projective-space model has
`ProjectiveSpace.isPullback_map`, with top map `ProjectiveSpace.map`, structural
map to Spec L, and the two specified projections. Thus no arbitrary morphism,
comparison assumption, or independent choice replaces base change. The target is
literally the fibre product as well. The component base change is `(i ≫ f)_L`,
which is the restriction `(f_L)|_(R_L)` by functoriality of the same pullback functor.

A reduced closed immersion with irreducible-component image is exactly a presentation
of the reduced induced component in the node. The uniqueness clause of the recorded
`reduced_induced_closed_subscheme` identifies it with that canonical presentation.
The component theorem does not add a smoothness, dimension, finite-type, or properness
hypothesis on C. Its component and reducedness hypotheses come from the node, even
though the argument would apply more broadly to an isomorphic copy of P¹.

Dependency declarations read and used (the corresponding modules are imported):

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveLine`, its canonical structure map, and
  `AlgebraicGeometry.ProjectiveSpace.isPullback_map`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  `AlgebraicGeometry.ProjectiveLine.TwistData`, the recorded standard-cover interface.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`, `.map`.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `CategoryTheory.Over.pullback`;
  its definition maps arrows by the unique pullback lift with the original arrow
  on the first projection and the identity on the second.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  field clause of def-weil-algebraic-closure's Mathlib match. No algebraic closure
  of a second ground field is asserted or needed here.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`, and
  `Scheme.Hom.asOver`; `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  including its final uniqueness clause for any reduced closed immersion.
- Proof imports: `WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine`
  (`ProjectiveLine.nonempty_H_zero_twist_equiv` and the other recorded monomial clauses);
  `Mathlib.AlgebraicGeometry.OpenImmersion` (`IsOpenImmersion`);
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (`ΓSpec.adjunction`);
  `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`
  (`lem_nagata_affine_proj_scalar_extension`);
  `Mathlib.AlgebraicGeometry.Scheme` (`Spec`, `Spec.map`);
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (`Surjective` and its
  nonempty-source/subsingleton-target instance);
  `Mathlib.AlgebraicGeometry.PullbackCarrier` (surjectivity stable under base change).

Edge cases checked before and after writing:

- X = Spec k: the structure morphism has singleton image, factors through the identity
  point, and the extension has the unique Spec L point as image.
- X empty: there is no morphism r from the nonempty projective line, so the statement
  imposes no false nonemptiness assertion on arbitrary X.
- X nonreduced, e.g. Spec k[ε]/ε²: the affine factorization uses Γ(P¹, O) = k;
  no reducedness assumption on X is necessary or inserted.
- X nonseparated: an affine open around the singleton image suffices; separatedness
  is neither used nor assumed.
- r the identity of P¹: both singleton conditions are false. The criterion does not
  assert all morphisms are constant.
- L = k, positive characteristic, transcendental L/k, and non-algebraically-closed L:
  none is excluded. Only k is required to be algebraically closed, exactly as in the node.
- C may itself be nonreduced; only its selected component R has reduced structure.
- Scheme and coefficient types use the common ambient universe u required by the
  existing Scheme/Over interface. Any given k, L and schemes fit in a common larger
  universe; no independent smaller test universe or test-object quantifier is used.

Searches actually made using the prescribed msearch.py wrapper:

- LeanFinder: “A morphism from projective line with singleton image factors through a
  rational point and contraction is preserved and reflected by extension of the ground
  field”. Eight hits, including `WeierstrassCurve.Projective.comp_equiv_comp`,
  `AlgebraicGeometry.Proj.valuativeCriterion_existence` and rational-map results.
  None states this node.
- Loogle: `AlgebraicGeometry.Scheme.Hom, Set.range, Set.singleton`. Zero hits.
- Mathlib grep: `singleton.*(image|range)|[Pp]rojective[Ll]ine.*constant`, subdirectory
  `AlgebraicGeometry`. Fourteen hits: zero-locus simplification, quasi-finite fibre
  finiteness, geometric irreducibility, elliptic-curve functoriality, group schemes.
  No singleton-image factorization or contraction criterion.
- LeanSearch: “A morphism from the projective line with singleton image factors through
  a rational point, and this property is preserved and reflected by field extension”.
  Eight hits, mainly Weierstrass functoriality; also
  `Scheme.range_fromSpecResidueField`, which only constructs a residue-field point
  and does not assert k-rationality or factorization of r. No exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for projective-line constants,
  singleton images/ranges and contraction; and direct item-id search in
  `lean/WeilConjectures`. No exact statement. Broad searches also locate unrelated
  module contractions and the already existing semistable-curve consumer.

Validation: scompile.py compiled both the sandbox and the named library module cleanly
against the live published build. No warnings beyond the permitted sorry warnings.
An initial shorthand `Spec.map (.ofHom ...)` was corrected to `CommRingCat.ofHom`;
the existential pullback point also needed explicit `(C := Scheme.{u})` to avoid
Lean inferring the category of types. Neither change affects the mathematics.
No `#check`, local notation, local instance, hidden definition, or auto-bound variable
remains. All three proof bodies are exactly `by sorry`.

## Second reading by Q65

The dispatcher assigned a single worker, so the group's own section was a self-check.
This section is the clause-by-clause reading of the maintainer's independent second
reader (cc review service, 2026-10-24). The Lean module is unchanged.

Node clauses and their Lean renderings:

1. k is an algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]` (Mathlib's
   class behind def-weil-algebraic-closure). Correct.
2. L/k is a field extension: `[Field L] [Algebra k L]` (def-pc-field-extension record). Correct;
   L is not required to be algebraically closed, algebraic or separable.
3. X is any k-scheme: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. There is no properness,
   separatedness, finite type or reducedness instance on X. Correct.
4. P^1_k with its standard charts: `ProjectiveLine (Spec (.of k))`, i.e. the relative model
   `ProjectiveSpace` of def-nagata-projective-space-base-change with its `CanonicallyOver`
   structure map; the recorded def-sc-p1-standard interface `ProjectiveLine.TwistData`
   uses this same model and `standardOpen`. Correct.
5. r is a k-morphism: `(r : ProjectiveLine (Spec (.of k)) ⟶ X) [r.IsOver (Spec (.of k))]`. Correct.
6. Singleton image {x} ⇒ x is k-rational and r = (point) ∘ (structure map):
   `exists_rationalPoint_of_range_singleton` gives `a : Spec k ⟶ X` with `a ≫ X ↘ Spec k = 𝟙`
   (a k-point), `Set.range a = {x}` (that point is x) and `(P ↘ Spec k) ≫ a = r`. This is
   exactly the node's clause; a k-section with image x is the same as κ(x) = k. Correct.
7. r_L : P^1_L → X ×_k L, and singleton image is preserved and reflected:
   `range_singleton_scalarExtension_iff`. r_L is `((Over.pullback (Spec.map (algebraMap k L))).map
   (r.asOver _)).left`, the canonical base change through def-pc-fibre-product's `pullback`.
   Its target is literally `pullback (X ↘ Spec k) (Spec.map …)` = X ×_k L. Its source is
   P^1_k ×_k Spec L, which the cited proof (lem-nagata-affine-proj-scalar-extension,
   `ProjectiveSpace.isPullback_map`) identifies with P^1_L compatibly with the projections.
   Being a singleton image is invariant under this canonical isomorphism, so the statement
   neither weakens nor strengthens the node. Both directions are existential singletons, as
   the node says "has singleton image". Correct.
8. Application to f|_R for a reduced closed component R ⊆ C isomorphic to P^1_k:
   `component_range_singleton_scalarExtension`. It has `IsReduced R`, `IsClosedImmersion i`,
   `Set.range i ∈ irreducibleComponents C`, and the k-isomorphism `e` with `e.hom.IsOver`.
   By the uniqueness clause (3) of lem-weil-pbc-reduced-induced-closed-subscheme, such an
   `i` is the reduced induced structure on the component. Both conclusions (factorization
   and the equivalence) are stated for `i ≫ f` = f|_R. Its base change `(i ≫ f)_L` equals
   f_L|_{R_L} by functoriality of `Over.pullback`. Reading "isomorphic to P^1_k" as an
   isomorphism over k matches the proof's Step 5 ("the given k-isomorphism"). Correct.

Edge cases: X empty (there is no r, since P^1 is nonempty); X = Spec k; X = Spec k[ε]
(nonreduced, still covered); non-separated X; r = id_P (both sides false); L = k; L
transcendental or not algebraically closed; any characteristic; C nonreduced. None of
these is excluded or mis-stated. Universes: k, L and all schemes are in the common
universe u, which the Scheme/Over interface requires. There is no extra universe
restriction, and no variable is left unbound (`autoImplicit false`).

Records: the item `lean.statement` is verbatim the signature of
`range_singleton_scalarExtension_iff`. The three declarations are listed. All eight
stmt_deps are mathlib/imported/unsplit records whose declarations are the ones used.
There are no new nodes and no dependency modules. All proofs are `sorry`. The
docstrings carry the source place, `(blueprint: …)` and the proof steps.

Searches: the worker's searches, plus rg in lean/WeilConjectures for singleton
ranges of ProjectiveLine morphisms. There is no existing declaration.

Mismatches found: none in the Lean or the records. The only change is this report section.
