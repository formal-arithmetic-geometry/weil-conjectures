## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.NormalDenseOpenFiniteTargetExtension`
states `AlgebraicGeometry.Scheme.existsUnique_extension_of_normal_dense_open_finite_target`.
It has one theorem, with proof `sorry`, and introduces no definitions. The item is unchanged
except for its `lean` record. No new nodes, dependency repairs, or statement corrections are needed.

Sources read: `literature/stacks-project/morphisms.tex`,
`lemma-characterize-normalization` (Tag 035I, lines 13936 onward), and
`lemma-equality-of-morphisms` (Tag 01RH, lines 1212 onward). The first gives the integral
factorization universal property used after base changing E over X. The second confirms that
uniqueness is relative over S and does not require S itself to be separated. The normal-source
identification is the recorded `Scheme.isIso_fromNormalization_denseOpen`, whose complete
signature and docstring were read in the upstream source. The six-step docstring in the new
module reproduces the node's proof: quasi-compactness of j, quasi-separatedness of j, integral
pullback T, normalization and its universal property, composition with the normalization
inverse, and uniqueness using that same universal property.

Hypotheses and conclusion, clause by clause:

- S, X, E and the open source U are arbitrary schemes: `{S X E U : Scheme.{u}}`, with
  `universe u` explicitly declared. The category of schemes uses a shared arbitrary size;
  no finite or countable size constraint is imposed.
- The arbitrary map n : X → S is `(n : X ⟶ S)`. There is no finiteness condition on n.
- The finite target map is `(p : E ⟶ S) [IsFinite p]`.
- X locally Noetherian is `[IsLocallyNoetherian X]`.
- Every local ring of X is an integrally closed domain is exactly
  `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`.
  This uses the normal-domain conjunction of the dependency's recorded inline form,
  applied directly to each local ring; it does not replace X by an integral scheme.
- The open immersion is `(j : U ⟶ X) [IsOpenImmersion j]`. Its dense image is
  `(hdense : DenseRange j)`. Mathlib `DenseRange` is definitionally `Dense (Set.range j)`
  (`Mathlib/Topology/Defs/Basic.lean:150`). U is not restricted to a chosen open-subscheme
  presentation, and the image is not required to equal X.
- Every compatible initial morphism is `(a : U ⟶ E) (ha : a ≫ p = j ≫ n)`.
  Category composition is left to right, so this is precisely p ∘ a = n ∘ j.
- Existence and uniqueness is `∃! b : X ⟶ E, b ≫ p = n ∧ j ≫ b = a`.
  Both the structure-map equation and the extension equation belong to the unique
  witness's predicate. It asserts uniqueness among S-morphisms extending a.
- The equivalent Hom-set bijection is expressed by this unique existence for every a:
  surjectivity gives an extension and uniqueness gives injectivity. No second conclusion
  or arbitrary map representing restriction is substituted for the equations.
- E is subject to no normality, reducedness, or nonemptiness hypothesis; S has no
  separatedness hypothesis; X has no nonemptiness, connectedness, or quasi-compactness
  hypothesis. Thus all explicit negative clauses of the node are retained.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (lines 42 and 74), for schemes and their morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (line 39), for the finite morphism. Its integral counterpart is `IsIntegralHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Integral` (line 35).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  (line 57), equivalent to the affine-cover presentation recorded on pqf-def-locnoeth.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`
  (line 74), together with `IsDomain` (`Mathlib/Algebra/Ring/Defs.lean:439`), for the
  recorded normal-domain conjunction. Each X.presheaf.stalk x is its local ring.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (line 38), the recorded scheme open-immersion predicate.

All five statement dependency modules are public imports. Plain proof imports retain the
recorded proof plan: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (the affine
quasi-compactness test), `Mathlib.AlgebraicGeometry.Pullbacks` (scheme fibre products),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (the diagonal test),
`Mathlib.AlgebraicGeometry.Normalization` (normalization, its two structure maps,
`normalizationDesc`, its two composition equations, and `normalization.hom_ext`), and
`WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDenseOpen`
(`Scheme.isIso_fromNormalization_denseOpen`). The noetherian-open and finite-implies-integral
proof dependencies are already in the corresponding public Mathlib imports; integral
base-change stability is in the integral-morphism import closure. No proof import is a
new copy of a dependency notion.

Edge cases checked mathematically before writing:

- X empty: density and the open immersion force U empty, and the unique map out of the
  empty scheme supplies the extension, even when E is empty.
- E empty and X nonempty: a map U → E would force U empty, contradicting density.
  The assertion remains correctly conditional on a and is vacuous in this case.
- Disconnected X, including arbitrarily many components: the stalk condition is pointwise
  and no `IsIntegral X` or finite-components assumption was inserted. Density meets each
  nonempty open component, as used in the normalization identification.
- j an isomorphism (including the full open): the extension is a composed with its inverse;
  the statement does not demand a nonempty complement or a proper open.
- E nonreduced: nothing in the signature excludes nilpotents in E. Maps from the reduced
  normal X still have the asserted uniqueness; the integral pullback argument applies.
- S nonseparated and n arbitrary: the proof uses the relative affine target q, rather than
  absolute separatedness of E or S.

Searches actually run (2026-10-24):

1. `msearch.py ... leanfinder` with “Every morphism from a dense open subscheme of a normal
   locally Noetherian scheme X to a finite S-scheme E extends uniquely over X”: eight hits,
   including relative normalization's universal property and relative separated uniqueness;
   none is this existence-and-uniqueness statement.
2. `msearch.py ... loogle '"normalizationDesc"'`: six hits on normalizationDesc, its
   integralness and composition equations, but no theorem identifying the normal source
   and giving this general extension statement.
3. `msearch.py ... grep` with
   `normal.*denseOpen|denseOpen.*[Ee]xten|[Ee]xten.*[Ff]inite|normalizationDesc`
   restricted to Mathlib AlgebraicGeometry: nine hits, principally normalizationDesc;
   no exact existing statement.
4. `msearch.py ... leansearch` with “Every S-morphism from a dense open of a locally
   Noetherian normal scheme to a finite S-scheme extends uniquely”: eight hits, including
   normalization.hom_ext, normalizationDesc and relative separated uniqueness; no match.
5. `rg` over the project's `lean/WeilConjectures` and `lean/Sheaf`, by the exact item id,
   extension/normal/dense/finite words and the proposed declaration name; also
   `dag/lean_names_upstream.json`. No existing public theorem with this statement or name.
   The broad query returned unrelated condensed-coefficient matches, so narrower searches
   in the algebraic-geometry directories were inspected as well.
6. Opened `WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso` and
   `FiniteNormalDenseOpenComparison`: their public results compare two finite normal
   schemes by an isomorphism and assume finiteness/normality on both sources. The private
   `extend_from_normalization` helper supplies existence only, under a chosen-open and
   normalization-isomorphism interface; it does not state this node and is not an exported
   replacement. Opened `NormalDenseOpenIntegralSection` too: it concerns integral sections,
   not arbitrary scheme morphisms. Their existing definitions and the recorded normalization
   theorem are reused through imports, with no duplicated construction.

Validation: `scompile.py Q47 lem-trf-normal-dense-open-finite-target-extension` passed
for the delivered file in sandbox mode (10.0 s) and library mode (2.6 s), with no errors
or unexpected warnings. There is no statement dispute or node fault.

## Second reading by Q47

I reread the final node copy and Lean file directly, in a separate review pass. This is a
single worker's second pass; the maintainer supplies the independent review requested in the
brief. The explicit morphisms n and p retain the node's base S; `IsFinite p` applies only to p.
`IsLocallyNoetherian X` and the conjunction on every stalk apply only to X. The independent
source scheme U and `[IsOpenImmersion j]` preserve every open-immersion presentation, while
`DenseRange j` is density of the actual image. The compatibility equation has the correct
composition order. The unique extension predicate includes both equations, so uniqueness is
neither absolute uniqueness of all maps X → E nor mere existence of a factorization.
The signature excludes none of the empty, disconnected or nonreduced-target cases above.
No hypothesis or conclusion mismatch was found, and no statement correction was made.
