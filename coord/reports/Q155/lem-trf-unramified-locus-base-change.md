## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange` states the complete
node, with one concrete helper definition and one theorem whose proof is `sorry`.
The helper `AlgebraicGeometry.unramifiedLocus h` is the union of all source opens
on which `h` is unramified, written as membership in some such open. It uses the
recorded `AlgebraicGeometry.IsUnramified`, without redefining unramifiedness.

The hypotheses and clauses correspond as follows:

- Schemes and the morphism are `{Z S : Scheme.{u}} (h : Z ⟶ S)`; local finite
  type is `[LocallyOfFiniteType h]`. The arbitrary scheme universe is explicit.
- The union in the node is `{z | ∃ O : Z.Opens, z ∈ O ∧
  IsUnramified (O.ι ≫ h)}`. Here `O.ι ≫ h` is the restriction on the source,
  with the original target S.
- Openness is the first conjunct `IsOpen (unramifiedLocus h)`.
- The fibrewise characterization is the second conjunct. Mathlib's `h.asFiber z`
  is exactly the point corresponding to z under the homeomorphism between the
  fibre at h(z) and the set-theoretic fibre. Its membership in
  `unramifiedLocus (h.fiberToSpecResidueField (h z))` says exactly that it has
  an unramified source neighbourhood in this scheme-theoretic fibre.
- The third conjunct is the equivalent local-ring/residue-field criterion.
  `IsIso ((h.fiber (h z)).residue (h.asFiber z))` says the canonical residue
  map of the fibre local ring is an isomorphism. Its target is the residue
  field of the corresponding fibre point, canonically identified with κ(z).
  The other two factors are `(h.residueFieldMap z).hom.Finite` and
  `Algebra.IsSeparable`, with the explicit algebra structure induced by that
  same residue-field map. Thus the field extension is the actual κ(z)/κ(h(z)),
  finite and separable, with no freely chosen algebra structure.
- The final conjunct quantifies over every `S'` and `k : S' ⟶ S`.
  `pullback.snd h k` is h', and `pullback.fst h k` is g'. It asserts exactly
  `unramifiedLocus h' = g' ⁻¹' unramifiedLocus h` for the chosen fibre product.
  Every other cartesian realization is canonically isomorphic to this one.
- No flatness, finite presentation, noetherianity, separatedness, or nonempty
  hypothesis is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
  The local source was missing, so its complete live source and docstring were
  read using `scompile.py --source`. Its interface is usable and is imported.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberToSpecResidueField`,
  `fiberHomeo`, and `asFiber`; the last is the inverse homeomorphism at z.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Hom.residueFieldMap`. The residue map is literally the local-ring quotient.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`,
  and `snd`, with the scheme pullbacks supplied by Mathlib's instance.

The two already stated proof dependencies are imported privately:
`WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen` and
`Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion`. The third
proof dependency is Mathlib's locally-finite-type base-change instance, already
available through the statement imports. The theorem docstring supplies both
DAG proof steps, the cited dependency ids, and the Stacks places.

Source read: `literature/stacks-project/morphisms.tex`, lines 7875–7980,
Tags 02GF (`lemma-unramified-at-point`) and 0475
(`lemma-set-points-where-fibres-unramified`). These assume only local finite
type for the unramified assertion; local finite presentation belongs to the
additional G-unramified version and is not imposed here.

Edge cases checked before the final statement: the empty source and empty
base change give empty loci and vacuous pointwise conditions; an open immersion
has its whole source as locus; a finite separable field extension gives its
unique point; an inseparable extension fails the separability factor; a
nonreduced fibre such as dual numbers fails the residue-map-isomorphism factor.
A ramified finite map excludes its ramification points. None of these cases is
excluded by an additional Lean binder.

Searches actually run in this attempt using `msearch.py Q155
lem-trf-unramified-locus-base-change`:

- LeanFinder: "For a locally finite type scheme morphism the unramified locus is
  open and commutes with arbitrary base change". Eight hits included
  `Algebra.isOpen_unramifiedLocus`, formally unramified scheme diagonal and
  permanence results; none states the whole scheme locus theorem.
- Loogle: `AlgebraicGeometry.IsUnramified`. Zero hits, reporting that identifier
  unknown to its index. The live project definition is nevertheless usable.
- grep: `unramifiedLocus|0475`, subdirectory `AlgebraicGeometry`. Zero hits.
- LeanSearch: "unramified locus of a scheme morphism commutes with arbitrary
  base change". Eight hits included `Algebra.Unramified.baseChange`,
  `Algebra.unramifiedLocus`, and scheme formally unramified stability under
  base change; no exact match for the pointwise locus statement.
- `rg -n 'unramifiedLocus|lem-trf-unramified-locus-base-change'` over the named
  upstream `WeilConjectures` and project `lean/Sheaf` directories found an
  algebra-level use and a downstream docstring citation, with no exact theorem.

No new independent notion, dependency repair, or statement correction remains
in this delivery. No STATEMENT-DISPUTED issue was found.

## Second reading by Q155

I reread the final node and file after correcting the draft. The draft had
omitted the residue-field characterization, had reversed the two pullback
projections, and tried to use the fibre homeomorphism in the wrong direction.
The final statement includes all four conjuncts, uses Mathlib's `asFiber` for
the canonical point, and uses `pullback.snd` for the base-changed structure
morphism and `pullback.fst` for the projection to Z. The fibre residue map is
specified, and finiteness/separability use h's own induced field extension.

The source restriction uses `O.ι ≫ h`, so it retains S as target. All variables
and the universe are bound with `autoImplicit false`; all declarations are
public. The sole postponed theorem has its source, blueprint id, and full
natural-language DAG proof in its docstring. Its helper definition has actual
data and the same source and blueprint id. A duplicate dependency module was
removed after the live recorded unramified definition was confirmed usable.
The item node changes only its `lean` record, whose signature is extracted
verbatim from the final file. No other node is delivered.
