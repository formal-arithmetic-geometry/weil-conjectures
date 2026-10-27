## Worker report

`Sheaf.AlgebraicGeometry.AlterationCoverCalculus` states
`AlgebraicGeometry.PrimeToEllAlteration.alteration_cover_calculus` with the single proof
`sorry`. No definitions are introduced. Only the item's `lean` field changes. The theorem
is an eleven-part conjunction; its docstring includes all eleven natural-language proof
steps with their dependency ids.

The source was read directly in ILO, Travaux de Gabber, Exposé II, printed pp. 24–28:
Definitions 1.1.8 and 1.2.2, 1.2.5–1.2.8, Corollary 2.2.4 and 2.3.1–2.3.4.
The PDF was extracted into this item's sandbox. Remark 2.3.2 warns that the two raw
classes of generators do not themselves compose. The proof plan therefore uses their
finite-tree closure. Section 2.3.4 states flat ordinary base change; the node's dominant
possibly nonflat integral variant is the expansion in its proof steps 7–8, using dominant
reduction and the generator argument. This variant is preserved without adding flatness.
There is no statement correction or disputed statement.

The item has an old Q45 review and report but no current Lean record. Searches found no
remaining declaration, and `scompile.py --source Sheaf.AlgebraicGeometry.AlterationCoverCalculus`
returned `Module source unavailable`. The old report was read as historical context; this
delivery supplies the missing module and binding, checked against the current node and
current dependency source.

Hypotheses and clauses, in the order of the theorem's conjunction:

1. The global hypotheses are `(S : Scheme.{u}) [IsNoetherian S]` and
   `(ell : ℕ) [Fact ell.Prime]`. All objects use the recorded `Alt S` category.
   Finite composition quantifies over `I : Type w`, `[Finite I]`, `J : I → Type w'`,
   `[∀ i, Finite (J i)]`, families `U`, `V`, and arrows `f`, `g`. The two hypotheses
   `IsCoveringFamily ell U f` and `∀ i, IsCoveringFamily ell (V i) (g i)` yield the
   covering family indexed by `Sigma J`, with composites `g ij.1 ij.2 ≫ f ij.1`.
   This index is finite as the dependent sum of finite types over a finite type.
2. Covering refinements use the same outer and inner families without finiteness assumptions,
   and a further family `W : K → Alt S` with `K : Type w''`. `Refines` of the composites
   into `W` means every composite factors through a member of `W`. Both covering hypotheses
   imply `IsCoveringFamily ell W h`. Taking `W` equal to the composites includes composition
   for arbitrary covering families, hence in particular refinement of a cover by covers.
   The direction agrees with the dependency's definition of `Refines`.
3. A covering sieve `R : Sieve T`, with `R ∈ topology S ell T`, contains a family indexed
   by `Fin n` with `IsCoveringFamily ell U f` and `∀ i, R (f i)`. This says the finite
   contained family itself covers; it is not just a finite family of arbitrary sieve arrows.
4. For arrows `f : X ⟶ T`, `g : Y ⟶ T`, existential `P`, `p`, `q` have
   `IsPullback p q f g` in `Alt S`. The comparison `j` into the ordinary scheme
   `pullback f.hom.left g.hom.left` is a closed immersion, compatible with both projections.
   Its exact image is the union of irreducible components `c` for which the closure of the
   image under the map to `T.obj.left` is an irreducible component of `T.obj.left`.
   Together with reducedness of `P : Alt S`, this gives precisely the reduced union of
   dominating components, with the categorical universal property. It does not merely
   assert containment in that union or the existence of an arbitrary comparison map.
5. For a covering family `f` and an arbitrary arrow `g : Y ⟶ T`, any family of squares
   `∀ i, IsPullback (p i) (q i) (f i) g` has covering second projections `q`.
   This uses the categorical pullbacks from clause 4, allowing any isomorphic choice.
6. Dominant integral base change quantifies over `S' : Scheme.{u}`, `[IsIntegral S]`,
   `[IsIntegral S']`, `[IsNoetherian S']` and `a : S' ⟶ S` with `[IsDominant a]`,
   `[LocallyOfFiniteType a]`, `[QuasiCompact a]`. The base S already is Noetherian.
   An existential functor `F : Alt S ⥤ Alt S'` has closed-immersion comparisons `j X`
   into `pullback X.obj.hom a`. Their exact image is the union of components whose
   second-projection image has closure `Set.univ`; as S' is integral this means domination.
   The second-projection equation fixes the structure map. The equation for `F.map f`
   fixes compatibility with the original arrow and first projections. Along with the
   over-category structural equation these pin down the morphisms canonically. Reducedness
   follows from `F.obj X : Alt S'`. The final implication says every covering family maps
   to a covering family. Thus this is the specified reduced dominant operation, without a
   flatness assumption or an arbitrary cover-preserving functor substituted for it.
7. A proper surjective arrow `f` between integral objects has a singleton cover when every
   source generic residue-field map is finite and `Nat.Coprime (f.hom.left.residueDegree x)
   ell`. Generic points are characterized by singleton closure being an irreducible component.
   For an integral source this is the unique generic point, so the condition is precisely
   finite generic degree prime to ell. Finiteness is explicit; the natural-number degree's
   default for infinite extensions cannot be used instead. The singleton is indexed by
   `Fin 1`. These are arrows between alteration objects, as the node's proof step 9 specifies.
   For a standalone morphism to an integral Noetherian target X, apply the assertion in
   `alt/X`; the source and the identity of X are then the relevant objects.
8. Proper birational arrows between integral objects cover as singletons. Birationality is
   expressed by a dense target open `V` with `IsIso (f.hom.left ∣_ V)`. For these finite-type
   integral Noetherian schemes this is the usual birational condition. Surjectivity follows
   from properness and dominance; it is not imposed as an extra hypothesis here.
9. Finite affine open covers are encoded by `[Finite I]`, affine `(U i).obj.left`, open
   immersion arrows `(f i).hom.left`, and joint surjectivity
   `∀ t, ∃ i x, (f i).hom.left x = t`. This exact family is concluded covering.
10. The reduced component family uses an equivalence
    `e : Fin n ≃ {c : Set T.obj.left // c ∈ irreducibleComponents T.obj.left}`.
    Each arrow is a closed immersion with exact image `(e i).1`. Reducedness of each source
    is inherited from its alteration object, so the arrows are the reduced induced component
    subschemes, uniquely determined up to isomorphism. Every component occurs exactly once,
    and the whole family is covering.
11. Every `T : Alt S` is asserted reduced, locally of finite type and quasi-compact over S,
    and its generic points map to generic points of S with finite residue-field extensions.
    This is the recorded category definition, with no independent duplicate predicate.

Dependency declarations inspected:

- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`: the full source was read,
  including `AlgebraicGeometry.PrimeToEllAlteration.Alt`, `topology`,
  `IsCoveringFamily`, `Refines`, and the two generator predicates. These are used directly.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  `AlgebraicGeometry.IsIntegral`; their full fields and docstrings were read.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity uses
  `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsNoetherian` and
  `isNoetherian_iff_of_finite_iSup_eq_top`, matching a finite affine Noetherian cover.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `.QuasiCompact`: `QuasiCompact`; finite type is their conjunction, as recorded.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`; universal closedness supplies
  quasi-compactness, so its locally-finite-type field gives finite type.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; `.Integral`: `IsIntegralHom`.
  These affine-local signatures were read. They serve the proof of the component-cover
  clause rather than adding a finite/integral-map hypothesis to the main theorem.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; the full signatures and docstrings were read. `IsPullback` expresses the
  categorical universal property; ordinary scheme pullbacks are Mathlib's construction.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, the recorded Mathlib match even
  though its node has no `lean` record. `irreducibleComponents` is maximal `IsIrreducible`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.Hom.residueFieldMap`, `residueDegree`.
- Proof-only imports include the recorded
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`, with
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme` (read in full),
  `Sheaf.CategoryTheory.Sites.GrothendieckTopos`, and Mathlib's
  `PrecoverageToGrothendieck`, `Sites.MorphismProperty`, `AlgebraicGeometry.Limits`,
  and `Morphisms.Integral`. The other Mathlib proof leaves are supplied transitively by
  these imports and the public statement imports. Four proof prerequisites have no usable
  declaration recorded: generic-fibre finiteness, dominant coreflection, residue-degree
  base change, finite extraction. They are named in the proof docstring, not invented as
  hypotheses. They are not required to type this statement, so no interface repair is needed.

Edge cases checked before writing:

- Empty schemes and empty index types are included, with no `Nonempty` hypothesis. `Fin 0`
  is permitted for both finite extraction and the empty reduced component family. The empty
  affine family over an empty scheme is also covered. Object generic-point clauses are
  vacuous on empty sources, exactly as in the recorded category.
- A nonreduced Noetherian base S is permitted outside clause 6; there is no silently assumed
  identity object of `Alt S` or reducedness of S. Only the dominant-base-change clause
  requires integral bases, as in the node.
- No separability, regularity, excellence, characteristic restriction or invertibility of ell
  is added. Purely inseparable finite extensions are allowed.
- Proper birational identities, affine identities, and nonflat dominant finite-type base
  changes are included. The generic-degree clause retains explicit finiteness.
- All universes `u w w' w''` and every binder are explicit, with `autoImplicit false`.
  Index universes are independent; the finite extracted families use `Fin n`.
- Both reduced constructions are pinned by closed immersion plus exact support, so empty,
  larger, nonreduced, or arbitrary maps cannot replace the intended reduced subschemes.

Searches performed in this session:

- `msearch.py leanfinder`: “Prime to ell alteration covering families compose, pull back by
  dominant reduced fibre products, admit finite refinements, and cover by irreducible
  components”. Eight results, headed by `Scheme.zariskiPrecoverage` and
  `Scheme.jointlySurjectivePrecoverage`; no exact alteration theorem.
- `msearch.py leansearch`: “Covering families in the prime to ell alteration topology are
  stable under composition and dominant reduced base change and every covering sieve
  contains a finite covering family”. Eight generic precoverage/composition results;
  no exact alteration statement. Mathlib's generic results supply only parts of the proof.
- `msearch.py loogle`: `GrothendieckTopology.transitive, Sieve.generate,
  Presieve.ofArrows` returned no hits and unknown identifier for the first name.
  The fully qualified `CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`
  returned the existing recorded proof leaf; its source signature was read.
- `msearch.py grep`: `alteration|Alteration` in Mathlib AlgebraicGeometry returned no hits.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `alteration_cover_calculus|alterationCoverCalculus` returned no match. Wider alteration
  searches found the topology, dominant-part definition and different specialized results,
  but no theorem stating this calculus. The upstream declaration-name table likewise had no
  matching name. The full `DominantPart` module was read: it is a construction of a reduced
  subscheme, not this eleven-clause theorem.

Validation: `scompile.py NE lem-per-alteration-cover-calculus` compiled both its sandbox
probe (2.5 seconds) and its intended library-module form (2.6 seconds), with no diagnostics.
The final signature is copied verbatim into `lean.statement`. There are no lines over 100
characters, no auto-implicit binders, and no definitions or proofs besides the named theorem's
expected `sorry`. The required dry run and delivery are performed after this report.

## Second reading by NE

No second agent was started: this assignment explicitly forbids it and delivers directly for
independent maintainer review. I reread the final signature against the node as an author
self-check. The eleven correspondences above were checked, especially the direction of
`Refines`, both pullback projection equations, exact component support, generic finiteness
in addition to coprimality, and the functor and both base-change compatibility equations.
No statement correction, new definition node, dependency repair, or mathematical mismatch
was found. This is an author self-check, not a claim of independent review.
