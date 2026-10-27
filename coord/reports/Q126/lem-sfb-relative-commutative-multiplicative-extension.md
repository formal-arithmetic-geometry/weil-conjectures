## Worker report

The repaired delivery states `AlgebraicGeometry.relative_commutative_multiplicativeType_extension`
in `Sheaf.AlgebraicGeometry.RelativeCommutativeMultiplicativeExtension`, with one `sorry`.
It imports the existing `Sheaf.AlgebraicGeometry.RelativeMultiplicativeType` and reuses
`AlgebraicGeometry.IsRelativeMultiplicativeType` from the definition node landed by Q140.
It adds no definition or dependency module. The item's statement and twelve-step proof
are unchanged. Its statement dependencies gain the already-landed
`def-sfb-relative-multiplicative-type`.

## Repair of returned head 72306f2509fd

The sole return says that `def-sfb-relative-multiplicative-type` already exists on
sheaf-dag. I compared the retained delivery with the current item, read the complete
landed definition node and its module, and confirmed the current server source with
`scompile.py --source Sheaf.AlgebraicGeometry.RelativeMultiplicativeType`.
The current item differs from the retained item only in `lean` and `stmt_deps`.
The landed definition is from Q140 and uses an existential fppf covering family,
whereas Q126's returned definition used a chart through each base point. The landed
interface directly expresses the item's fppf-local definition, so it is usable as is.

I deleted the Q126 definition module and definition node from this sandbox. They are
not delivered, replaced, or re-recorded. The theorem continues to import the same
module path and name, now resolving to Q140's published declaration. I refreshed the
item copy from current main, preserving only Q126's theorem record and its additional
statement dependency. I also added the plain imports of two proof dependencies that
have since landed: `Sheaf.RingTheory.SubgroupAlgebraCosetPresentation` and
`Sheaf.AlgebraicGeometry.CompleteLocalDiagonalizableFibreHomLift`. This repair therefore
changes the actual dependency used, rather than re-pushing the returned packet.

## Statement correspondence

Source read for the original statement: Conrad, Reductive group schemes,
Definition B.1.1 (printed p.280), Corollary B.4.2(2) and proof (printed pp.299--301),
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . The relative commutative
case agrees with the node. This repair preserves that statement.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary scheme S | `{S : Scheme.{u}}` |
| E and D are S-group schemes | `(E D : Over S) [GrpObj E] [GrpObj D]` |
| E affine over S | `[IsAffineHom E.hom]` |
| E commutative | `[IsCommMonObj E]` |
| Homomorphism p respecting multiplication, identity and inverse | `(p : E ⟶ D) [IsMonHom p]`; a monoid homomorphism between group objects preserves inverse |
| p faithfully flat | `[Flat p.left] [Surjective p.left]`, precisely the node's flatness and surjectivity on underlying spaces |
| p locally of finite presentation | `[LocallyOfFinitePresentation p.left]` |
| Scheme-theoretic kernel with induced group structure | `Grp.mk (GrpObj.ker p)`; the upstream construction is the pullback along the identity section in `Over S`, with its induced `instGrpObjKer` |
| N multiplicative type of finite presentation | `hN : IsRelativeMultiplicativeType (Grp.mk (GrpObj.ker p))` |
| D multiplicative type of finite presentation | `hD : IsRelativeMultiplicativeType (Grp.mk D)` |
| E multiplicative type of finite presentation | `IsRelativeMultiplicativeType (Grp.mk E)` |
| No smoothness, connectedness, reducedness or characteristic restriction | No such binder or instance occurs |

The existing predicate is
`∃ (I : Type u) (R : I → CommRingCat.{u}) (f : ∀ i, Spec (R i) ⟶ S), ...`.
Its first conjunct is membership of `Presieve.ofArrows (fun i ↦ Spec (R i)) f` in
`Scheme.fppfPrecoverage S`: the maps are flat and locally finitely presented and their
images jointly cover S. Its second conjunct gives, for each chart, `M : Type u`,
`AddCommGroup M`, `AddGroup.FG M`, and a group-object isomorphism
`(Over.pullback (f i)).mapGrp.obj P ≅ ringDiagonalizableGroup (R i) M`.
Thus the predicate is exactly the node's fppf-local diagonalizability with finitely
generated characters. Refining each member of a splitting cover by its affine open
cover gives this form, and the node's glued relative spectrum restricts to precisely
this recorded ring-diagonalizable group. It is not merely a geometric-fibre condition.
The character group may vary with the chart and may have torsion.

## Dependencies

The statement uses these existing declarations, with their actual signatures and
docstrings read in the source:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`, flat locally finitely presented jointly surjective coverings.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`, the Hopf spectrum of
  `AddMonoidAlgebra R M` with canonical group-algebra Hopf operations.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.RelativeMultiplicativeType`:
  `AlgebraicGeometry.IsRelativeMultiplicativeType`, as described above. This is the
  declaration in the landed node's `lean` record; no repair of that record is needed.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`:
  `CategoryTheory.GrpObj.ker` and `GrpObj.instGrpObjKer`. These are general in a
  cartesian monoidal category with pullbacks, and apply to `Over S` unchanged.
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic` supplies pullbacks in
  `Over S`; no extra pullback-existence hypothesis is imposed.

All currently stated proof dependencies are imported as plain imports, preserving
module visibility. `lem-sfb-relative-diagonalizable-character-duality` and
`lem-sfb-multiplicative-type-fpqc-descent` still have no current Lean record; they are
not needed to type the theorem. The declaration docstring contains the complete
twelve-step node proof, including the Noetherian approximation, strict henselization,
completion, field case, character exact sequence, unique lifting, explicit fppf-local
surjectivity argument, fpqc descent, and spreading of a finite splitting family.

## Edge cases

The empty base admits an empty covering family (`I` may be empty); the definition
has no nonemptiness assumption. The zero ring is allowed. The zero character group
is allowed and gives the trivial group; no positive rank is required. Torsion
characters include infinitesimal mu_p in characteristic p, with no smoothness or
reducedness restriction. Disconnected bases allow different character groups on
different charts; disconnected groups are also allowed. No affine or Noetherian
hypothesis on S appears. Flatness and finite presentation of E are consequences
in the proof and are not added as hypotheses. All universes are explicitly u and
`set_option autoImplicit false` forbids implicit auto-bound variables.

## Searches

The original searches are retained in searches.jsonl. They were actually run:

- LeanFinder: “A commutative affine group scheme extension of groups of multiplicative
  type over an arbitrary scheme is of multiplicative type”. Eight hits about affine
  spaces, pulled-back group objects and abstract commutative groups; no exact theorem.
- Loogle: `"Grp", "extension"`: zero hits.
- Mathlib grep in AlgebraicGeometry:
  `MultiplicativeType|multiplicative.type|diagonalizable`: zero hits.
- LeanSearch: “A group scheme over a scheme is of multiplicative type of finite
  presentation if it is fppf locally isomorphic to the spectrum of the group algebra
  of a finitely generated abelian group”. Eight hits about ordinary type tags,
  group-algebra finite generation, affine schemes and finite presentation; no relative
  group-scheme definition.
- LeanFinder: “A group scheme is fppf locally diagonalizable by finitely generated
  character groups over affine covering schemes”. Eight scheme-diagonal results.
- Mathlib grep in AlgebraicGeometry:
  `MultiplicativeType|multiplicative.type|diagonali[sz]able`: zero hits.
- Original rg over WeilConjectures and Sheaf by the item id, multiplicative-type and
  diagonalizable terms found the ring-diagonalizable construction and the field-only
  `MultiplicativeType.IsMultiplicativeType`. The latter does not express arbitrary
  base schemes. Original DAG searches found the same field and ring notions;
  `blueprint_refs.py search 'multiplicative type'` returned zero blueprint matches.
- Repair search and direct reading now find the landed relative definition from
  Q140. The repaired delivery uses it directly. Its node source and full `lean`
  record and the server source were read. No new definition search or node is needed.

No STATEMENT-DISPUTED issue or statement correction is needed.

## Validation

The repaired module is compiled against the published relative multiplicative-type
module through scompile.py. The dry run and final delivery are repeated on the repaired
packet. Only the item node, its theorem module and this report belong to the delivery.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
