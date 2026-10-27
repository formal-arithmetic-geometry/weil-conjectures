## Worker report

This delivery states `AlgebraicGeometry.exists_smooth_integral_finite_etale_chart` in
`Sheaf.AlgebraicGeometry.SmoothIntegralFiniteEtaleChart`. Its sole proof is `sorry`,
with all nine accepted DAG proof steps in its docstring. It adds no definitions,
new nodes, dependency modules, or statement correction. The accepted stage-1 split,
including the reviewer's scheme-fibre clarifications, is preserved verbatim.

The inherited BLOCKED message concerned stage-1 re-splitting. This assignment is
stage 2: the live node is split and reviewed PASS, its queue entry is stage 2,
and it has no Lean record. The handoff in brief-stage2 section 0 explicitly permits
this statement delivery. There is no repair note for this node.

### Hypotheses and clauses

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  No separate algebraic extension is requested: the statement only uses the
  algebraically closed part of def-weil-algebraic-closure.
- The k-scheme is `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`.
  Smoothness is `[Smooth f]`; integrality is `[IsIntegral X]`, which includes
  nonemptiness. Finite type is exactly `[LocallyOfFiniteType f] [QuasiCompact f]`,
  as specified by the dependency record. Separatedness is the stated
  `[IsClosedImmersion (pullback.diagonal f)]`.
- The nonnegative dimension and positive degree are existential `(d n : ℕ)`
  and `1 ≤ n`; in particular no positive-dimension restriction is imposed.
- Affine space is literally `Spec (.of (MvPolynomial (Fin d) k))`, with its
  canonical structure map `Spec.map (CommRingCat.ofHom (algebraMap k ...))`.
  Its affine open is `V : (...).Opens`, `IsAffineOpen V`, `Nonempty V`.
- The open subscheme of X is `W : X.Opens`; `W.ι` is its canonical open immersion
  (Mathlib's instance `IsOpenImmersion W.ι`). It is affine and nonempty by
  `IsAffineOpen W`, `Nonempty W`, and dense by `Dense (W : Set X)`.
- The map is `q : W.toScheme ⟶ V.toScheme` with `IsFinite q ∧ Etale q ∧ Surjective q`.
  Its k-linearity is the displayed equality
  `q ≫ V.ι ≫ Spec.map (...) = W.ι ≫ f`.
- Finite local freeness of constant degree n is exactly the recorded upstream
  `q.IsFiniteLocallyFreeOfDegree n`. This class extends finite local freeness
  and requires `q.fiberDegree s = n` at every point s of V, not merely rational s.
- Both W and V are smooth integral finite-type k-schemes: the conclusion explicitly
  lists `Smooth`, `IsIntegral`, `LocallyOfFiniteType`, and `QuasiCompact` for each
  of their induced structure morphisms.
- A point of V(k) is `v : Spec (.of k) ⟶ V.toScheme` satisfying
  `v ≫ V.ι ≫ Spec.map (...) = 𝟙 (Spec (.of k))`. Quantification is over all such
  morphisms, with this equality as the antecedent, rather than arbitrary absolute
  morphisms of schemes. The fibre is the actual rational-point pullback `pullback q v`.
- Its disjoint-union description uses the project convention of a colimiting cofan:
  `a : Fin n → (Spec (.of k) ⟶ pullback q v)` and
  `Nonempty (IsColimit (Cofan.mk (pullback q v) a))`. This is precisely an
  isomorphism from a coproduct of n copies of Spec k to the fibre, by the coproduct
  universal property. The equation `a i ≫ pullback.snd q v = 𝟙 (Spec (.of k))`
  makes that coproduct isomorphism an isomorphism over k, rather than just over
  the category of absolute schemes.
- The n distinct rational points of W are the maps `a i ≫ pullback.fst q v`.
  The conclusion asserts that their values at `IsLocalRing.closedPoint k` are
  injective in i and have range exactly `{x | q x = v (IsLocalRing.closedPoint k)}`.
  The maps are over k: combine the cofan's projection equation, the pullback
  square, q's k-linearity, and the antecedent for v. This also explains why the
  point enumeration is equivalent to the stated rational-fibre assertion.

### Dependencies used

The statement dependencies were read with their complete records and signatures.
They supply the following original notions; no copied predicate is introduced:

- `Mathlib.Algebra.Field.Defs`: `Field` (via the public field imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed
  notion explained in def-weil-algebraic-closure's Mathlib match).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.OpenImmersion` and `...Restrict`:
  `AlgebraicGeometry.IsOpenImmersion`, `Scheme.Opens.toScheme`, `Scheme.Opens.ι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` (actual source lines
  899 and 907; the record's old line 778 is stale, but its module and interface work).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, with the scheme
  pullback instances from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` and its canonical k-algebra.

These dependencies are public imports or are publicly exposed by the public
FiberDegree import. Proof dependencies are plain imports, including the recorded
EtaleLocalNormalForm, GenericFiniteOpenNeighborhood, UnramifiedQuasiFinite,
QuasiFiniteMorphism, ProperQuasiFinite, FiniteLocallyFreeDegreeLocallyConstant,
EtaleFibreDiscreteSeparablePoints, and upstream smooth-affine-space modules.
Mathlib proof inputs for Noetherianity, the étale open image, function fields of
domains and finite/radicial base change are also imported. The remaining elementary
spectrum, affine morphism, restriction, and finite-type composition inputs are in
those same import closures. No available proof-dependency import was omitted to
break an import cycle.

### Sources and edge cases

Read Stacks `groupoids.tex`, lemma-algebraic-quasi-projective (0BF7), the diagram
G <- U -> affine space, W -> V and its rational-fibre paragraph; also
`morphisms.tex` lemmas smooth-etale-over-affine-space (054L), generically-finite
(02NW), finite-locally-free (04MH), and etale-over-field (02GL). The statement is
exactly the existing DAG statement; no correction or dispute is needed.

- d = 0 is allowed. For X = Spec k the identity chart has V = W = Spec k, n = 1.
- n = 0 is excluded by the node's positive-degree clause, consistent with
  nonempty V and surjective q; no additional exclusion of a genuine case occurs.
- Empty X is excluded by integrality itself. Empty W and V are explicitly excluded.
- No characteristic restriction is imposed; purely inseparable smooth-coordinate
  obstructions are avoided by the smoothness hypothesis, not by an extra assumption.
- No rational point v is assumed to have been chosen, and the splitting assertion
  quantifies over every rational point. Pulling back at v rather than silently at
  a residue-field map preserves the reviewer clarification in proof step 8.
- Universe u is explicit and arbitrary. The finite coordinate and splitting index
  `Fin d`/`Fin n` impose no size restriction on k or the schemes. No automatic
  implicit binder, local notation, private definition, or chosen structure is used.
- Separatedness is retained verbatim even though the finite-chart argument itself
  does not need it.

### Searches

All searches used the prescribed msearch wrapper under Q16 and this item:

1. LeanFinder: "A smooth integral variety over an algebraically closed field has
   a dense affine open finite etale surjective of positive constant degree over
   an affine open of affine space with split rational fibers". Eight hits,
   including `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
   and smooth local charts; none contains this full statement.
2. Loogle: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree,
   AlgebraicGeometry.IsIntegral`. Zero hits; the upstream degree declaration is
   unknown to Loogle. Its actual upstream source was therefore read directly.
3. Mathlib grep: `finite.*[Ee]tale.*[Aa]ffine|IsFiniteLocallyFreeOfDegree` in
   AlgebraicGeometry: zero hits.
4. LeanSearch: "smooth integral scheme finite etale chart affine space constant
   degree split rational fibres". Eight hits on smoothness and étaleness, none
   stating the complete chart theorem.
5. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for finite-etale chart
   terminology, the proposed declaration, and the item id. No existing declaration
   states this result. The item id occurs only in its consumer's proof docstring.
   Read `WeilConjectures.DeligneLaumon.Reduction.FiniteEtaleChart` in full at the
   existing theorem signature: `AlgebraicGeometry.exists_isFinite_etale_to_affineSpace`
   only gives an arbitrary open target, nonempty open source and a finite étale
   surjection for a nonempty reduced scheme over a perfect field. It does not give
   affine opens, density, integral smooth finite-type source and target, a positive
   constant degree, or split rational fibres. It cannot be an existing:true exact
   attachment for the present statement.

### Validation

The prescribed server scompile.py wrapper compiled the initial formulation in
both sandbox and library module mode cleanly. The fibre conclusion was then
rewritten as a colimiting cofan to follow the project's explicit coproduct-cover
convention; that final module also compiled cleanly in sandbox and library module modes
(44.7 s and 8.5 s reported by the wrapper, including its queue/build handling). Only the named
main theorem is postponed. No proof is supplied, as required for stage 2.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
