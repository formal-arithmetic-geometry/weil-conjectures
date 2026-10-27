## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.exists_fieldSquare_after_finite_extension`
in `Sheaf.AlgebraicGeometry.FieldSquareAfterFiniteExtension`. Its sole theorem proof is
`sorry`. The helper `squareDifferenceAfterBaseChange` is a full tensor/internal-Hom
construction, with no postponed data or proofs. No mathematical statement is corrected.
The source read was Guo, *Divisors on coherent schemes and homogeneous spaces*,
March 31, 2026 version, Section 5.1, Proposition 5.2(ii), Claim 5.2.1 and its proof,
printed pp. 11–13, at the node's URL
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf .
The source's square is descent of the four coordinate pullbacks, with signs
`+,+,-,-` at `00,11,01,10`, as in the node.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The three named structure morphisms are
  `X₁ X₂ X₃ : Over (Spec (CommRingCat.of k))`, with maps `Xᵢ.hom`.
- For each of the three morphisms, `[Smooth Xᵢ.hom]` states smoothness and
  `[IsSeparated Xᵢ.hom]` states the closed-immersion diagonal condition.
- Each finite-presentation assumption is `[LocallyOfFinitePresentation Xᵢ.hom]`
  plus `[QuasiCompact Xᵢ.hom]`. Quasi-separatedness is supplied by separatedness;
  no weaker mere local finite presentation is substituted for finite presentation.
- For each factor, `[GeometricallyIntegral Xᵢ.hom]` means integral after every
  field extension. It includes nonemptiness and is stronger than merely geometric
  irreducibility, exactly as the node explicitly requests.
- `C` is `((X₁ ⨯ X₂) ⨯ X₃).left` and `P` is `(squareParameter X₁ X₂).left`.
  These are products in the over category, hence fibre products over `Spec k`.
  `Over.prodLeftIsoPullback` identifies them with the recorded chosen pullbacks.
- `(A : ((X₁ ⨯ X₂) ⨯ X₃).left.Modules) [IsInvertible A]` is the arbitrary
  invertible module on `C`, using the dependency's locally rank-one class.
- The maps `r_ab` are the existing `squareCoordinate X₁ X₂ X₃ a b`, with
  `false = 0`, `true = 1`. Reading its body: the first product projection selects
  the doubled X₁/X₂ block; its first/second projections select that block; each
  Boolean then chooses `prod.fst`/`prod.snd`; the X₃ component is the identity.
  Thus all four maps have exactly the node's coordinate formula.
- The extension is `∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
  (_ : Module.Finite k K)`. This is finite vector-space degree, not a finite
  underlying field, and imposes no separability or characteristic condition.
- Its spectrum map is `Spec.map (CommRingCat.ofHom (algebraMap k K))`, say `g`.
  `P_K` is literally `Limits.pullback (squareParameter X₁ X₂).hom g`.
  The existential `N` is a module on this scheme; `IsInvertible N` is explicit.
- `A_K` is exactly `(tensorPullback (pullback.fst C.hom g)).obj A` in the theorem.
  The helper's input is this module on `C_K = Limits.pullback C.hom g`.
- The helper uses `(Over.pullback g).map (squareCoordinate ... a b)` for each
  base-changed map. Its four factors are tensor pullbacks of `A_K` at `00`, `11`,
  followed by `SheafOfModules.homObj ... (𝟙_ _)` of the `01` and `10` pullbacks.
  Internal Hom into the structure sheaf is precisely the dual; the helper does
  not replace a dual by an unspecified inverse or arbitrary invertible module.
- The helper lives on `Limits.pullback (squareParameter X₁ X₂ ⨯ X₃).hom g`.
  This is `(P ×_k X₃)_K`, canonically `P_K ×_K X₃,K` by pullback pasting.
- The right side is `(tensorPullback (((Over.pullback g).map
  (squareProjection X₁ X₂ X₃)).left)).obj N`, the actual base-changed projection
  `π_K`. `Nonempty (D(A_K) ≅ π_K^*N)` asserts existence of a module isomorphism,
  not numerical equivalence, equality of Picard classes, or pointwise triviality.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (`def-weil-field`, mathlib_match).
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `AlgebraicGeometry.GeometricallyIntegral`,
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`; the definition and its
  base-change meaning were read, rather than using only the similarly named
  irreducibility class.
- `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; the internal-Hom dual
  in `WeilConjectures.AlgebraicGeometry.Modules.Dual` was also read.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, retained upstream by the
  recorded `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; the
  tensor construction and the section-normalized adjunction's signature were read.
- The monoidal tensor from the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, retaining
  sheafification of the sectionwise tensor, and its sheaf monoidal structure.
- `Algebra`, `Mathlib.Algebra.Algebra.Defs`, and the finite-extension clause
  `Module.Finite k K` documented in `Sheaf.FieldTheory.FieldTower`; its recorded
  `FieldExtension.degree` definition was read. No duplicate field-extension
  notion is introduced.
- The already landed `squareParameter`, `squareCoordinate`, `squareDifference`,
  `squareProjection`, from `Sheaf.AlgebraicGeometry.NormalProductSquareDescent`.
  The new definition node `def-sfb-product-square-coordinates` records these
  four existing constructions and is added to stmt_deps. The theorem node
  `lem-sfb-normal-product-square-descent` is not a statement dependency. The
  helper is the base-change formula, expressed on the node's chosen `C_K` and
  `(P × X₃)_K`, using the existing maps without duplicating them.

Per the H9 return, the eight unused private proof-dependency imports and the
unused public FieldTower import are removed. The seven-step proof plan remains
in the docstring, naming the proof inputs without adding assumptions. In
particular, `lem-sfb-birigidified-affine-triviality-locus` and
`lem-sfb-normal-noetherian-generic-line-pullback` remain cited in that plan. There
is no missing statement dependency. The proof plan also notes that the current clopen
locus node permits a further finite extension: enlarge the extension, retain the
rational points, and use transitivity of finiteness. This does not change the
item's statement or its accepted seven-step route.

Edge cases checked before drafting: an empty factor is excluded by geometric
integrality itself, so no additional nonemptiness hypothesis is needed; taking a
factor to be `Spec k` is permitted. For the structure sheaf all four factors are
units and the assertion permits `K=k`, `N=O`. A module pulled back from the first
two factors also gives the expected square. Degree one is permitted; purely
inseparable finite extensions in positive characteristic are permitted; k need
not be perfect or algebraically closed. Nonproper affine factors are permitted.
`u` is explicit and arbitrary: any finite extension can be represented in `Type u`,
so its existential does not impose a mathematical size restriction. No test-field
universe quantifier has been made vacuous. There are no auto-bound variables,
local notations, private definitions, or statement `let` binders.

Searches actually run through msearch.py for this item:

- LeanFinder: `The square difference of a line bundle on three smooth geometrically
  integral schemes descends after a finite field extension` — eight results,
  all pullback-carrier/residue-tensor constructions such as
  `AlgebraicGeometry.Scheme.Pullback.Triplet.isPullback_SpecMap_tensor`; no theorem match.
- Loogle: `"IsInvertible", "pullback"` — two results, both analytic VectorField
  pullback lemmas; no algebraic-geometric theorem match.
- Mathlib grep, AlgebraicGeometry:
  `squareDifference|squareCoordinate|fieldProductSquare|finite.*extension.*square`
  — zero results.
- LeanSearch: `finite field extension square difference invertible sheaf on product
  of smooth schemes` — eight results about finite fields and algebraicity,
  beginning `FiniteField.instFieldExtension`; no line-bundle theorem match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `squareDifference|fieldSquare|square_after|squareAfter` found the existing
  `NormalProductSquareDescent` construction and the separate tensor-power theorem
  in `FieldProductSquarePower`, neither of which states this conclusion.
  `grep -rn` of the exact node id in `lean/WeilConjectures` found no occurrence.
  Name searches for both new declarations in these source roots and
  `dag/lean_names_upstream.json` found no collision.

Compilation: scompile.py, full delivered module, clean in both sandbox mode
(4.5 s) and library module mode (16.8 s), with no diagnostics. The first probe
exposed namespace resolution of bare `pullback` as the legacy module-pullback
functor; all scheme object occurrences are now explicitly `Limits.pullback`.
The theorem still uses only `tensorPullback` for module pullbacks.

No STATEMENT-DISPUTED flag, source correction, or dependency-node repair. The
item changes only in lean and stmt_deps; the latter adds the new definition
node described below. The new node records existing declarations and adds no
Lean module or duplicate definition.

## Second reading by Q14

I reread the completed module against the node and the source after compilation.
This is a second pass by the dispatcher worker; the brief prohibits starting
another agent, and the maintainer supplies the independent review.

The three groups of hypotheses each have smoothness, separatedness, local finite
presentation, quasi-compactness and geometric integrality. No properness or
rational-point assumption entered. The existential extension uses Module.Finite,
not Finite K. The source/target objects of every base-changed coordinate are
`(P × X₃)_K` and `C_K`, and the input really is the pullback of the original A.
The order of tensor factors is 00,11,01-dual,10-dual; the internal-Hom ring is
that of the source scheme. The projection is the image of the existing
squareProjection under the same Over.pullback functor. N lives on P_K and is
explicitly invertible. The conclusion is existence of an isomorphism.

This reading found no hypothesis or conclusion mismatch. I retained the explicit
base-changed-map helper instead of silently substituting the pullback of D(A),
which would require a tensor/dual comparison to identify it with the literal
D(A_K). The only elaboration repair was qualification of categorical pullbacks,
as reported above. The helper has actual data and the one theorem has sorry.


## Repair of returned delivery d626a2fa76aa

1. H2: replaced `lem-sfb-normal-product-square-descent` in the item's added
   statement dependencies with `def-sfb-product-square-coordinates`. The new
   definition node records `squareParameter`, `squareCoordinate`,
   `squareDifference`, and `squareProjection` with `existing: true` on
   `Sheaf.AlgebraicGeometry.NormalProductSquareDescent`. Its statement defines
   P, the four r_ab, π, and D(A), citing exactly the four requested definition
   dependencies. Its proof and proof_deps are empty. The existing module and
   its definitions are unchanged; the item does not choose any data from its
   normal-descent theorem. Current main was read again: the returned item
   differs there only in lean and stmt_deps, and still has no main-branch Lean
   record. The item copy was regenerated from that current node, keeping only
   its authorized repaired lean and stmt_deps delta. The wrapper rebases the
   repair on current main when assembling delivery.
2. H9: removed all eight private imports listed in the return:
   `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Finite`, `.FiniteType`,
   `.Immersion`, `Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct`,
   `Sheaf.TraceFormula.SmoothGeometricallyNormal`,
   `Sheaf.AlgebraicGeometry.FiniteClosedSetRationalLifts`, and
   `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`.
   Also removed `public import Sheaf.FieldTheory.FieldTower`. The three public
   statement imports remain. The module text from its module docstring onward
   is byte-identical to the returned sandbox: SHA256
   `8229a13d42dce7ff3f8e0618198775fa0540e589244328fbdf266d845ae5004a`.
   Thus both declarations, their types, bodies and docstrings are unchanged.

## New nodes

`def-sfb-product-square-coordinates` is the definition-node attachment requested
in H2, sourced to Guo §5.1, printed p.11, March 31, 2026 version. For arbitrary
S-schemes it defines P, Q, the four coordinate maps, π and D(A). It has an
`existing: true` record for all four exact definitions in
`Sheaf.AlgebraicGeometry.NormalProductSquareDescent` (source lines 51–87 read).
`lean.statement` is the verbatim squareDifference signature. No module is
written for it, and no data is defined again. Its new statement explicitly
specifies the left association already used in the existing Lean tensor
expression. Arbitrary bases, empty schemes and non-smooth factors are permitted
by these constructions; the specialization to invertible A uses the same full
definition that is available for all modules.

Fresh searches for this node, logged by msearch.py under this item:

- LeanSearch, `Coordinate projection maps and square difference of an invertible
  sheaf on a triple product of schemes`: eight hits, starting with
  `EuclideanSpace.projₗ`, plus scheme pullback-carrier projection facts;
  none defines this square difference.
- LeanFinder, `Four coordinate pullbacks defining the square difference of a
  line bundle on a product of three schemes`: eight hits, starting with
  `AlgebraicGeometry.Scheme.Pullback.t'` and `.t`, and residue-tensor pullback
  constructions; none defines this square difference.
- Mathlib grep in AlgebraicGeometry,
  `squareParameter|squareCoordinate|squareDifference|squareProjection`: zero hits.
- Project `rg` for that same regex on both `lean/WeilConjectures` and `lean/Sheaf`
  finds the four exact definitions only in NormalProductSquareDescent. The
  other name hit `ReducedCoproduct.squareProjection` is an unrelated
  algebraic-space abelian-family projection, not these product coordinates.
- DAG `rg -l` for these names and `product-square-coordinates` found no
  definition node owning them. The existing theorem node records them in its
  declarations but is not their definition node, precisely the H2 defect.
  `tools/blueprint_refs.py search 'square difference'` returned zero matches;
  `ancestor lem-sfb-field-square-after-finite-extension` returned None. The
  new node preserves this null ancestor, adds the item in front of its via
  chain, and cites the exact Guo source place. The item's reach from the
  current target/former-target roots was checked directly by reading the DAG;
  it is reached, so the new node has `import_flags: []`.

The three new mathlib_searches records store the actual msearch log records,
including their timestamp, hit count, returned names and digest. No existing
DAG node or Mathlib definition is duplicated.

Repair second pass: read the new node next to all four source declarations.
P is exactly `(X₁ ⨯ X₁) ⨯ (X₂ ⨯ X₂)` in Over S; the Boolean branches select
first for 0 and second for 1; the third factor is the identity. π is prod.fst.
D(A) uses tensorPullback, signs +,+,-,- at 00,11,01,10, and homObj into the
structure sheaf for the last two duals. The new definition imposes no extra
geometry. The repaired item retains all hypotheses and the same literal
D(A_K) and base-changed π_K as the version accepted mathematically by the
independent review. Both returned points are addressed; none is deferred.

Repair compilation: the reduced-import module passes scompile.py cleanly in
sandbox mode (3.2 s) and library mode (2.1 s), with no diagnostics. The delivery
wrapper also checks the existing declaration attachment for the new definition
node with its own module-mode probe.
