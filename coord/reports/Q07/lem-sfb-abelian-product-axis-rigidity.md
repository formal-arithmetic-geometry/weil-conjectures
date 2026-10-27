## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.ProductAxisRigidity` states
`AlgebraicGeometry.IsAbelianVariety.eq_identity_of_product_axes`, with the whole
proof `sorry`. There are no new definitions, nodes, dependency repairs or statement
corrections. The module docstring and declaration docstring identify Milne, Abelian
Varieties, Chapter I, Theorem 3.4, printed pp. 18–19. The declaration docstring carries
all six steps of the node's proof, including the curve completion, Weil extension,
proper rigidity, dense pointed curves, and dense rational-point evaluation.

Clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The two k-schemes are `(V W : Scheme.{u})`, with their explicitly specified
  structure maps `fV : V ⟶ Spec (.of k)` and `fW : W ⟶ Spec (.of k)`.
- Smoothness is `[Smooth fV] [Smooth fW]`.
- Separatedness is `[IsSeparated fV] [IsSeparated fW]`. Mathlib defines these
  classes by closed immersions of the diagonals, exactly as the node specifies.
- Geometric integrality is `[GeometricallyIntegral fV] [GeometricallyIntegral fW]`.
  These are the recorded Mathlib classes, not geometric connectedness alone.
- Finite type is the two pairs `[LocallyOfFiniteType fV] [QuasiCompact fV]` and
  `[LocallyOfFiniteType fW] [QuasiCompact fW]`, as the dependency record prescribes.
- The rational points are `v₀ : Spec (.of k) ⟶ V` and `w₀ : Spec (.of k) ⟶ W`
  with `hv₀ : v₀ ≫ fV = 𝟙 _` and `hw₀ : w₀ ≫ fW = 𝟙 _`. This is the section
  definition of rational points in def-pc-rational-point and in the docstring of
  `Scheme.Hom.baseChangeFieldPoint`; no replacement notion is introduced.
- The abelian variety is `(A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]`.
  The recorded upstream predicate supplies properness, smoothness and connectedness;
  the separate group-object instance supplies the group scheme, as its docstring
  requires. The canonical identity section is `η[A].left`.
- The product is the recorded `pullback fV fW`. Its structural map is
  `pullback.fst fV fW ≫ fV`.
- The k-morphism is `h : pullback fV fW ⟶ A.left`, together with
  `hh : h ≫ A.hom = pullback.fst fV fW ≫ fV`.
- The first axis is `pullback.lift (𝟙 V) (fV ≫ w₀) ...` and its restriction is
  required by `hV` to equal `fV ≫ η[A].left`.
- The second axis is `pullback.lift (fW ≫ v₀) (𝟙 W) ...` and its restriction is
  required by `hW` to equal `fW ≫ η[A].left`. The compatibility proofs for these
  lifts merely use the section equations; no extra commutativity assumption is added.
- The conclusion is `h = pullback.fst fV fW ≫ fV ≫ η[A].left`. This is equality
  of scheme morphisms, including their structure-sheaf maps, not just point maps.
- There is no properness hypothesis on V or W.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (the algebraically closed
  clause of def-weil-algebraic-closure; no chosen closure is needed).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral:
  `AlgebraicGeometry.GeometricallyIntegral`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- WeilConjectures.AlgebraicGeometry.DensePoints:
  `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`; its docstring identifies
  rational points with sections. Its base-change construction is not needed here.
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs:
  `AlgebraicGeometry.IsAbelianVariety`, read with its explicit instruction to use
  `[GrpObj A]` beside `[IsAbelianVariety A]`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.
- Mathlib.AlgebraicGeometry.Morphisms.Separated:
  `AlgebraicGeometry.IsSeparated` (its diagonal formulation).

Statement dependencies are public imports, or provided by their public imported
modules. All recorded proof-dependency modules are imported, including the Mathlib
modules for the Mathlib leaves. Already public imports also supply proof dependencies
(smoothness, finite type and rational-point density). The proof dependencies
lem-sfb-weil-extension-to-abelian-variety and lem-sfb-smooth-pointed-curves-dense
currently have neither a recorded declaration nor a Mathlib match, so there is no
module to import for them. They are proof prerequisites, not missing notions in this
statement. No other module is restated.

Edge cases checked: the rational sections make each factor nonempty; no additional
nonemptiness assumption is imposed. Zero-dimensional factors, the trivial abelian
variety, and positive characteristic are all included. There is no dimension or
characteristic binder restricting them. The identity map in either section equation
has source Spec k, not the identity map of the factor. Choosing the first projection
for the product structure map agrees with the second by pullback.condition. The
single universe u is the ordinary Scheme/field universe convention and is arbitrary;
there is no independent smaller universe of test objects. Nonproper factors are
allowed, precisely the case for which Milne 3.4 uses Lemmas 3.5 and 3.6.

Searches performed:

- msearch.py leanfinder: "A morphism from a product of smooth varieties to an
  abelian variety that is zero on both coordinate axes is zero". Eight hits, all
  affine-map, elliptic-point or zero-morphism statements; none is this theorem.
- msearch.py loogle: "AlgebraicGeometry.IsAbelianVariety". The search service does
  not know this project-specific identifier; recorded as unavailable for that name.
- msearch.py loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsProper".
  Valid Mathlib identifiers, zero hits.
- msearch.py grep: "abelian.variety|rigidity|Rigid", subdirectory AlgebraicGeometry:
  zero Mathlib hits.
- rg of lean/WeilConjectures and lean/Sheaf for axes/axis and rigidity variants,
  with targeted reading of AbelianVariety/Defs.lean, Basic.lean and Rigidity.lean:
  no exact theorem. `exists_eq_snd_comp` requires a proper first factor, so it is
  a proof dependency, not a match for the present statement.
- rg for the node id in lean/WeilConjectures and dag/lean_names_upstream.json:
  no match. rg for `eq_identity_of_product_axes` in Mathlib, WeilConjectures and
  Sheaf: no existing declaration of this name.
- Read the current node, every statement dependency's statement and record, and
  the full signatures/docstrings of the relevant recorded declarations. The example
  Sheaf/CategoryTheory/CompactObject.lean is now withdrawn; its node points to
  WeilConjectures/CategoryTheory/CompactObject.lean, which was read instead.

Source checked locally with pdftotext: Milne's printed pp. 18–19 explicitly state
Theorem 3.4 for nonsingular factors without completeness and explain the curve
compactification and density argument. No STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the module separately as sandbox and library module,
with no errors or unexpected warnings (2.3 s and 2.9 s respectively).

## Second reading by Q07

Independent clause-by-clause reading of `AlgebraicGeometry.IsAbelianVariety.eq_identity_of_product_axes`
against the node (Milne, Abelian Varieties, Ch. I Thm 3.4, printed pp. 18–19, specialised to
k = k̄ and the identity value). This replaces the worker's self-check.

| Node clause | Lean | Verdict |
|---|---|---|
| k algebraically closed field | `(k : Type u) [Field k] [IsAlgClosed k]` | exact (def-weil-field `Field`; def-weil-algebraic-closure `IsAlgClosed`) |
| V, W schemes over k | `(V W : Scheme.{u}) (fV : V ⟶ Spec (.of k)) (fW : W ⟶ Spec (.of k))` | exact (def-pc-scheme) |
| smooth | `[Smooth fV] [Smooth fW]` | exact (def-sbc-smooth-morphisms) |
| separated (diagonal closed immersion) | `[IsSeparated fV] [IsSeparated fW]` | exact (Mathlib: `IsClosedImmersion` of the diagonal) |
| geometrically integral | `[GeometricallyIntegral fV] [GeometricallyIntegral fW]` | exact (def-pc-geometrically-irreducible record) |
| finite type | `[LocallyOfFiniteType f] [QuasiCompact f]` for both | exact (def-weil-finite-type-morphism record: conjunction); LFT is implied by Smooth, so not stronger |
| v₀ ∈ V(k), w₀ ∈ W(k) | `v₀, w₀ : Spec (.of k) ⟶ _` with `v₀ ≫ fV = 𝟙 _`, `w₀ ≫ fW = 𝟙 _` | exact: sections of the structure map (def-pc-rational-point) |
| A abelian variety with 0 | `(A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]`, `η[A].left` | exact: `IsAbelianVariety` extends `IsProper A.hom, Smooth A.hom, ConnectedSpace A.left`, group structure by `GrpObj` as its docstring prescribes; `η[A].left : Spec k ⟶ A.left` is the identity section |
| V ×_k W | `pullback fV fW` | exact (def-pc-fibre-product) |
| h a k-morphism | `h : pullback fV fW ⟶ A.left`, `hh : h ≫ A.hom = pullback.fst fV fW ≫ fV` | exact (structure map of the product via fst; equal to snd ≫ fW by `pullback.condition`) |
| V × {w₀} ↪ V ×_k W | `pullback.lift (𝟙 V) (fV ≫ w₀) _` | correct: v ↦ (v, w₀); compatibility from `hw₀` only |
| {v₀} × W ↪ V ×_k W | `pullback.lift (fW ≫ v₀) (𝟙 W) _` | correct: w ↦ (v₀, w); compatibility from `hv₀` only |
| both composites constant identity | `hV : … ≫ h = fV ≫ η[A].left`, `hW : … ≫ h = fW ≫ η[A].left` | exact |
| conclusion: h constant identity | `h = pullback.fst fV fW ≫ fV ≫ η[A].left` | exact: equality of scheme morphisms |
| V, W not required proper | no properness binder | exact |

Edge cases: a factor equal to Spec k (dimension 0) is allowed; the empty factor is excluded
by the rational point, as in the node; the trivial abelian variety A = Spec k is allowed;
there is no characteristic restriction. Universe: one universe `u` for k and the schemes,
which `Spec (.of k)` requires. There is no smaller test universe and no extra universe restriction.

Records: `lean.statement` is verbatim the signature in the file (script check). The node differs
from side-live only in `lean`. There are no new definitions and no dependency modules. The proof is only `sorry`.
The module and declaration docstrings give the source place and `(blueprint: lem-sfb-abelian-product-axis-rigidity)`,
and the declaration docstring gives the six proof steps. There is no pro-étale content.

Searches: no existing declaration. `AbelianVariety/Rigidity.lean`'s `exists_eq_snd_comp` needs a
proper first factor, so it is the proof dependency lem-sc-rigidity and does not match the statement.

Parallel delivery: Q62 ae891c27 delivered the same item to the same file path with declaration
`eq_const_of_product_axes` (an equivalent `Over`/monoidal formulation). It has a PASS review but
is not landed. Only one of the two may land, and the later one must not rebind.
