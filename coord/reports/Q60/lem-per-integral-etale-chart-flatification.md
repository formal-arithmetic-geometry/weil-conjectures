## Worker report

The module states `AlgebraicGeometry.exists_integral_etale_chart_flatification` with
`sorry` as its whole proof. Five real auxiliary definitions specialize the existing
scheme-theoretic image to the generic fibre; they introduce no independent notion.
There are no new nodes, dependency repairs or statement corrections. All original
node fields are preserved; only `lean` is added.

The source was read in ILO, Expose II, the platification paragraph in the general
proof of 3.2.1 (printed p. 29) and the initial platification sentence of 3.2.3
(printed p. 30). The detailed argument follows the node's fourteen proof steps;
all fourteen, with their named dependencies, are included in the theorem docstring.
Stacks `flat.tex`, Tags 081R and 0B48, were also read. In particular 081R requires
finite type, quasi-separatedness and a flat finitely presented restriction, whereas
0B48 supplies finiteness from properness and flatness over a dense finite locus.

Hypothesis correspondence:

- An integral Noetherian scheme: `(X : Scheme.{u}) [IsIntegral X]
  [IsNoetherian X]`. Mathlib's Noetherian condition is equivalent to a finite
  affine cover by Noetherian rings, by
  `isNoetherian_iff_of_finite_iSup_eq_top`, read in `Noetherian.lean`.
- All affine coordinate rings quasi-excellent: `hX : ∀ U : X.affineOpens,
  IsQuasiExcellent Γ(X, U)`. This uses the dependency's precise quasi-excellent
  predicate, including Noetherianness, G-ring and J-2.
- A finite family, including the empty family: `(I : Type v) [Finite I]`.
  Independent `v` is allowed here because this is a finite family, not a limit.
- Sources and maps: `E F : I → Scheme.{u}`, `e : ∀ i, E i ⟶ X` and
  `f : ∀ i, F i ⟶ E i`.
- Nonempty integral etale-chart sources: `[∀ i, IsIntegral (E i)]`;
  nonemptiness is included in `IsIntegral`.
- Separated, etale and finite type: `[∀ i, IsSeparated (e i)]`,
  `[∀ i, Etale (e i)]`, and the pair `[∀ i, LocallyOfFiniteType (e i)]`,
  `[∀ i, QuasiCompact (e i)]`. There is no covering or surjectivity assumption
  on the family `e`.
- Integral proper dominant sources: `[∀ i, IsIntegral (F i)]`,
  `[∀ i, IsProper (f i)]`, `[∀ i, IsDominant (f i)]`.
  Mathlib's dominance is dense range of the actual underlying map.
- Finite function-field extension of positive degree: `hfinite` is
  `RingHom.Finite` for the actual stalk map at `genericPoint (F i)`;
  `hdegree` gives its `Module.finrank = n i`, and `hn` gives `0 < n i`.
  The module structure is explicitly `Algebra.toModule` for that ring map's
  `toAlgebra`, so there is no arbitrary field action or hidden statement let.
  Dominance identifies `f i (genericPoint (F i))` with the generic point of
  `E i`; thus the stalk in the degree formula is exactly its function field.
  The codomain is definitionally `(F i).functionField`.

Conclusion correspondence:

- `∃ (X' : Scheme.{u}) (_ : IsIntegral X') (p : X' ⟶ X)` selects the modified
  integral base, and `IsNormalScheme X' ∧ IsNoetherian X' ∧ IsProper p`
  states all its required properties. `IsNormalScheme` is the existing predicate:
  integral and every stalk an integrally closed domain.
- An isomorphism over a dense open is `∃ U : X.Opens, Dense (U : Set X) ∧
  IsIso (p ∣_ U)`; no density assumption is put into the input.
- `LocallyOfFiniteType p ∧ QuasiCompact p` states that the modified base is
  finite type over the original base.
- `E_i'` is exactly `pullback (e i) p`. The existential `IsIntegral` witness,
  `IsNormalScheme`, and `IsNoetherian` give its integral, normal and Noetherian
  properties. The composite `pullback.snd (e i) p ≫ p` is explicitly finite type.
- The first projection sends the generic point to `genericPoint (E i)` and its
  actual stalk map there is `Function.Bijective`. This is the induced function-field
  isomorphism, rather than an unrelated abstract field isomorphism.
- `F_i'` is explicitly `Scheme.Hom.chartGenericClosure (e i) (f i) p`.
  Its existential `IsIntegral` witness and `IsNoetherian` supply the source
  properties. Specifying this canonical representative implements "may be chosen"
  without adding any extra hypothesis.
- `chartGenericClosureMap` is `a_i`, and
  `IsFiniteLocallyFreeOfDegree (n i)` uses exactly the recorded dependency's
  finite, flat, locally finitely presented morphism with fibre-degree `n i`.
  `Surjective` is stated separately as required by the node.
- The composites of `a_i` with the second projection and `p` are explicitly
  locally finite type and quasi-compact, giving finite type of `F_i'` over `X`.
- `chartGenericClosureToSource` is the requested map to `F_i`. It is an `E_i`-map
  by construction: its composite with `f_i` equals the composite of `a_i` with
  the first projection by the pullback relation. No arbitrary comparison map is
  quantified. Its generic-point equality and bijective stalk map explicitly say
  that this particular comparison induces a function-field isomorphism.
- For the final closure clause, `chartGenericFibreι` is the first projection from
  the pullback along `E_i'.fromSpecStalk (genericPoint E_i')`.
  `chartGenericClosure` is this morphism's existing `Hom.image`, and
  `chartGenericClosureι` its existing `Hom.imageι` closed embedding.
  The ambient `F_i ×[E_i] E_i'` is canonically `F_i ×[X] X'`.
  Because the first projection identifies the function fields, this generic fibre
  is the original generic fibre transported to the modified chart, exactly as
  in the node. `Hom.image` is defined as `f.ker.subscheme`, giving the stated
  affine kernel of restriction; no reduced topological closure is substituted.

Dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, including its nonempty and component-domain fields.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; scheme form from `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsQuasiExcellent`
  (the recorded node also lists this declaration alongside `IsExcellent`).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `IsProper`, `IsSeparated` and `UniversallyClosed` (the last is implicit in properness).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd` and the universal pullback relation.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`; its full definition and parent
  `IsFiniteLocallyFree` were read.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `Surjective`; supplied by the public morphism imports.
- `def-nagata-scheme-theoretic-closure`:
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, `Scheme.Hom.image` and `imageι`.
- Existing normality: `Sheaf.AlgebraicGeometry.NormalScheme`, `IsNormalScheme`.
  Existing function field: `Mathlib.AlgebraicGeometry.FunctionField`,
  `Scheme.functionField`, the generic stalk. The current
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback` was additionally read
  using `scompile.py --source`; its `functionFieldMap` is precisely the stalk
  map with a generic-point equality inserted. We use that same actual stalk
  directly, avoiding an extra heavy import and arbitrary algebra structures.

Every recorded proof dependency with an available module is imported; Mathlib
matches without `lean` records are imported through their recorded source files.
Statement dependencies are public imports and the remaining proof imports are ordinary.

Edge cases checked before writing: the empty family is permitted, with no
nonemptiness assumption on `I`; normalization still produces the required modified
base. Empty `X`, `E_i` or `F_i` are excluded exactly by the given integrality,
not by an added condition. The degree-zero case is excluded exactly by the node's
`n_i > 0`. Degree one, purely inseparable finite extensions and arbitrary
characteristic are allowed; no separability hypothesis was added. The family can
consist of a single non-surjective etale chart. Dense opens can be the whole base.
The generic closure uses the scheme-theoretic kernel, retaining the intended scheme
structure. All variables and both universes are explicitly bound.

Searches for an existing statement (2026-10-18 UTC):

- `msearch.py leanfinder`, query "simultaneous flatification proper generically finite
  morphisms over integral etale charts finite locally free": eight results concerning
  flatness, etaleness and finite presentation; no simultaneous theorem.
- `msearch.py leansearch`, query "proper generically finite morphism flatification
  blowup finite locally free": eight results about finite/proper morphisms; no match.
- `msearch.py loogle`, query "AlgebraicGeometry.IsIntegral,
  AlgebraicGeometry.Scheme.functionField": twelve results about the existing
  generic stalk and rational maps; no simultaneous flatification theorem.
- `msearch.py grep`, query `flatification|flat.*blow|blow.*flat` in
  `Mathlib/AlgebraicGeometry`: zero results.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `flatification|etale_chart|etaleChart|lem-per-integral-etale-chart-flatification|
  functionFieldMap|functionField.*[mM]ap|IsBirational`: related curve and flattening
  statements only, notably `FlatteningByAdmissibleBlowup` and
  `ProperBirationalCurveFinite`; neither states this node.
- `rg` for the exact node id in upstream source and for the chosen theorem name in
  `dag/lean_names_upstream.json`: no matches. Searches for generic closures found
  related component-spreading statements, but no construction specialized to this
  base-changed source. The underlying image notion already exists and is reused.

Validation: `scompile.py Q60 lem-per-integral-etale-chart-flatification` compiled
both the sandbox and actual library-module forms cleanly (about 2.5 seconds each).
The first elaboration exposed ambiguous scheme-to-type coercions in generic-point
arguments; these were repaired by explicit `Scheme.{u}` annotations, without a
statement change. No errors or warnings remain. The only postponed theorem is
`AlgebraicGeometry.exists_integral_etale_chart_flatification`.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
