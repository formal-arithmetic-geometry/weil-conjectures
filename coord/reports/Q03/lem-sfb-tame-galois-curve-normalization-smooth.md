## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.TameGaloisNormalizationSmooth` states
`AlgebraicGeometry.tame_galois_curve_normalization_smooth`, with its sole proof `by sorry`.
It introduces no definitions and changes only the item's `lean` field. The source statement,
statement dependencies, proof plan, and proof dependencies are unchanged.

The node and its source were read: Stacks Project `more-algebra.tex`, Tag 09EB,
`lemma-galois-conclusion` (the formula `[L:F] = n e f`), Tag 09ED,
`lemma-galois-galois` (normality of the residue extension), and `varieties.tex`, Tag 0B8Y,
`lemma-regular-point-on-curve` (normality and smoothness at separable closed points).
The theorem docstring carries all seven original proof steps, with their dependency names.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| K is an arbitrary field | `(K : Type u) [Field K]`; no perfectness assumption. |
| C is an integral K-curve | `(C : Scheme.{u}) (q : C ⟶ Spec (.of K)) [IsIntegralCurve q]`. This is the recorded variety convention, including integrality, separatedness, finite type and dimension exactly one. |
| C is smooth over K | `[Smooth q]`. |
| F = K(C) | `C.functionField`, the existing generic stalk, not a new independent field. |
| L/F is a field extension | `(L : Type u) [Field L] [Algebra C.functionField L]`. |
| The extension is finite-dimensional, normal and separable | `[FiniteDimensional C.functionField L] [IsGalois C.functionField L]`; Mathlib's IsGalois consists exactly of Normal and Algebra.IsSeparable. |
| Its degree is d >= 1 | `(d : ℕ) (hd : 1 ≤ d) (hdegree : Module.finrank C.functionField L = d)`. |
| The image of d is invertible in K | `(hunit : IsUnit (d : K))`. |
| Y and nu are the normalization in L and its canonical map | `C.normalizationIn L` and `C.fromNormalizationIn L` throughout. Fixing these canonical representatives imposes no condition on the mathematical normalization, which is unique over C. |
| Y is an integral K-curve with the induced structure morphism | `[IsIntegralCurve (C.fromNormalizationIn L ≫ q)]`. |
| Y is normal, meaning integrally closed domain stalks | `hnormal : ∀ y, IsIntegrallyClosed ((C.normalizationIn L).presheaf.stalk y)`; stalks are already domains by the preceding integral-curve hypothesis. |
| nu is finite | `[IsFinite (C.fromNormalizationIn L)]`. |
| D is a reduced closed subscheme of C | `(D : Scheme.{u}) (i : D ⟶ C) [IsClosedImmersion i] [IsReduced D]`. |
| D is finite etale over K | `[IsFinite (i ≫ q)] [Etale (i ≫ q)]`. |
| nu is etale above C minus D | `U : C.Opens`, `hU : (U : Set C) = (Set.range i)ᶜ`, and `hetale : Etale (C.fromNormalizationIn L ∣_ U)`. The open U is uniquely specified by its underlying set; this names the complement rather than assuming an extra open. |
| Every y above some x in D | `∀ y : C.normalizationIn L, C.fromNormalizationIn L y ∈ Set.range i → ...`; x is exactly the image of y, so quantifying a separate x with an equality is unnecessary. |
| y is closed in Y | `IsClosed ({y} : Set (C.normalizationIn L))`. |
| [kappa(y):kappa(x)] divides d | `@Module.finrank (C.residueField (C.fromNormalizationIn L y)) ((C.normalizationIn L).residueField y) _ _ ((C.fromNormalizationIn L).residueFieldMap y).hom.toAlgebra.toModule ∣ d`. The displayed module is induced by the actual residue field map of nu. |
| kappa(y)/K is finite | `((C.fromNormalizationIn L ≫ q).residueFieldAlgebraMap y).Finite`, meaning finite as a module via the canonical base-field embedding. |
| kappa(y)/K is separable | `@Algebra.IsSeparable K ((C.normalizationIn L).residueField y) _ _ ((C.fromNormalizationIn L ≫ q).residueFieldAlgebraMap y).toAlgebra`. This is minimal-polynomial separability, not a perfect-field condition. |
| Y -> Spec K is smooth | Final conjunct `Smooth (C.fromNormalizationIn L ≫ q)`. |
| No projectivity hypothesis | Neither q nor the normalization map is assumed projective. |

The finiteness conclusion over K also ensures that the displayed residue finrank is the
finite extension degree, not its infinite-dimensional junk value. All scalar structures
in the residue statements are explicit; there is no arbitrary algebra structure. The
normalization's K-structure is always the composite through C, so no independent action or
compatibility hypothesis is needed. The use of one explicitly bound universe follows the
recorded scheme/normalization API: taking a larger universe accommodates any given finite
extension and any of the schemes in the node.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-curve`: `AlgebraicGeometry.IsIntegralCurve` and `IsVariety`,
  WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective. The class's `isIntegral` field
  is an instance, so its function field and domain stalks require no added hypotheses.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties, through the curve instance.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-sc-function-field`: the integral-scheme clause uses `Scheme.functionField`,
  Mathlib.AlgebraicGeometry.FunctionField; import its recorded
  WeilConjectures.AlgebraicGeometry.FunctionField module, whose docstring explicitly
  delegates the integral case to that Mathlib construction.
- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs.
- `def-fin-normalization-extension`: `Scheme.normalizationIn` and
  `Scheme.fromNormalizationIn`, WeilConjectures.Mathlib.AlgebraicGeometry.Normalization.
  Their full section assumptions are `[IsIntegral C]`, `[Field L]`, and
  `[Algebra C.functionField L]`; all are supplied by the theorem's actual data.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  Mathlib.AlgebraicGeometry.ResidueField; the base-field specialization is the existing
  `Scheme.Hom.residueFieldAlgebraMap`, WeilConjectures.ZetaSeries, read in full.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  Mathlib.LinearAlgebra.Dimension.Finrank.

All recorded proof dependencies with modules are imported without `public`, except for
notions also needed publicly by the statement. Mathlib proof dependencies use their
recorded source modules. `lem-sfb-curve-closed-point-affine-local-model` has neither a Lean
record nor a Mathlib match at this reading, so it has no module to import; it is a proof
prerequisite, not a missing notion needed to state this theorem. Its use remains in the
unchanged node proof and in the theorem's docstring.

Edge cases checked before writing:

- D empty: there is no point y satisfying the image-membership antecedent. U is all C,
  and the etale hypothesis supplies the everywhere etale case. No Nonempty D is imposed.
- d = 1, including L = F: the degree/invertibility hypotheses are meaningful and the
  divisibility conclusion forces every relative residue degree to be one.
- Imperfect fields of positive characteristic are allowed. Invertibility excludes only
  characteristic divisors of d, exactly as in the node. Characteristic zero is allowed.
- C is nonempty and dimension one by the node's integral-curve convention. No empty
  curve or zero-dimensional scheme is accidentally included; the branch scheme may be empty.
- Nonproper and affine curves are allowed, with no geometric integrality assumption.
- All variables and the universe are explicitly bound, and `autoImplicit` is false.

Searches made for an existing theorem (all via the prescribed batch2/msearch.py unless
specified otherwise):

- LeanFinder: `A finite Galois normalization of a smooth curve of degree invertible in the
  base field is smooth when the branch points are finite etale`. Eight unrelated hits:
  standard smooth charts and Weierstrass curve reduction; no theorem matching the node.
- Loogle: `AlgebraicGeometry.Scheme.normalizationIn, AlgebraicGeometry.Smooth, IsGalois`.
  Zero hits; normalizationIn is a project declaration unknown to the Mathlib index.
- LeanSearch: `A finite Galois normalization of a smooth curve is smooth if its degree
  is invertible and its branch points are separable`. Eight hits: IsGalois normality and
  separability and relative normalization properties, not the combined curve theorem.
- Mathlib grep: `normalization.*smooth|galois.*smooth` in AlgebraicGeometry. Three hits,
  all normalization commuting with smooth base change, not this result.
- `rg -n 'tame.*[Gg]alois|[Gg]alois.*smooth|normalization.*smooth'` in both
  lean/WeilConjectures and lean/Sheaf. Related tame radical normalization and normal
  separable-point smoothness statements were read. The former requires a projective,
  geometrically integral curve with radical and root-of-unity data; the latter is a
  local criterion with residue separability as input. Neither states this node.
- `grep -rn 'lem-sfb-tame-galois-curve-normalization-smooth' lean/WeilConjectures`: no hits.
- `rg` of the chosen theorem name in dag/lean_names_upstream.json and of normalization
  data in that index: the existing normalization definition was found; the new theorem
  name has no match. The prescribed source searches also confirmed the dependency APIs.

No statement correction, new node, dependency repair, or disputed assertion was needed.

Validation: the prescribed scompile.py compiled the delivered file as both its sandbox
module and its actual library module, with no errors or warnings (8.3 s and 2.2 s).

## Second reading by Q03

Written by the maintainer's independent second reader (cc review service,
2026-10-24) in place of the worker's own second pass, which was not an
independent reading (delivery-errors H11). The Lean module and node record
are unchanged.

Node statement, item by item, against the delivered Lean:

| Node | Lean | Verdict |
|---|---|---|
| K a field, need not be perfect | `(K : Type u) [Field K]` | exact; no PerfectField |
| C a smooth integral K-curve | `(C : Scheme.{u}) (q : C ⟶ Spec (.of K)) [IsIntegralCurve q] [Smooth q]` | exact; `IsIntegralCurve` (def-pc-curve record) = separated + locally finite type + quasi-compact + integral + `topologicalKrullDim = 1`; no projectivity |
| F = K(C) | `C.functionField` (def-sc-function-field record: Mathlib generic stalk for integral schemes) | exact |
| L/F finite Galois (finite-dim, normal, separable) | `[Field L] [Algebra C.functionField L] [FiniteDimensional _ L] [IsGalois _ L]` | exact; `IsGalois` = Normal + IsSeparable |
| degree d ≥ 1 | `(d : ℕ) (hd : 1 ≤ d) (hdegree : Module.finrank C.functionField L = d)` | exact |
| image of d invertible in K | `hunit : IsUnit (d : K)` | exact |
| ν : Y → C normalization of C in L | `C.normalizationIn L`, `C.fromNormalizationIn L` (def-fin-normalization-extension record: relative normalization of Spec L → C) | exact; canonical construction |
| Y normal integral K-curve | `[IsIntegralCurve (C.fromNormalizationIn L ≫ q)]` + `hnormal : ∀ y, IsIntegrallyClosed (stalk y)` | exact; stalks are domains via `IsVariety.isIntegral` instance, so hnormal is exactly the remaining clause |
| ν finite | `[IsFinite (C.fromNormalizationIn L)]` | exact |
| D ⊂ C reduced closed subscheme | `(D : Scheme.{u}) (i : D ⟶ C) [IsClosedImmersion i] [IsReduced D]` | exact |
| D finite étale over K | `[IsFinite (i ≫ q)] [Etale (i ≫ q)]` | exact (on the composite to Spec K, not on i) |
| ν étale above C ∖ D | `U : C.Opens`, `hU : (U : Set C) = (Set.range i)ᶜ`, `hetale : Etale (C.fromNormalizationIn L ∣_ U)` | exact; U is determined by hU (closed immersion has closed range) |
| ∀ y ∈ Y above x ∈ D | `∀ y, C.fromNormalizationIn L y ∈ Set.range i → …` | exact |
| y closed | `IsClosed ({y} : Set _)` | exact |
| [κ(y):κ(x)] ∣ d | `@Module.finrank κ(ν y) κ(y) … (ν.residueFieldMap y).hom.toAlgebra.toModule ∣ d` | exact; module structure from the actual residue map of ν (x = ν y); junk 0 excluded since the true degree is finite |
| κ(y)/K finite | `((ν ≫ q).residueFieldAlgebraMap y).Finite` | exact; `Hom.residueFieldAlgebraMap` (WeilConjectures.ZetaSeries) is the canonical K → κ(y) induced by the structure map |
| κ(y)/K separable | `@Algebra.IsSeparable K κ(y) … (same algebra)` | exact; minimal-polynomial separability |
| Y → Spec K smooth | `Smooth (C.fromNormalizationIn L ≫ q)` | exact; global conjunct, outside the ∀ y |

Universes: K, C, L, D all in `u`; forced by `Spec (.of K)` over `Scheme.{u}` and
`normalizationIn` (L in the universe of C); any finite extension of `C.functionField`
has a copy in `Type u`, so no case is lost. No variable unbound; `autoImplicit false`.

Edge cases: D = ∅ (antecedent `∈ Set.range i` vacuous, U = ⊤-set, hetale gives
everywhere étale); d = 1 (L = F allowed, divisibility forces degree 1); characteristic 0
(`IsUnit (d : K)` automatic); imperfect K of characteristic p ∤ d; non-proper,
affine curves. No extra hypothesis beyond the node; `IsFinite ν` and `IsReduced D` are
node hypotheses (redundant mathematically but stated by the node).

Records and gates: the item JSON differs from the live record only by its `lean`
field; `lean.statement` is verbatim the file's signature; all 12 stmt_dep records
are byte-identical to live and their declarations are the ones used; no new
definitions, no hollow data, proof is `by sorry`; module and theorem docstrings
carry the source places (Stacks 09EB, 09ED, 0B8Y; de Jong §3.5) and
`(blueprint: lem-sfb-tame-galois-curve-normalization-smooth)`, and the theorem
docstring carries the node's seven proof steps. Non-public imports are recorded
proof-dependency modules, all present in the live tree. No pro-étale substitute.

Searches (independent): `rg 'tame.*[Gg]alois|normalizationIn.*Smooth|Smooth.*normalizationIn'`
in lean/WeilConjectures and lean/Sheaf: hits are `IsAffine.normalizationIn`
(WeilConjectures/AlgebraicGeometry/Curve/Affine.lean:70, lem-sc-finite-extension-affine-model:
affine connected curve, smoothness via regularity over a perfect field, no branch-point
residue clauses) and `exists_tame_galois_sequence` (Henselian DVR Galois groups); neither
states this node. No duplicate.

No mismatch found; nothing changed except this section.
