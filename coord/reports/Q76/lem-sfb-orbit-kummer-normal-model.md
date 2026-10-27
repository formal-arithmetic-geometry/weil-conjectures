## Worker report

The module `Sheaf.AlgebraicGeometry.OrbitKummerNormalModel` states
`AlgebraicGeometry.orbit_kummer_normal_model`. Its sole postponed proof is `sorry`.
Seven helper declarations give real constructions belonging to this node:
`orbitKummerGenericCurve`, `orbitKummerGenericPoint`, `orbitKummerRadicand`,
`orbitKummerField`, `orbitKummerBranchLocus`, `orbitKummerLiftingPairs`, and
`orbitKummerGenericExtension`. Their declaration docstrings cite de Jong §3.5;
the theorem docstring carries all ten original proof steps and their dependency IDs.
No new independent mathematical notion or dependency repair is needed.

The source read was de Jong, *Families of curves and alterations*, §3.4,
printed p.606, and §3.5, printed pp.606–608, in the publisher PDF:
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf (PDF pages 8–10).
The current blueprint unit `sk-thm-sf-ctf-stability/_section.md` was also read.
This item is an extracted proof lemma, not the unit's own statement.

Hypotheses, in the order of the statement:

- The field is `(k : Type u) [Field k]`. The schemes are `S X : Scheme.{u}`;
  `[IsIntegral S] [IsIntegral X]` retain nonemptiness, reducedness and irreducibility.
  `pS`, `pX` are their structure maps. `[IsHProjective pS]`, the two
  `LocallyOfFiniteType` and `QuasiCompact` pairs, and `hSnormal`, `hXnormal` render
  projectivity, finite type and normality. `IsNormalScheme` asks exactly for
  integral schemes with integrally closed domain stalks.
- `(f : X ⟶ S) [IsHProjective f]` and `hf : f ≫ pS = pX` render the morphism
  over k. `hpure` quantifies over every algebraically closed field-valued point
  in the scheme universe and uses `Scheme.IsPureDimension 1` on its pullback.
- `K` and `F` are the actual generic stalks `S.functionField` and `X.functionField`.
  `orbitKummerGenericCurve f` is exactly `pullback f S.fromSpecFunctionField`.
  The two instances on `pullback.snd` are its smoothness and geometric integrality.
  `[Algebra K F]` is fixed by `hKF`, the equality of its spectrum map with the
  generic-point map through f. This is a presentation of the embedding named in
  the node, not an arbitrary extra field extension or a dominance assumption.
- `G` has `[Group G] [Finite G]`, with no faithful-action hypothesis.
  `σk`, `σX`, `σS` and `hGkX`, `hGkS`, `hGf` give the compatible semilinear
  actions. The supplied action on F is fixed by `hGfield` to pullback along the
  inverse geometric action, using `Scheme.functionFieldAut`. `σC`, `hCX`, `hCK`
  give the induced action on the generic pullback: its two projections determine
  it. These are the actions already implicit in the words “act compatibly”.
- `M : Closeds C` denotes its reduced closed subscheme via
  `(Scheme.IdealSheafData.vanishingIdeal M).subschemeι`. `hMfinite`, `hMetale`
  impose finite etaleness over K. `hMstable` is stability under the induced action.
- `ell`, `hell`, `hell5`, `hchar` give the prime, lower bound and characteristic
  restriction. Since k is a field, `(ell : k) ≠ 0` is precisely invertibility
  of this prime in k and all its extensions. `ζ`, `hζ : IsPrimitiveRoot ζ ell`
  give the specified primitive root in K.
- `m`, `U`, `hUaffine`, `hUne`, `hUcover` give the finite affine cover, with the
  source-based nonempty-open correction explained below. `φ`, `hφover`,
  `hφfinite`, `hφsurj` give the local finite surjective pencils over these opens.
- `e` and `he` are the canonical factorizations of Spec K into U_i. `c`, `hcX`,
  `hcK` are the canonical pullback comparison maps. `ψ`, `hψover`, `hψφ` are
  the generic pencils; the projective-space base-change equation fixes them.
  These comparison maps are specified by their projections, not chosen
  replacements for the pencils. `hψetale` says that the pencil is etale over a
  dense open of its target, including the identity/whole-open case.
- `hspecial` gives finite etaleness of each actual fibre product over the three
  standard sections, spelled inline as `if j = 2 then ProjectiveLine.infinity ...`
  and otherwise `AffineSpace.homOfVector (𝟙 ...) (fun _ ↦ if j = 0 then 0 else 1)`
  followed by `ProjectiveLine.affineChart` (zero, one, infinity).
  A finite etale scheme over a field is reduced, so no separate reducedness
  hypothesis is needed. `havoid` gives disjointness of each inverse image from M.
- `x` and `hx` identify the actual affine coordinate functions: their generic
  morphisms are `AffineSpace.homOfVector` on x_i followed by `affineChart`.
  `ΓSpecIso.inv` is the standard conversion from a field element to its global
  section. This equation fixes x_i, rather than assuming unrelated rational functions.
- `Ω` is an algebraic closure of F. `L` with `hL` is the actual intermediate field
  `orbitKummerField`, the adjunction of all ell-th roots of the orbit radicands.
  Since F contains the primitive root, all roots of a nonzero radicand differ by
  elements of F; this is exactly the field obtained by choosing one root per
  entry, independently of choices. The K-algebra structure and scalar-tower
  instance encode the composite K → F → L. The B0-algebra structure is fixed by
  `hBL` to B0 → F → L, where B0 is Mathlib's `FixedPoints.subfield G F`.
- `E` with `hE` is Mathlib's relative `algebraicClosure K L`, exactly the elements
  algebraic over K. `D` with `hD` is the reduced closed orbit union constructed
  from the three special inverse images. Introducing these named intermediate
  fields and closed set with defining equalities avoids hidden statement lets.

Conclusions, clause by clause:

- The first universal conclusion says that every radicand is nonzero, including
  every i, g and each of the two functions. The next equivalence identifies D
  pointwise with the union of the translates themselves; the closure in the
  helper definition therefore adds no points. The following `IsFinite`, `Etale`
  and `Disjoint` give the asserted reduced finite etale branch locus avoiding M.
- The next universal conclusion says that every radicand is the image of a unit
  of the local ring of C at every point outside D. Its local-ring embedding into
  F is fixed by the equation on spectra through `orbitKummerGenericPoint`.
  This states exactly that every zero and pole is contained in D; a unit and its
  inverse are regular there. It does not assume a private function-field algebra.
- `Module.Finite F L ∧ IsGalois F L` and the corresponding pair for B0 give both
  finite Galois extensions. Mathlib's `IsGalois` means normal and separable;
  finiteness is explicitly separate. `Module.Finite K E` and
  `Algebra.IsSeparable K E` give finite separability of the constants.
- The membership equivalence for `a : F` asserts `E ∩ F = K`, using the ranges
  of the exact maps fixed above.
- Put γ = `orbitKummerGenericExtension f hKF L`. It is the composite
  Spec L → Spec F → C. Mathlib's `γ.normalization`, `γ.fromNormalization`,
  `γ.toNormalization` are the actual relative normalization, normalization map,
  and generic map. This is the normalization of C in L, with no chosen comparison
  or arbitrary replacement scheme. The existential `pE` is fixed on Spec L by
  `γ.toNormalization ≫ pE = Spec.map (algebraMap E L)` and over K by its other
  equation. Smoothness over K, etaleness over C minus D, and smoothness,
  H-projectivity and geometric integrality over E are explicit conjuncts.
- `orbitKummerLiftingPairs` is precisely the subtype of pairs (g, τ) in
  G × Aut_B0(L) satisfying the restriction equation on every a in F.
  The existential `Group` witness has projection homomorphisms `β`, `τ`, which
  are required pointwise to equal the two components. As these components
  jointly inject, these requirements fix the componentwise group law uniquely.
  `Function.Surjective β` asserts J → G is onto; the `MulEquiv` ε identifies
  its kernel with Aut_F(L), with equality on every z in L. The next equivalence
  says L^N = F via the canonical inclusion.
- The homomorphism `τE` is required to agree with τ after E → L. Thus it is
  exactly the restriction action on E and asserts preservation of E. Its
  fixed-point equivalence is precisely E^N = K.
- The relative models are the literal schemes `S.normalizationIn E` and
  `X.normalizationIn L`. Their `IsNormalScheme` conjuncts include integrality.
  H-projectivity and the finite-type pairs of the specified structure maps give
  the claimed properties over k. The canonical T → S is finite surjective.
  The map r to `pullback f (S.fromNormalizationIn E)` is finite surjective and
  has first projection equal to the canonical normalization map Y → X and
  second projection q. Hence it is exactly the asserted factorization, not an
  unrelated finite map. q is H-projective with all geometric fibres pure of
  dimension one.
- ηE is set equal to the canonical generic map from Spec E into T. The equations
  for `cY` identify its map to X and its map to T. The additional equality
  `γ.toNormalization ≫ cY = (X.fromSpecOfAlgebraFunctionField L).toNormalization`
  fixes its map on the specified generic field L. `IsPullback cY pE q ηE`
  identifies the generic E-fibre of q with the above smooth projective
  geometrically integral normalized curve. Its dimension-one property follows
  from the stated pure geometric fibres. This identification fixes the
  E-structure and includes the actual generic field embeddings.
- `aT`, `aY` are J-actions. Their three equivariance equations lift the G-actions
  on S, X, f. Their equations at the canonical Spec E and Spec L points enforce
  exactly the prescribed τE and τ field actions; the inverse index compensates
  for contravariance of Spec. Compatibility with k follows by composing the
  displayed equivariance equations with hGkX and hGkS, without a new hypothesis.
- The last `IsFinite` and `Etale` apply to the actual pullback of M along the
  normalization map, with structure map to Spec E. This pullback is already
  reduced because it is etale over E, so equals the reduced generic inverse
  image in the node. `aC` is its induced generic action, fixed by equivariance
  with Y, E and C. The last image equality gives stability of the marking.

Dependency declarations read and reused:

- `Field`; `Algebra` (`Mathlib.Algebra.Algebra.Defs`); `AlgebraicClosure`,
  `IsAlgClosure` (`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `.Basic`).
- `AlgebraicGeometry.IsIntegral` (`Mathlib.AlgebraicGeometry.Properties`),
  `LocallyOfFiniteType` and `QuasiCompact` (`Morphisms.FiniteType`, `.QuasiCompact`).
- `AlgebraicGeometry.IsHProjective`
  (`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`).
- `Scheme.functionFieldOfComponents` in
  `WeilConjectures.AlgebraicGeometry.FunctionField` was read; its arbitrary
  integral-scheme clause uses `Scheme.functionField` from Mathlib directly,
  as this theorem does. The generic map is `Scheme.fromSpecFunctionField` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`.
- `Scheme.IsPureDimension` (`Sheaf.AlgebraicGeometry.PureDimension`).
- `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`
  (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`) give both the
  geometric fibres and the fibre products of the node.
- `Smooth`, `SmoothOfRelativeDimension` (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`),
  `GeometricallyIntegral`, `GeometricallyIrreducible`, `GeometricallyReduced`
  (`Mathlib.AlgebraicGeometry.Geometrically.Integral` and its imports) were read;
  this theorem needs Smooth and GeometricallyIntegral only.
- `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`) define the two
  relative normal models. For C, `Scheme.Hom.normalization` is their underlying
  Mathlib relative construction, applied to Spec L → C; this avoids manufacturing
  a second function field or a noncanonical algebra structure.
- `IsFinite`, `IsIntegralHom` (`Mathlib.AlgebraicGeometry.Morphisms.Finite` and
  `.Integral`), `Surjective` (`Morphisms.UnderlyingMap`), and `Etale`
  (`Morphisms.Etale`) give the indicated morphism properties.
- `ProjectiveSpace`, `ProjectiveLine`, `ProjectiveSpace.map`,
  `ProjectiveLine.affineChart`, `ProjectiveLine.infinity` are the recorded
  projective-space construction and its published chart interface.
- `Scheme.arithmeticGenus` (`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`)
  was read as requested by the existing dependency list; this node asserts no
  genus bound, so its definition is not applied or duplicated here.
- The three standard sections are spelled inline from the existing projective-line
  primitives above. The local-pencil theorem and its helper definition are not
  imported or cited as a statement dependency.
- Additional existing APIs: `Scheme.functionFieldAut`, `IsNormalScheme`,
  `Scheme.IdealSheafData.vanishingIdeal`, `subschemeι`, `IntermediateField.adjoin`,
  `FixedPoints.subfield`, `algebraicClosure`, `IsPrimitiveRoot`, and `IsGalois`.
  Their definitions and the relevant full signatures were inspected.

The module imports the recorded proof-dependency modules already stated, and
Mathlib modules for the Mathlib proof leaves (primitive element, splitting
field, normal lifting, separable transitivity, fixed fields, finite morphism
permanence, Noetherian schemes, affine fraction fields, localization).
The following proof prerequisites currently have no recorded declaration and
are not needed to type this statement: `lem-sfb-radical-normalization-projective-etale`,
`lem-sfb-tame-galois-curve-normalization-smooth`,
`lem-sfb-smooth-cover-constant-field-marking`,
`lem-sfb-semilinear-finite-normalization-model`,
`lem-sfb-finite-curve-factor-projective-pure`. Their proof references are retained
verbatim in the docstring and DAG; their imports can be added when stated.

Edge cases checked before and after writing:

- Empty X or S is excluded by the source's integrality; an empty index m cannot
  cover this nonempty S. Empty M is allowed and makes all marking conclusions
  the empty finite etale scheme. The removed empty-open case is the correction below.
- G can be trivial, act trivially, or have a nontrivial kernel; J is the actual
  fibre product with G, not its effective image. No faithful-action API is assumed.
- S may be a point and k may be finite. No positive-dimensional base or infinite
  field hypothesis is added. The supplied pencils are used exactly as given.
- Repeated pencils or repeated roots do not change the adjunction or branch union.
  The radical field may equal F and E may equal K. All fixed-field statements use
  images, so these identity cases remain included.
- Imperfect k and nontrivial semilinear action on k are allowed. The theorem
  asserts the substantive smoothness over K rather than inferring it from normality.
- The characteristic restriction and primitive root are explicit; ell = 0, 1, 2, 3
  are excluded exactly by the prime and lower-bound hypotheses. No extra root
  choices, split action, or linearization is assumed.
- Group universe v is independent of the scheme universe u. The field objects
  and normalizations use the scheme universe; auxiliary geometric fields use
  that same universe, matching Mathlib's geometric-property convention. There
  is no smaller independent test-field universe.

Searches actually run:

- msearch leanfinder: `finite group orbit Kummer radical extension normalization
  family of curves semilinear action` returned eight hits, including
  `FixedPoints.normal`, `FixedPoints.toAlgAut_surjective`, and
  `autAdjoinRootXPowSubCHom`; none states this relative model theorem.
- msearch loogle: `IntermediateField.adjoin, IsGalois, Scheme.normalizationIn`
  returned zero hits and the diagnostic `unknown identifier 'Scheme.normalizationIn'`.
  It is not evidence of absence of the published normalization construction;
  that construction was located and read directly instead.
- msearch grep: `Kummer|Semilinear|semilinear|normalizationIn` in Mathlib
  AlgebraicGeometry returned four unrelated semilinear structure-sheaf lines.
- msearch leansearch: `finite group orbit radical Kummer field normalization
  semilinear normal curve model` returned eight fixed-field/Galois hits, including
  `IsGalois.of_fixed_field` and `FixedPoints.toAlgAutMulEquiv`; none is this theorem.
- Direct rg over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node ID and `orbitKummer|orbit_kummer_normal_model` found no existing
  declaration. Concept searches found the existing normalization, field-action,
  projective charts, high-genus cover and local-pencil modules, which were read.
  On repair, the standard sections are spelled inline from the projective-line
  primitives, as expressly permitted by the reviewer, without a helper declaration.

Validation of the returned version: the prescribed scompile.py compiled it as
both a sandbox module and its intended library module, without errors or warnings.
The repair is compiled and preflighted again as recorded below. No proof, axiom,
local notation, private definition, local instance, auto-bound implicit or statement
let is introduced.

## Statement corrected

The old statement is preserved verbatim in `statement_change.old_statement`.
The only prose change is “finite affine cover” → “finite affine cover by nonempty
opens”. An empty affine open is permitted in a cover, and the unique empty-source
pencil is finite surjective to the empty projective line, but has no generic
coordinate x_i in F. Thus the old root list is undefined in that case.
De Jong §3.4 constructs each U as a neighbourhood of a closed point and §3.5
chooses a finite subcover of precisely these nonempty opens. This correction
follows that source, changes no unit statement and requires no change to any
proof step or proof dependency.

The repaired statement-dependency list is identical to the current main node's
list. The unnecessary theorem dependency was removed; no `old_stmt_deps` field
remains because the delivery no longer changes `stmt_deps`. The correction record
now describes only the source-based nonempty-open correction.

Citer audit: rg for `"lem-sfb-orbit-kummer-normal-model"` in all DAG nodes found,
other than the item itself, exactly `lem-sfb-high-genus-equivariant-cover`.
It cites the item in its proof steps constructing the Kummer cover and composing
models. Its use still holds: those pencils come from nonempty affine
neighbourhoods, and any superfluous empty members can be deleted before applying
this lemma without changing the radical field, orbit locus or normal models.
This citer is recorded with `holds: true`; it was read and not edited.


## Repair of return a6cc5bb80b70

F1 (H2): removed the import of `Sheaf.AlgebraicGeometry.InvariantLocalCurvePencils`
and its theorem-node dependency `lem-sfb-invariant-local-curve-pencils`. All five
uses of `invariantPencilSpecialPoint` (in the branch-locus helper, both special-fibre
hypotheses, avoidance, and the pointwise branch-union conclusion) are now the exact
inline section formula from `ProjectiveLine.infinity`, `AffineSpace.homOfVector`
and `ProjectiveLine.affineChart`. This is the reviewer-permitted inline option;
there is no new definition, re-export, or duplicate declaration. For j = 0 the
formula is [0:1]; for j = 1 it is [1:1]; for j = 2 it is infinity [1:0]. The
statement dependencies now match current main exactly. Removed `old_stmt_deps`
and the obsolete dependency explanation from `statement_change`; the original
nonempty-open correction, old statement, source and complete citer audit remain.

F2 (H3): added the requested conclusion verbatim:

```lean
(orbitKummerGenericExtension f hKF L).toNormalization ≫ cY =
  (X.fromSpecOfAlgebraFunctionField L).toNormalization
```

It pins cY to the canonical Spec L maps into both normalizations. Thus the generic
comparison preserves the specified identification with L, and its equivariance
with aY pins aC to the specified tau action rather than a deck-conjugate action.
The node's `lean.statement` was regenerated from the repaired theorem signature,
verbatim from `theorem` through the type before `:=`.

Compared the retained sandbox record with the returned-head findings and current
main's node: current main has no Lean attachment and retains the original
statement and eighteen definition dependencies. The repair preserves every
other node field and all ten proof steps. The only main-node changes are the
reviewed nonempty-open prose correction, its `statement_change`, and the repaired
Lean record. The only citer remains `lem-sfb-high-genus-equivariant-cover`, whose
use still holds as explained above. No source checkout or live Lean file was edited.

Repair validation: `scompile.py Q76 lem-sfb-orbit-kummer-normal-model` compiled the
repaired file separately as `Sheaf.Stage2.Sandbox0` (14.7 s) and
`Sheaf.AlgebraicGeometry.OrbitKummerNormalModel` (9.5 s), with no errors or warnings.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
