## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedAffineGenericFlatFinitePresentation` states
`AlgebraicGeometry.exists_dense_open_flat_locallyOfFinitePresentation_of_isReduced_affine`.
It introduces no definitions and leaves its single theorem proof as `sorry`.
The theorem docstring carries all seven proof steps of the node, with their dependency ids.
The source was read at `literature/stacks-project/morphisms.tex`, the entire statement
and proof of `proposition-generic-flatness-reduced` (Tag 052B, lines 5246–5347).
The affine structure-sheaf case gives exactly the requested conclusion. Both schemes
being affine makes the locally finite type map quasi-compact, so the source's finite
type hypothesis requires no additional assumption in the Lean statement.

Each hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Schemes U and V, in the size convention | `universe u`; `{U V : Scheme.{u}}` |
| Both schemes affine | `[IsAffine U] [IsAffine V]` |
| A morphism g : U → V | `(g : U ⟶ V)` |
| V reduced | `[IsReduced V]` |
| g locally of finite type | `[LocallyOfFiniteType g]` |
| There exists an open subscheme D of V | `∃ D : V.Opens`; the canonical scheme is `D.toScheme` and its inclusion is `D.ι` |
| The underlying subset of D is dense in V | `Dense (D : Set V)` |
| The base-changed morphism U ×_V D → D | `pullback.snd g D.ι` |
| This morphism is flat | `Flat (pullback.snd g D.ι)` |
| This morphism is locally of finite presentation | `LocallyOfFinitePresentation (pullback.snd g D.ι)` |
| No Noetherianity or irreducibility assumption | Neither appears among the binders |
| Empty affine source and target are allowed | No `Nonempty`, `Nontrivial`, integral, domain, or nonempty-open binder |

Choosing the canonical open subscheme for each `V.Opens` is precisely the open-subscheme
meaning in the node, not an additional existence requirement or an arbitrary map.
`Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and the open-immersion instance were read in
`Mathlib.AlgebraicGeometry.Restrict` lines 40–59. The type of `pullback.snd` was read
in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` lines 94–116, and
`HasPullback`/`HasPullbacks Scheme` in `Mathlib.AlgebraicGeometry.Pullbacks` lines 480–486.
Thus the conclusion uses the chosen categorical fibre product itself.

Statement dependency declarations, all read with their source signatures and docstrings:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is Mathlib's `IsAffine`,
  `Mathlib.AlgebraicGeometry.AffineScheme`, equivalent to the canonical map to
  the spectrum of global sections being an isomorphism.
- `def-weil-size-convention`: the recorded metatheoretic convention has no declaration;
  explicit `universe u` and `Scheme.{u}` implement the relevant size bound. No sites,
  coefficient objects or derived categories occur in this item.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  `Mathlib.AlgebraicGeometry.Properties`, sectionwise reducedness and its stalk equivalence.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (all affine pairs).
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, applied through the canonical `D.ι`;
  `Mathlib.AlgebraicGeometry.Restrict` supplies the actual restricted scheme.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence for schemes.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; the class's docstring explicitly
  identifies the affine-pairs definition with flatness of all stalk maps.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, the recorded exact interface.

The module publicly imports the statement interfaces above and privately imports all
already-stated proof-dependency interfaces. In particular it imports
`Sheaf.RingTheory.ReducedPolynomialModuleGenericFreeness`, whose recorded theorem is
`MvPolynomial.isOpen_dense_polynomialModuleGoodLocus` (its full statement and proof
docstring were read). The other proof imports provide `RingHom.FiniteType`,
`Module.Finite`, `Localization.Away`, `LocalizedModule.Away`,
`Module.FinitePresentation.fg_ker`, `Algebra.FinitePresentation`,
`Module.Flat.of_projective`/`Module.Flat.of_free`, and the affine principal-open
and residue-field criteria named by the proof. Affine reducedness, the locally finite
type criterion and the affine flatness criterion are already in the public imports.
There are no missing notions, repaired dependency interfaces, or import cycles.

Edge cases checked before writing:

- Empty V: a morphism into V forces U empty; `D = ⊥` is dense in the empty
  space, and both requested morphism properties are vacuous. `IsReduced` and
  `IsAffine` exclude no such schemes.
- Empty U and arbitrary reduced affine V: `D = ⊤` works; the source conditions
  and the two conclusions are pointwise vacuous.
- Identity on any reduced affine scheme, including a non-Noetherian one: `D = ⊤`
  gives the identity base change, which is flat and locally of finite presentation.
- A disconnected reduced base, e.g. Spec(k × k), is permitted. Neither affineness
  nor reducedness imposes irreducibility, and the chosen open need not be principal.
- Spec(ℤ/2) → Spec(ℤ): the good open can be D(2); the theorem does not assert
  that flatness holds everywhere or that every generic point has a fixed common rank.
- A reduced base with infinitely many components is permitted. The conclusion is
  a dense union of good principal opens, with no quasi-compactness requirement on D.

Searches for an existing statement (all against the prescribed read-only sources):

1. `msearch.py NF lem-sfb-reduced-affine-generic-flat-finite-presentation leanfinder`
   with query “A locally finite type morphism of affine schemes with reduced target
   is flat and locally of finite presentation over a dense open subset”: 8 hits,
   including `LocallyOfFinitePresentation`, `LocallyOfFiniteType`, `flat_iff`, and
   affine-pairs criteria. None asserts generic flatness over a reduced base.
2. The same wrapper, `loogle`, query
   `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`: 12 hits,
   including `UniversallyOpen.of_flat`, etale criteria, flat descent, and flat mono
   criteria. None supplies the dense open required here.
3. The same wrapper, `grep`, query `generic.*flat|flat.*generic|GenericFlat` in
   `AlgebraicGeometry`: zero hits in Mathlib.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for generic flatness and
   reduced/dense names, and exact declaration-name searches: no exact result.
   `grep -rn` for this node id in `lean/WeilConjectures` returned no result.
   The existing source modules `GenericFlatness`, `GenericFlatFinitePresentation`,
   `AffineGenericFlatness`, `GenericLocallyOfFinitePresentation`, and
   `ReducedFlatAffinePreparation` were inspected. Their generic-flatness assertions
   require an integral/domain base (the last prepares such a base using a generic
   point); they do not state this arbitrary reduced-base result. The project module
   `GenericQuasiSeparatedness` likewise requires a domain and has a different conclusion.
   `ReducedPolynomialModuleGenericFreeness` is the algebraic proof dependency, not
   the scheme theorem being stated.

Validation: the prescribed `scompile.py NF
lem-sfb-reduced-affine-generic-flat-finite-presentation <module>` compiled both
its sandbox and library checks successfully (1.4 seconds each), without diagnostics.
The node copy changes only `lean`, records the signature verbatim, and retains all
statement and proof dependencies. No statement correction or disputed statement.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
