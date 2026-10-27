## Worker report

The module `Sheaf.AlgebraicGeometry.TraitSpecializationEtaleChartDensity` states
`CategoryTheory.trait_specialization_etale_chart_density`, with its sole theorem
proof `sorry`. Its two data definitions construct the canonical closed and generic
arrows of the trait, rather than assume unspecified maps. No definitions or
statements are corrected. The item gains the already landed definition nodes
`def-sfb-open-moduli-substack` and `def-sfb-moduli-chart-normalization` in stmt_deps,
as permitted by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES). These supply the
existing notions in the original statement; no new node is needed.

Sources read: Stacks `moduli-curves.tex`, `lemma-smooth-dense` (0E86), including
its final specialization argument, and `lemma-smooth-dense-in-stable` (0E87);
`algebra.tex`, `lemma-map-into-henselian` (08HQ), including its retraction proof.
The current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md` was also
read; this node is an auxiliary input, not the statement of a blueprint unit.

Hypothesis and conclusion correspondence:

- The base field is `(k : Type u) [Field k]`. `F` is a category over
  `Over (Spec (.of k))`, with arbitrary explicitly bound total-category universes
  `v,w`. `hF : IsDeligneMumfordModuliStack F` is the recorded DM condition, including
  stack descent, representable diagonal, and an etale surjective scheme atlas.
- `U : OpenModuliSubstack F` uses the existing full object predicate, pullback
  stability, and scheme-test representation by an actual open immersion. We do
  not replace the full groupoid by isomorphism classes.
- Algebraically closed extensions are quantified as `Ω : Type u`, `[Field Ω]`,
  `[IsAlgClosed Ω]`, `[Algebra k Ω]`; they need not be algebraic over k. In
  particular `[IsAlgClosure k Ω]` would incorrectly exclude transcendental
  extensions and is not assumed.
- `x : BasedFunctor (discreteModuli (yoneda.obj (algSpec ... Ω))) F` is a
  scheme-valued object in the existing convention. For a CFG this is the
  representable-category formulation of an object of F(Ω), retaining its
  automorphisms, not an arbitrary function on points.
- `htraits` gives an actual map `ξ` from the relative spectrum of `PowerSeries Ω`
  and `Nonempty (ModuliTwoIso (closed.comp ξ) x)`. Thus its closed restriction
  is isomorphic to the specified x, not merely equal on isomorphism classes.
- Its generic restriction belongs to U by the predicate
  `∀ z, U.property (ξ.obj (generic.obj z))`. Here z ranges over the entire
  representable category of `Spec (Localization.Away PowerSeries.X)`. This
  expresses factorization of the generic map into the full substack. It is
  equivalent to membership of that scheme-valued object: it includes the identity
  test object, and pullback stability supplies every other test object.
- The ring `PowerSeries Ω` is Mathlib's `MvPowerSeries Unit Ω`, the one-variable
  case of the recorded definition. The puncture is exactly localization at X.
  `algSpec` gives each spectrum its canonical k-structure. `moduliTraitClosed`
  is the spectrum of `PowerSeries.constantCoeff`, regarded as an Ω-algebra
  homomorphism using the existing `constantCoeff_C` theorem, then restricted to k.
  `moduliTraitGeneric` is the spectrum of the canonical localization algebra map
  `IsScalarTower.toAlgHom`; neither helper contains postponed data or a new proof.
- An arbitrary chart is `(V : Over (Spec (.of k)))` and a scheme-valued map `a`.
  Its sole map hypothesis is `IsEtaleModuliMap a`, the existing definition of
  representable etaleness tested on all scheme base changes. Surjectivity of a
  is not required. The surjectivity inside hF belongs to some DM atlas, not to a.
- Each geometric point is `v₀ : Spec Ω ⟶ V` over k. The lifting conjunct quantifies
  over every `ξ`, every prescribed `φ : ModuliTwoIso (closed.comp ξ) (v₀.comp a)`,
  and the generic-U condition for that ξ. Thus it is not restricted to an
  existentially selected smoothing from htraits.
- The resulting `v₁ : Spec Ω[[t]] ⟶ V` satisfies the actual equality
  `moduliTraitClosed k Ω ≫ v₁ = v₀`. Its `e : ModuliTwoIso ξ (v₁.comp a)` is the
  inverse orientation of the isomorphism a(v₁) ≃ ξ in the prose, hence equivalent.
- The final `HEq` compares the hom natural transformation of e restricted by
  `Functor.whiskerLeft` with `φ.val.hom`. The source is the same restricted ξ;
  target functors agree by the preceding equality of scheme maps and Yoneda's
  composition law. Heterogeneous equality permits precisely this canonical
  transport of endpoints. It requires equality of the actual transformation,
  not just existence of an isomorphism at the special point. Equality of the hom
  components also determines the inverse, so the entire prescribed iso is kept.
- The other conjunct supplies `W`, `j : W ⟶ V`, and its comparison `c` with the
  actual `moduliTwoFiberProduct a (fullModuliInclusion F U.property)`.
  `IsSchemeModuliBaseChange c j` identifies its projection with j,
  `IsOpenImmersion j.left` makes it the open subscheme in the statement, and
  `DenseRange j.left` states that the closure of its image is all of V.
- There is no smoothness hypothesis on F and no finite-type, quasi-compactness,
  separatedness, or surjectivity hypothesis on V or a.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, extending CommRing and DivisionRing.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsDeligneMumfordModuliStack`, `ModuliTwoIso`, `discreteModuli`,
  `discreteModuliMap`, and `moduliTwoFiberProduct`. Full definitions and their
  docstrings were read, including `HasSpaceBaseChange` and `SpaceMapIsEtale`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (polynomial splitting).
  The geometric-point dependency's other declaration, `Scheme.SpecToEquivOfField`,
  was read in `Mathlib.AlgebraicGeometry.ResidueField`; its residue-field embedding
  description is used in the natural-language density proof.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`; the one-variable
  alias, coefficient map, C and X were read in `Mathlib.RingTheory.PowerSeries.Basic`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`,
  `fullModuliInclusion`, and `OpenModuliSubstack.category` (the latter supplies the
  interpretation of the full substack in the inherited interface).
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `IsEtaleModuliMap` and
  `IsSchemeModuliBaseChange`. Their complete scheme-test signatures are used,
  without importing any normalization hypothesis into the theorem.
- `Mathlib.AlgebraicGeometry.Group.Affine`: `algSpec` and its map construction;
  `Mathlib.Algebra.Algebra.Tower`: `AlgHom.restrictScalars`;
  `Mathlib.Algebra.Algebra.Hom`: `IsScalarTower.toAlgHom`.

All already stated proof-dependency modules are imported, including the power-series
quotient and completion inputs, henselian lifting, algebraic-space fibre products,
chartwise etale permanence, etale/weakly-etale comparison and the algebraically
closed-field section theorem. The pointed affine-shrink Mathlib interface is in
`Mathlib.AlgebraicGeometry.OpenImmersion`. The only proof dependency without a
recorded statement is `lem-sfb-dm-etale-atlas-calculus`; it supplies no import yet
and is not a statement prerequisite. Its eventual proof-only import can be added
when that node lands. No theorem of that node is assumed as an extra hypothesis.

Edge cases checked before drafting and again on reading:

- Empty V has a valid empty open representation, DenseRange is vacuous, and it
  has no geometric points to lift. Empty F is likewise allowed by the statement.
- The empty open U cannot satisfy htraits at any existing geometric object;
  where F has no geometric objects the condition and chart conclusions are vacuous.
- Ω may have positive characteristic and may be transcendental over k.
- V can have arbitrarily many components, nonclosed points and no finite-type
  hypothesis. Every y has a geometric point over an algebraic closure of κ(y),
  which lives in the fixed scheme universe u. No closed-point-only test is used.
- φ is universally quantified, so nontrivial stack automorphisms and different
  framings are retained; the HEq clause does not discard them.
- The chart need not cover F and need not be nonempty. The source's proof uses
  only its representable etaleness, and strict henselian lifting preserves the
  selected special point.

Searches actually run:

- msearch.py leanfinder: "An open substack is dense on every etale chart if each
  geometric point admits a formal power series trait with generic point in the
  open". Eight hits: partial-map dense opens, etale locus openness and dominant
  maps. None provides a framed trait lift or the stack criterion.
- msearch.py loogle: "Dense, IsOpenMap". One hit `Dense.preimage`; it assumes
  density already and does not construct traits or framed lifts.
- msearch.py grep: "trait.*dens|dens.*trait|DeligneMumford|OpenModuliSubstack".
  Zero Mathlib hits.
- rg in `lean/WeilConjectures` for the item id and for trait/density combinations:
  no matching statement. rg in `lean/Sheaf` for open moduli substacks and
  trait/density found the already landed interfaces above and references to this
  still unstated node in proof docstrings, not an existing theorem. The chosen
  helper and theorem names were also searched in both libraries and the upstream
  name index; no collision.

Validation: the prescribed scompile wrapper compiled the file against the current
server sources in 6.0 seconds, with no errors or non-sorry warnings after fixing
one syntax issue in the scalar-restriction helper. Its local compilation attempt
reported `OSError(28, 'No space left on device')`; the wrapper's normal server
confirmation succeeded. The final dry run and delivery repeat the file check.

## Second reading by NB

A separate reading pass in this worker session checked the node alongside the full
signature and the definitions of the two landed stack interfaces. No other agent
was started, as required by the dispatch brief; the maintainer's independent
review remains separate.

The main checks were preservation of all choices of φ, actual equality of the
closed map, arbitrary (not necessarily surjective) charts, arbitrary algebraically
closed field extensions, and the scheme-test interpretation of the open. The e
orientation was checked against φ: both restricted hom transformations run from
ξ on the closed point toward a(v), so the HEq clause has the right orientation.
The density conclusion retains the comparison c and j, rather than asserting
density for an unrelated open W. The helper maps are genuine reductions and
localizations, with explicit k-linearity inherited from Ω. The read-through added
the two already landed definition dependencies and explicit public imports of the
original Mathlib statement-dependency modules. No mathematical mismatch or
STATEMENT-DISPUTED condition was found; the natural-language statement is unchanged.
