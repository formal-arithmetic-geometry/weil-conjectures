## Worker report

The delivery states `AlgebraicGeometry.projective_inseparable_spread_normalization` in
`Sheaf.TraceFormula.ProjectiveInseparableSpreadNormalization`.  Its proof is `sorry`, as
required for stage 2.  The module and theorem docstrings cite ILO, Exposé X, proof of
Theorem 3.5, Step 5, printed pp. 163--164, and the blueprint node.

The signature renders the node clause by clause:

- `A`, `[CommRing A]`, `hbase`, `S`, and `eS` express that the base is either a field
  spectrum or a spectrum of an excellent integral discrete valuation ring.
- `Y`, `[IsIntegral Y]`, `hYexc`, `[IsHProjective p]`, and `hpdom` express an excellent
  integral `Y` with projective dominant `p : Y ⟶ S`; `hYexc` tests every affine coordinate
  ring.  `X₀`, `[IsIntegral X₀]`, `hXexc`, `[IsProper g]`, and `hgdom` render the excellent
  integral `X₀` and proper dominant `g : X₀ ⟶ Y`.
- `K`, `[Field K]`, `[Algebra Y.functionField K]`, `hKpure`, and `hKfin` render the finite
  purely inseparable extension of `κ(Y)`.  The target function-field clause is the explicit
  ring isomorphism from `Y₁.functionField` (with the integral-scheme irreducibility
  instance) to `CommRingCat.of K`.
- The first existential supplies `Y₁`, its integral instance `hY₁`, and `b`.  The following
  conjunctions state excellence on affine opens, finiteness, projectivity, properness,
  dominance, the function-field isomorphism, and projectivity of `b ≫ p` over `S`.
- `W`, `hW`, and `j : W ⟶ pullback g b` give a reduced integral dominant irreducible
  component of the fibre product: `IsClosedImmersion j`, membership of its range in
  `irreducibleComponents`, and dominance of its map to `Y₁`.
- `X₁`, `hX₁`, and `n` make `X₁` exactly `W.normalization` and `n` exactly the canonical
  `Scheme.fromNormalization` transported along `hX₁`; the next clauses give excellence,
  finiteness, and properness.
- `c` and `f` are proper dominant arrows to `X₀` and `Y₁`; `c ≫ g = f ≫ b` is the Lean
  rendering of `g ∘ c = b ∘ f`.  The dense-open `IsFinite (c ∣_ U)` clause is the required
  generic finiteness of `c`.
- The quantified `a` clause assumes properness, dominance, and generic finiteness of
  `a : X₀ ⟶ X`, and concludes the corresponding three properties for `c ≫ a` (the Lean
  composition rendering of `a ∘ c`).
- For every generic point `y₁` of `Y₁`, `Z`, `hZ`, and `jη` describe a dominant irreducible
  component of the canonical generic base change
  `X₀ ×_Y Spec K`; the final `Nonempty (f.fiber y₁ ≅ Z.normalization)` is the stated
  generic-fibre normalization identification.  The `Spec.map (algebraMap ...) ≫
  Y.fromSpecFunctionField` presentation is definitionally the fibre over `η` followed by
  `Spec K`, while avoiding a noncanonical residue-field identification.

The statement uses these recorded declarations and Mathlib matches:

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing.IsExcellent`.
- `def-kun-projective` and `def-pc-projective-morphism`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective.IsHProjective`.
- `def-pc-fibre-product`: Mathlib `CategoryTheory.Limits.pullback`, `pullback.fst`,
  and `pullback.snd`.
- `def-pc-field-extension`: Mathlib `Algebra` together with `Field` instances.
- `def-pc-integral-scheme`: Mathlib `AlgebraicGeometry.IsIntegral`.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme`.
- `def-pc-scheme-fibre`: Mathlib `Scheme.Hom.fiber`.
- `def-sc-discrete-valuation-ring`: Mathlib `IsDiscreteValuationRing`.
- `def-sc-function-field`: `Sheaf.AlgebraicGeometry.FunctionField`'s component
  declaration, with Mathlib `Scheme.functionField` for integral schemes.
- `def-sc-generic-point`: Mathlib `IsGenericPoint`.
- `def-sc-normalization`: upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` declarations
  `Scheme.normalization` and `Scheme.fromNormalization`.
- `def-weil-finite-integral-morphism`: Mathlib `IsFinite` and `IsIntegralHom`.
- `def-weil-irreducible-components`: Mathlib `irreducibleComponents`.
- `def-weil-pbc-finite-purely-inseparable-extension`: Mathlib
  `IsPurelyInseparable` and `Module.Finite`.
- `def-weil-proper-morphism`: Mathlib `IsProper`.

No new definition node or dependency repair was needed.  All notions are taken from the
recorded declarations or Mathlib; no private copy was introduced.

Edge cases checked before writing include: the field branch of `hbase`, the trait branch,
`K = κ(Y)` (identity purely inseparable extension), characteristic zero, empty or
zero-dimensional projective space, `X₀` and `Y` of dimension zero, a single irreducible
component, the zero-dimensional generic fibre, and the empty dense-open complement in the
finite-over-dense-open clauses.  The existential formulation does not exclude any of these.

Searches performed:

- `msearch.py ... leanfinder "finite purely inseparable extension function field projective
  normalization dominant component proper base change"`: eight generic normalization and
  purely-inseparable hits, but no theorem combining the required spread construction.
- `msearch.py ... loogle "Scheme.normalizationIn, IsFinite, IsHProjective"`: unavailable
  (`Scheme.normalizationIn` unknown); no absence claim was drawn from this query.
- `msearch.py ... grep "normalizationIn|IsPurelyInseparable|IsHProjective"
  AlgebraicGeometry`: three Mathlib universally-injective/purely-inseparable hits and no
  combined theorem.
- `rg` over `WeilConjectures/` and shared `lean/Sheaf/` for normalization, projective,
  purely-inseparable, and generic-finite terminology: existing component declarations and
  helper APIs only; no exact theorem declaration.
- The node's recorded stage-1 LeanFinder, Loogle, and grep searches were also read; they
  likewise found no exact match.

## Second reading by Q10

I reread the node statement and this module after compilation.  Every input hypothesis and
all conclusion clauses are present: the two base alternatives, both excellence conditions,
projective/proper/dominant maps, finite purely inseparable extension, normalization data,
component condition, canonical normalization map, commutative square, generic finiteness,
the additional-composite clause, and generic-fibre normalization.  The only Lean adjustment
from the prose is the categorical order of composition (`c ≫ g`, `f ≫ b`, and `c ≫ a`),
which is exactly the same composite.  No statement correction was made.

## Maintainer review fix (cc review service, 2026-10-18)

The delivered statement was weaker than the node in three clauses. The fixed module adds:

1. `κ(Y₁) ≅ K` is an isomorphism of `κ(Y)`-algebras: `∃ φ : Y₁.functionField ≅ CommRingCat.of K,
   Spec.map φ.hom ≫ Y₁.fromSpecFunctionField ≫ b = Spec.map (algebraMap κ(Y) K) ≫ Y.fromSpecFunctionField`.
   The bare `Nonempty (Y₁.functionField ≅ K)` held for `Y₁ = Y`, `b = 𝟙` whenever `K ≅ κ(Y)` as abstract
   fields (e.g. `κ(Y) = 𝔽_p(t)`, `K = κ(Y)(t^{1/p})`). The parent lem-trf-generic-smooth-boundary-preparation
   needs `κ(Y) ⊂ κ(Y₁)` to be finite purely inseparable, which an abstract isomorphism does not give.
2. `c = n ≫ j ≫ pullback.fst g b` and `f = n ≫ j ≫ pullback.snd g b`: `X₁` is the normalization of the
   component `W` and `c`, `f` are its maps to the factors. In the delivered version they were arbitrary.
3. The generic-fibre identification is an isomorphism `e : f.fiber y₁ ≅ Z.normalization` over `X₀`
   (`e.hom ≫ ν ≫ jη ≫ pr₁ = f.fiberι y₁ ≫ c`) and over `Spec K` through a `κ(Y)`-compatible
   `ψ : κ(y₁) ≅ K`. The delivered version used a bare `Nonempty` isomorphism of schemes, which cannot
   carry the `κ(y₁)`-structure that the parent's smoothness clause uses.

Everything else is unchanged. The proof is still `sorry`. The per-file compile through `nt_compile.py`
is clean.
