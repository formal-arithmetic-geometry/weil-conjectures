## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidHypersurfaceSlice` states
`AlgebraicGeometry.exists_cm_groupoid_hypersurface_slice`, with `sorry` as its whole
proof. It adds no definitions, axioms, instances, or helper theorems. The node is
unchanged except for `lean`. Its nine accepted proof steps appear in the theorem's
docstring with their dependency ids.

I read the current stage-2 brief, the node and all its statement dependencies and
recorded interfaces, and Stacks `more-groupoids.tex`, Situation 04MY and Lemma 0461
including its full proof. The previous ending was a stage-1 unchanged-split refusal.
The current brief's stage handoff explicitly permits stating this accepted split.
There is no repair note for this item and no existing Lean record to withdraw.

### Hypotheses and conclusions

| Node clause | Lean rendering and interpretation |
| --- | --- |
| Scheme S and the size convention | Explicit `universe u` and `{S U R : Scheme.{u}}`; every constructed scheme has the same scheme universe, and no site or coefficient universe is introduced. |
| A groupoid scheme with the indicated operations | `s t`, `e`, `i`, `c : pullback s t ⟶ R`, and `hG : IsGroupoidScheme s t e i c`, using the dependency's complete groupoid laws. |
| Every structure map is over S | `p : U ⟶ S`, `q : R ⟶ S`, `hs : s ≫ p = q`, `ht : t ≫ p = q`. These are equivalent to the relative groupoid condition: the identity law gives `e ≫ q = p`, the inverse law gives `i ≫ q = q`, and the composition-source law gives `c ≫ q = pullback.snd s t ≫ q`, equal to the first-projection structure map by the pullback condition. Thus no base compatibility is omitted. |
| s and t are flat at every point | `[Flat s] [Flat t]`, equivalent to stalkwise flatness by Mathlib `Flat.iff_flat_stalkMap`. |
| Their fibre local rings are Noetherian with depth equal to dimension | `hcm` quantifies over `f = s ∨ f = t` and every `r : R`, and asserts `IsNoetherianRing` and the equality between the coerced `IsLocalRing.depth` of the fibre stalk at `f.asFiber r` and its `ringKrullDim`. This is exactly the two global Cohen-Macaulay conditions, with no condition on other morphisms. |
| s and t are locally of finite presentation | The two `LocallyOfFinitePresentation` instance binders. |
| u is a finite type point | `(u : U)` and `LocallyOfFiniteType (U.fromSpecResidueField u)` together with `QuasiCompact` of that same map, the recorded finite-type definition. |
| F_u and its identity point | Mathlib's `s.fiber` and `s.asFiber (e u)`. The latter lies in the fibre over `s (e u)`; `hG.identity_source` identifies this base point with u, so this is canonically the specified point in F_u. Transport along that equality gives the same local dimension. |
| G_u is the stabilizer fibre over the single residue-field point | In `hdrop`, `pullback.lift s t (hs.trans ht.symm)` is `(s,t) : R ⟶ U ×_S U`. The other `pullback.lift` is `(u,u) : Spec κ(u) ⟶ U ×_S U`. Their pullback is precisely G_u, and `topologicalKrullDim` is its global dimension. The expression does not replace G_u by the double restriction with two independent field factors. |
| d2 is finite and d2 > d1 | `(n : ℕ)`, `hdim : topologicalKrullDimAt (s.asFiber (e u)) = (n : WithBot ℕ∞)` and `hdrop` asserting `dim G_u < n`. At a point local dimension is nonnegative, so representing the finite value by a natural number excludes no case. |
| Existence of an affine B and lfp immersion g | `∃ (B : Scheme.{u}) (g : B ⟶ U) (b : B), IsAffine B ∧ IsImmersion g ∧ LocallyOfFinitePresentation g ∧ ...`. Its canonical S-structure is `g ≫ p`. |
| g(b) = u and the induced residue map is an isomorphism | `g b = u ∧ IsIso (g.residueFieldMap b)`. The latter's source is κ(g(b)); the preceding equality identifies it with κ(u), so this is the specified canonical residue map. |
| h = s composed with the R-projection | Every occurrence is exactly `pullback.snd g t ≫ s`, on `B ×_{g,U,t} R`. |
| x is (b,e(u)) | `∃ x : (pullback g t : Scheme.{u})` with both projection equations. Since g is an immersion, its base change `pullback.snd g t` is an immersion, hence injective on points; these equations determine x uniquely. Its existence is the existence of the specified identity point, not a choice of a different lift. |
| h is Cohen-Macaulay at x | `(h.stalkMap x).hom.Flat`, `IsNoetherianRing` of `(h.fiber (h x)).presheaf.stalk (h.asFiber x)`, and equality of its depth with `ringKrullDim`, all expanded in the signature. The point equations and source identity give h(x)=u. No global flatness of h is asserted. |
| Restricted groupoid R_B and its source | `pullback (pullback.snd g t ≫ s) g`, with source `pullback.snd (pullback.snd g t ≫ s) g`, is precisely `(B ×_{g,U,t} R) ×_{s,U,g} B`, with source the last projection. |
| Identity point e_B(b) in the source fibre | `z` belongs to that source morphism's `fiber b`; its fibre projection followed by the first projection to `B ×_U R` equals x. Its last B-coordinate is b by fibre membership, and its first two coordinates are b,e(u) by the x equations. The first projection of R_B is a base change of the immersion g and the fibre inclusion is an embedding, so z is unique and is the required identity point. |
| Dimension decreases by one | `topologicalKrullDimAt z = ((n - 1 : ℕ) : WithBot ℕ∞)`. The stabilizer is nonempty (its identity point), so `hdrop` forces n ≥ 1; natural subtraction therefore agrees exactly with d2-1. |

All type, universe and object variables are explicitly bound; `autoImplicit` is false.
There is no local notation, local instance, `let`, hidden `show` term or data chosen
from a postponed existence assertion.

### Dependency declarations

The recorded statement dependencies are used as follows. I read the definitions
and their docstrings in their recorded modules, rather than inferring their
interfaces from the DAG names.

| Dependency | Recorded module and declarations used |
| --- | --- |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`. |
| def-weil-size-convention | Metatheoretic convention, with no declaration; implemented by explicit universes. |
| def-a1-groupoid-scheme | `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`. |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, `Flat.iff_flat_stalkMap`; pointwise conclusion uses `RingHom.Flat` on the canonical stalk map. |
| def-pc-scheme-fibre | `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber` and the `fiberHomeo` underlying it. |
| def-weil-pbc-noetherian-ring | `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`. |
| def-weil-pbc-depth | `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth`, the specialization of `Ideal.depth`. |
| def-weil-pbc-krull-dimension-ring | `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`. |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`. |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, used in the canonical residue-field map and fibres; `IsAffine` is Mathlib's affine-scheme condition. |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.fromSpecResidueField`, `Scheme.Hom.residueFieldMap`. |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`. |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.lift`, `pullback.fst`, `pullback.snd`, instantiated in schemes. |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`. |
| def-kun-topological-dimension-at-point | `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`. |
| def-weil-closed-immersion | The node also records immersions through its Mathlib match; `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`, equivalent to a closed immersion followed by an open immersion. |

Proof-only imports include the published modules for the fibre-stalk quotient,
finite-type dimension formula, scheme-to-algebraic-space construction, field-groupoid
stabilizer dimension, associated-prime finiteness, prime avoidance, the depth bound
at associated primes, the nonzerodivisor quotient and the depth-support bound.
Finite-type base change, affine pullbacks and finite-presentation composition
are supplied by Mathlib imports. The three proof-only nodes
`lem-sfb-finite-type-field-point-characterization`,
`lem-sfb-field-groupoid-constant-local-dimension` and
`lem-sfb-scheme-fibre-regular-slice-flat` currently have no recorded Lean module;
they remain named in the proof docstring and no unavailable import is invented.
No statement dependency required a new node or a dependency repair.

### Edge cases checked before writing

- Empty U has no u, so the point binder handles that case without adding nonemptiness
  hypotheses. A nonempty U in a groupoid has identity arrows, so G_u is nonempty.
- For n=0, dim G_u ≥ 0 rules out `hdrop`. For n=1 the output dimension is exactly zero.
  No arbitrary positivity assumption was added, and no infinite dimension was truncated.
- A group scheme over a point has d1=d2, so the strict-inequality antecedent is false.
  For the pair groupoid of affine n-space at a closed rational point, d1=0 and d2=n;
  the familiar hyperplane through that point has the required n-1 fibre dimension.
- No Noetherian condition is imposed on S,U,R; only the fibre stalks are required
  Noetherian. Nonreduced fibres and positive-characteristic fields are allowed.
- The residue-field isomorphism uses the induced map, not an unrelated isomorphism.
  The field need not be algebraically closed and no separability is assumed.
- The x and z equations specify unique identity points because the slice morphism
  is an immersion, so existentially displaying the points does not weaken the result.
- Topological dimension is used for G_u and the two fibre dimensions, and local-ring
  Krull dimension only for the depth equalities. These notions were not interchanged.

### Searches for an existing statement

- `msearch.py`, LeanFinder: “Cohen Macaulay groupoid schemes admit a hypersurface slice
  decreasing the dimension of the source fibre at the identity”. Eight hits concerned
  standard smooth algebras and smooth relative-dimension charts; none states this result.
- `msearch.py`, Loogle: `"CohenMacaulay"`. Zero hits.
- `msearch.py`, grep, Mathlib AlgebraicGeometry: `Cohen.?Macaulay|groupoid.*slice`.
  Zero hits.
- `msearch.py`, LeanSearch: “A Cohen Macaulay groupoid scheme admits an affine immersed
  slice lowering the dimension of its source fibre at the identity by one”. Eight hits
  concerning immersions, affine schemes and smoothness; none states the groupoid slice.
- `rg` in the project's `WeilConjectures` and `Sheaf` and upstream-name index for
  `exists_cm_groupoid_hypersurface_slice|lem-sfb-cm-groupoid-hypersurface-slice|groupoid.*slice|slice.*groupoid`:
  no hits. Broader Cohen-Macaulay searches found the fibre locus, field-extension and
  closed-point quasi-finite slice results, but none is the groupoid hypersurface slice.
- Read `Sheaf.AlgebraicGeometry.GroupoidScheme` and the recorded dimension/depth
  modules; these supply the definitions used here, not an existing theorem.

No STATEMENT-DISPUTED flag or statement correction is needed. The previous stage-1
refusal is not a stage-2 fault under the current handoff rule.

### Validation

Validation is through the prescribed server `scompile.py` and `deliver2.py` wrappers
only; no library build or direct repository/Git mutation is performed. The first
compile diagnosed missing scheme type annotations on pullbacks in sort positions;
these were repaired by explicit `: Scheme.{u}` annotations. The node signature is
regenerated verbatim from the final theorem header.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
