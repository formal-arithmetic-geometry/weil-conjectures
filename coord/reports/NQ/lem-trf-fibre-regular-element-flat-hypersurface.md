# Stage-2 repair: lem-trf-fibre-regular-element-flat-hypersurface

Group NQ. Source read: Stacks Project, `more-morphisms.tex`, Tag 056Y,
`lemma-slice-given-element`, statement and complete proof.

## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.FibreRegularElementFlatHypersurface`
states `AlgebraicGeometry.exists_affine_flat_hypersurface_of_fiber_regular`.
Its only theorem proof is `sorry`. There are no new definitions, auxiliary
postponed theorems, new nodes, or dependency-module repairs.

The source additionally asserts that the hypersurface is an effective Cartier
divisor. The DAG source explicitly omits that assertion, and so does this
statement. No Noetherian, global-flatness, smoothness, dimension, or residue-field
finiteness hypothesis is added. The entire twelve-step current DAG proof plan
is in the theorem docstring, including descent of the chosen section and
flatness at the one initial point.

Each hypothesis and clause is rendered as follows:

| Node text | Lean |
| --- | --- |
| A morphism of schemes `f : X → S` | `{X S : Scheme.{u}} (f : X ⟶ S)` |
| Locally of finite presentation | `[LocallyOfFinitePresentation f]` |
| The point `x` and `s = f(x)` | `(x : X)` and the literal expression `f x` everywhere the image is needed |
| Flat at `x` | `(hflat : (f.stalkMap x).hom.Flat)`; this is flatness of the actual local-ring map, with no global `Flat f` assumption |
| A germ in the source stalk | `(h : X.presheaf.stalk x)` |
| In its maximal ideal | `(hh : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))` |
| Scheme-theoretic fibre and its point over `x` | `f.fiber (f x)` and `f.asFiber x` |
| The image of the chosen germ on the fibre | `(f.fiberStalkMap x).hom h`, the already recorded projection stalk map with source transported by `fiberι_asFiber` |
| Multiplication by that image is injective | `hregular : Function.Injective (fun z : (f.fiber (f x)).presheaf.stalk (f.asFiber x) ↦ (f.fiberStalkMap x).hom h * z)` |
| An affine open neighbourhood of `x` | `∃ (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U)` |
| The ring `B` and its element `a` | `B` is the canonical coordinate ring `Γ(X, U)` and `(a : Γ(X, U))` |
| Its germ is exactly the original `h` | `X.presheaf.germ U x hx a = h` |
| `D = Spec(B/(a))` and its inclusion | The source of `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))` is literally this spectrum; its target is `Spec Γ(X,U)`, identified with `U` by `hU.isoSpec` |
| Closed subscheme of `U` | The map is the canonical spectrum map of the surjection `Ideal.Quotient.mk`, so the closed-immersion property is inherent in this chosen construction, using the affine-quotient characterization of the dependency; it is not an arbitrary closed immersion or an abstract zero set |
| `D` contains `x` | `x ∈ Set.range (Spec.map (...) ≫ hU.fromSpec)` |
| Composite `D → U → X → S` is flat | `Flat (Spec.map (...) ≫ hU.fromSpec ≫ f)` |
| The same composite is locally of finite presentation | `LocallyOfFinitePresentation (Spec.map (...) ≫ hU.fromSpec ≫ f)` |

No existential is placed over an arbitrary map or algebra structure.
`IsAffineOpen.fromSpec` is the fixed affine-chart map; `Ideal.Quotient.mk` is the
fixed principal quotient map. The universe `u` is explicit, every variable is
bound, and `autoImplicit` is disabled. A single scheme universe is the standard
Mathlib scheme-category convention, not a restriction on geometric hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  morphisms, used for `def-pc-scheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the recorded declaration of
  `def-sbc-locally-finite-presentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`,
  `Flat.stalkMap`, and `Flat.iff_flat_stalkMap`. The recorded flatness notion is
  expressed pointwise in the hypothesis and globally in the conclusion.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`,
  and `fiberι_asFiber`, for `def-pc-scheme-fibre` and its canonical point.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, whose affine-quotient description is
  instantiated by the actual principal quotient spectrum map in the conclusion.
- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`:
  `AlgebraicGeometry.Scheme.Hom.fiberStalkMap` and
  `fiberStalkMap_surjective_ker_quotientEquiv`. I read the definition body,
  source docstrings, and full theorem signature. The actual canonical map, not
  an arbitrary isomorphism with a quotient, gives the image in the fibre.
  Its already landed owner, `lem-sbc-scheme-fibre-stalk-quotient`, is added to
  `stmt_deps`; it was already a proof dependency. No other dependency changes.

The proof-only imports include the recorded flat finite-presentation model,
open flat locus and regular-sequence flatness modules, and the Mathlib modules
for affine stalks, section vanishing, principal-open spectra, tensor-product
base change, finite-presentation stability, Noetherian finite-type algebras,
faithful flatness, and regular sequences. Their use is described step by step
in the theorem docstring. None is replaced by a private copy.

Edge cases checked: an empty `X` provides no `x`; a stalk at an actual point
and the fibre stalk at `f.asFiber x` are nonzero local rings. Thus the zero germ
cannot satisfy the injectivity hypothesis. The maximal-ideal hypothesis excludes
a unit and ensures the chosen hypersurface contains `x`. On a zero-dimensional
Artinian fibre there need be no such regular maximal-ideal element; the
hypotheses then correctly have no instance. Nilpotents, non-Noetherian bases,
and arbitrary residue-field extensions are allowed. No dimension bound or
irreducibility assumption is used. The coordinate ring cannot be the zero
ring on an affine neighbourhood containing the specified point. The conclusion
does not assert that `a` is globally regular or that the divisor is Cartier.

Searches actually run in this repair (the command log is `searches.jsonl`):

- `msearch.py`, LeanFinder: "A fibre nonzerodivisor germ of a flat locally
  finitely presented scheme morphism cuts out a flat hypersurface on an affine
  neighbourhood". Eight hits: affine/stalk flatness, standard smooth charts,
  `flat_iff`, and `Algebra.smoothLocus`; none states the requested quotient result.
- `msearch.py`, Loogle: `"Flat", "nonZeroDivisors"`. One hit,
  `Module.Flat.isSMulRegular_of_nonZeroDivisors`, which preserves regular scalars
  on an already flat module rather than proving quotient flatness.
- `msearch.py`, grep in Mathlib `AlgebraicGeometry`:
  `slice_given|flat.*nonzerodivisor|nonzerodivisor.*flat|quotient.*[Ff]lat`.
  Two hits, a constant-sheaf application and flat surjective morphisms being
  quotient maps. Neither is a principal quotient flatness statement.
- `msearch.py`, LeanSearch: "A fibrewise nonzero divisor germ in a flat finitely
  presented family cuts out a flat hypersurface locally". Eight hits concerning
  scalar regularity, flat stalks, free loci, and restriction of germs; no match.
- `rg` in the upstream `WeilConjectures`, this project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Tag 056Y, this node id,
  `slice_given_element`, and regular/flat fibre and hypersurface expressions.
  No exact statement was found. The upstream candidate
  `Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber` was read at
  `WeilConjectures/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:981` with
  its full preceding docstring and signature. It assumes local regular
  principality at every prime of the entire fibre and global algebra flatness;
  it is not an exact match for one prescribed germ at one point. The existing
  `Sheaf.AlgebraicGeometry.FibreCartierLocal` uses that stronger fibrewise
  hypothesis. The source node does not supply it, so neither is re-recorded.

No statement dispute or statement correction is required.

## Returned delivery repaired

The returned head is `caf8870bb16999b3640b525b2f85fa19368c447b`.
I read its commit, node and report directly from the repository's loose objects,
without a Git command or a repository mutation. Its commit title is
`Split lem-trf-fibre-regular-element-flat-hypersurface`: it is a stage-1 split,
with no `lean` record and no Lean module. Its report is also a stage-1 report.
Comparing its node with the current shared node showed only a `split_report`
difference; the statement, statement dependencies, proof and proof dependencies
are identical. The current node is therefore used as the base, retaining its
stage-1 ownership and review data.

The single returned issue says that the attempted `--apply-fixes` path
`coord/reports/NQ/lem-trf-fibre-regular-element-flat-hypersurface.md` is not an
allowed stage-2 fix, and also reports "no module". The sandbox initially
contained only `.brief2` through `.brief5`. This repair supplies a genuine
stage-2 packet: the theorem module under `lean/Sheaf/`, a current-base node copy
with its complete `lean` record, and this sandbox-root `report.md`, which
`deliver2.py` places at its prescribed report path. It does not pass a stage-1
report tree as a maintainer fix directory. A reviewer using `--apply-fixes`
would use `<item>.report.md` at that fix directory's root. The new packet is a
substantive repair, not a rebase or unchanged re-push of the stage-1 split.

## Validation

`scompile.py NQ lem-trf-fibre-regular-element-flat-hypersurface` on the delivered
module succeeded for both sandbox and library contexts, with no error or warning.
The theorem signature was checked byte-for-byte against `lean.statement`; all
Lean lines are at most 100 characters, and there is exactly one `sorry`, the
named theorem's proof. The required `deliver2.py --no-push` result follows.

`deliver2.py NQ lem-trf-fibre-regular-element-flat-hypersurface --no-push`
printed `OK (dry run): commit bee33b6bff passes the preflight and compiles;
nothing pushed`. Exactly the module, item's node, and report were staged.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
