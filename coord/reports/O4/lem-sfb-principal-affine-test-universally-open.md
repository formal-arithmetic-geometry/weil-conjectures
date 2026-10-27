## Worker report

The module `Sheaf.AlgebraicGeometry.PrincipalAffineTestUniversallyOpen` states
`AlgebraicGeometry.principalAffineTest_universallyOpen`, with one postponed proof and no
new definitions. The statement follows the node without correction. Source read:
`literature/stacks-project/more-morphisms.tex`, Tag 0F31,
`lemma-test-universally-open`, proof of (3) implies (1), affine localization and
principal-open basis reduction. The proof docstring carries all four DAG proof steps
and their cited nodes.

Hypothesis and clause correspondence:

- The ring map `φ : A → C` is represented by `(A C : Type u) [CommRing A]
  [CommRing C] [Algebra A C]`, with `φ = algebraMap A C`. An algebra structure on a
  commutative ring is exactly the data of this ring homomorphism, so this does not
  impose a restriction on `φ`.
- `f` is `Spec.map (CommRingCat.ofHom (algebraMap A C))`, using the recorded
  spectrum construction.
- Every commutative A-algebra is quantified as `(B : Type u) [CommRing B]
  [Algebra A B]`. The common universe is polymorphic and includes A, C, B and all
  schemes being considered; there is no smaller, independently quantified test universe.
- `D_B` is the existing `B ⊗[A] C` with its Mathlib commutative-ring instance.
  Its multiplication and unit are precisely `Algebra.TensorProduct.tmul_mul_tmul`
  and `Algebra.TensorProduct.one_def`. No tensor ring or multiplication is redefined.
- `j_B` is `Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C`, sending
  `b` to `b ⊗ₜ[A] 1`; `q_B` is its `Spec.map`.
- Hypothesis `h` quantifies over every such B and every `g : B ⊗[A] C` and asserts
  `IsOpen (q_B '' (PrimeSpectrum.basicOpen g : Set ...))`. `basicOpen g` consists
  exactly of primes not containing g. The carrier of `Spec` is definitionally the
  corresponding prime spectrum, so no comparison map is hidden.
- The first conclusion is `∀ B ... , IsOpenMap q_B`.
- The second conclusion is `UniversallyOpen f`, Mathlib's usual universal openness.
- Arbitrary scheme base change is spelled out by `T`, `a`, `P`, `p`, `q` and
  `IsPullback p q f a → IsOpenMap q`. This quantifies over any representative of
  the fibre product, in particular the chosen `pullback f a` with its projections.
  `IsPullback` expresses the node's defining equation P = X ×_S T, not an extra
  geometric assumption.
- An arbitrary affine open W with arbitrary specified coordinates is represented
  by `(W : T.Opens) (B : Type u) [CommRing B] [Algebra A B]
  (e : W.toScheme ≅ Spec (CommRingCat.of B))`. Having e already expresses affineness;
  no additional affineness hypothesis is needed. The equation
  `e.hom ≫ Spec.map (ofHom (algebraMap A B)) = W.ι ≫ a` means exactly that B has
  the A-algebra structure corresponding to the restriction of a in these coordinates.
  For every W and e the structure exists uniquely by the recorded spectrum
  full-faithfulness (`Spec.homEquiv`), so the conditional quantification drops no chart.
- The existential `i : pullback q W.ι ≅ Spec (of (B ⊗[A] C))` is the requested
  isomorphism P ×_T W to the tensor spectrum. The following morphism equality
  `i.hom ≫ q_B = pullback.snd q W.ι ≫ e.hom` makes it an isomorphism over W and
  identifies the projection with q_B.
- `IsOpenImmersion (pullback.fst q W.ι)` and
  `Set.range (pullback.fst q W.ι) = q ⁻¹' (W : Set T)` identify its canonical map
  to P with the open subscheme q⁻¹(W). This is the recorded open-immersion notion,
  so it includes the scheme structure, rather than merely a carrier bijection.
- For every `(O : P.Opens)`, the displayed equality states `q(O) ∩ W` equals the
  image under `W.ι ∘ e.inv ∘ q_B ∘ i.hom` of `(pullback.fst q W.ι) ⁻¹' O`.
  The latter preimage is exactly the restriction of O ∩ q⁻¹(W) to P ×_T W.
  This renders the node's formula with all identifications explicit and with both
  sides typed as subsets of T.
- The next `IsOpen` says that the image before applying `W.ι` is open in W;
  the final `IsOpen (q '' O ∩ W)` says it is open in T.
- There is no quasi-compactness, separation, Noetherian, finite-type or
  nonempty-scheme assumption.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; the coordinate
  interpretation uses `Spec.homEquiv` in `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with `TensorProduct.tmul`;
  `Mathlib.RingTheory.TensorProduct.Basic` gives the standard ring instance and
  `Algebra.TensorProduct.includeLeftRingHom`. This extends the same module tensor
  construction by its existing multiplication, not a replacement notion.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks. `IsPullback`
  allows their universal-property presentation, as allowed by STATE's cartesian-square
  convention.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, read with its full signature/docstring.

These dependencies are publicly available through the public Mathlib imports. Proof
nodes were also read: the principal-open basis in Prime.Topology; open pullback maps
and their ranges in Pullbacks/PullbackCarrier; `pullbackSpecIso` and its two projection
lemmas in Pullbacks; `Scheme.isBasis_affineOpens` in AffineScheme. Their modules are
available through imports. No dependency repair or missing notion was needed.

Edge cases checked before drafting: A, B or C may be zero rings; their spectra can be
empty. `g=0` gives the empty principal open and `g=1` the full spectrum. W, T, P and O
may be empty. For W empty the zero-ring chart is permitted. O=top and W=top require
no special hypotheses. Covers can be infinite; only arbitrary unions occur. No finite
presentation, flatness or nontrivial-ring assumptions appear. The formulas use images
of genuine scheme morphisms and respect arbitrary choices of affine coordinates and
fibre-product representatives.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder`: “An affine scheme morphism is universally open if
  images of principal opens after every affine tensor product base change are open”.
  Eight hits: `UniversallyOpen`, its defining equivalence and universal/base-change
  properties, `Scheme.Hom.isOpenMap`, and locality instances. None states the criterion
  or the affine-chart clauses.
- `msearch.py ... loogle`: `"UniversallyOpen", "basicOpen"`; zero hits.
- `msearch.py ... leansearch`: “Universal openness follows from open images of
  principal opens after every affine tensor base change”. Eight hits on the
  definition, constructor, recursor, equivalence, open-map consequence and open
  immersions; none states this result.
- `msearch.py ... grep`: `universallyOpen.*basic|basic.*universallyOpen|pullbackSpecIso`
  in `AlgebraicGeometry`; 25 hits, all on the existing tensor-pullback isomorphism and
  its applications. They supply ingredients, not the assembled result.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `universallyOpen.*basic|basic.*universallyOpen|principal.*universally|universally.*principal`
  returned no hits. Searching the item id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` also returned none. A broader principal-open search
  found unrelated localization/Čech statements and the sibling tensor-polynomial model,
  whose full statement was opened and differs from this universal-openness criterion.
- `rg` for `principalAffineTest_universallyOpen` in Mathlib, WeilConjectures and Sheaf
  found no pre-existing declaration.

Validation: `scompile.py O4 lem-sfb-principal-affine-test-universally-open` compiled the
module both in sandbox and library mode, cleanly, in 1.6 s and 1.5 s respectively.
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by O4

Author's second pass (no second agent was started, as required by the dispatcher;
the maintainer supplies independent review). Reopened the node and the complete
module and checked the correspondence above. In particular, checked that the tensor
order is B ⊗_A C, the ring inclusion is into the left factor, the pullback projection
is the second projection to W, and the image formula uses i.hom but e.inv. Checked
that the two openness clauses concern W and T separately and that the map to P is
both an open immersion and has exactly the required range. Checked that the chart
coordinate condition encodes the induced algebra structure and excludes no chosen
chart. The arbitrary-pullback presentation specializes to the node's chosen fibre
product and carries the same canonical map to P. No clause mismatch was found and
no statement change was needed. The theorem is the only declaration and its proof
is exactly `sorry`; all variables and the universe are explicitly bound.
