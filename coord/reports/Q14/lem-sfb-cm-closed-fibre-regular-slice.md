## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayClosedFibreRegularSlice` states
`AlgebraicGeometry.exists_regular_flat_locallyQuasiFinite_slice_of_closed_fibre_depth_eq_ringKrullDim`.
Its only theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The node's statement, dependencies and proof are unchanged. Source read in full:
`literature/stacks-project/more-morphisms.tex`, Tag 0570, lemma-slice-CM,
including the induction proof (lines 6358–6438). The global-flat specialization is
exactly the node's source specialization. No source outside the provided local
literature is needed.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`; `u` is explicit
  and arbitrary. No Noetherianity, separation, quasi-compactness or characteristic
  hypothesis is imposed on either scheme.
- Flatness and local finite presentation: `[Flat f] [LocallyOfFinitePresentation f]`.
- Base point and actual fibre point: `(s : S) (x : f.fiber s)`.
- Closedness in the fibre, not in X: `hx : x ∈ closedPoints (f.fiber s)`.
- The ring R is the actual fibre local ring `(f.fiber s).presheaf.stalk x`.
  `[IsNoetherianRing ...]` gives precisely the stated ring Noetherianity.
- Cohen–Macaulay equality is `hdepth`: the recorded `IsLocalRing.depth` of that
  ring as a module over itself, coerced from `ℕ∞` to `WithBot ℕ∞`, equals
  `ringKrullDim` of the same ring. The coercion only aligns codomains; it adds
  no finiteness or dimension hypothesis. The stalk is already a local ring.
- Existence: `∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : (i ≫ f).fiber s)`.
- The morphism is an immersion: `IsImmersion i`. Mathlib's immersion is the
  factorization by a closed immersion followed by an open immersion in the
  recorded `def-weil-closed-immersion` statement. It does not demand that i
  itself be globally closed.
- The point lies above x: `i ((i ≫ f).fiberι s z) = f.fiberι s x` uses both
  actual fibre projections. These projections identify each fibre with the
  set-theoretic fibre; thus this is exactly the node's meaning of i(z)=x.
- Composite properties: `Flat (i ≫ f)`, `LocallyOfFinitePresentation (i ≫ f)`
  and `(i ≫ f).IsLocallyQuasiFinite`, using the recorded Stacks-sense predicate.
- Singleton fibre: `∀ z' : (i ≫ f).fiber s, z' = z`, together with the
  existential witness z, says exactly that the whole fibre has underlying set {z}.
- At every source point `t : Z`, `V : Z.Opens` and `t ∈ V` give Z'.
  `U : X.Opens` with `hU : IsAffineOpen U` is the required affine ambient open.
  Its coordinate ring A is the existing section ring `Γ(X, U)`; `hU.isoSpec`
  identifies U with Spec A. Choosing this canonical A loses no possible chart.
- `j : V.toScheme ⟶ U.toScheme`, `IsClosedImmersion j`, and
  `V.ι ≫ i = j ≫ U.ι` express the closed-then-open factorization of i restricted
  to Z', using the actual inclusions of both opens.
- `a : List Γ(X, U)` is an arbitrary finite list, with no fixed positive length;
  I is `Ideal.ofList a`. `RingTheory.Sequence.IsRegular Γ(X, U) a` asserts
  injectivity on all successive quotients and a nonzero final quotient.
- `eV : V.toScheme ≅ Spec (.of (Γ(X,U) ⧸ Ideal.ofList a))` is the desired quotient
  isomorphism. The final equation identifies the given map j, via `hU.isoSpec`,
  with `Spec.map` of the actual quotient homomorphism. Hence the isomorphism is
  over U, rather than merely an abstract isomorphism of schemes.
- The list is permitted to be empty: then `Ideal.ofList [] = 0`, the quotient
  chart is an isomorphism, and i restricted to V is an open immersion.

Dependency declarations used (their source signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec` and `Spec.map` (through the public geometry imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `Scheme.Hom.fiberι`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth` (and its defining
  `Ideal.depth`), exactly the dependency node's recorded upstream interface.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  publicly available through `Mathlib.AlgebraicGeometry.Morphisms.Immersion`,
  whose `IsImmersion` and factorization equivalence realize the immersion clause.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`; Mathlib's weaker bare predicate is not substituted.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and the canonical
  open inclusions, available through the public geometry imports.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.isoSpec`, already
  available through the public geometry imports.

Proof dependencies with modules already recorded are imported privately:
`WeilConjectures.Topology.PresheafModuleStalkFunctor`,
`Sheaf.RingTheory.FiberRegularSequenceNeighbourhood`, plus the available Mathlib
modules for finite presentations, transitivity of flatness, affine pullbacks,
flat localization, Krull height and basic-open localization. The four statement-only
proof prerequisites (regular-immersion composition, CM hypersurface dimension drop,
prescribed-germ flat affine chart and zero-dimensional open slice) currently have
neither a usable Lean record nor a Mathlib match, and are not needed to type this
statement; their proof steps remain fully documented, rather than being assumed as
additional hypotheses. No missing statement-level dependency was encountered.

Edge cases checked before writing:

- Empty X, empty S and empty fibre have no x binder, so the implication has no
  inappropriate nonempty assumption or demanded slice.
- Empty Z cannot be an output because z is supplied in its fibre.
- The local ring at a scheme point is nonzero, so dimension bottom (the zero-ring
  case of ringKrullDim) cannot yield a spurious Cohen–Macaulay point.
- Zero-dimensional CM points, open slices and the empty list are retained.
  A chart around t has nonzero coordinate and quotient rings, as required by
  the nonzero-quotient clause of IsRegular.
- Positive dimension, arbitrary characteristic, non-Noetherian bases and
  ambient schemes, and varying local regular-list lengths are all admitted.
- No property of unselected fibres is asserted beyond the stated global flat,
  local finite-presentation and local quasi-finiteness conclusions.

Searches for existing statements (2026-10-24):

1. `msearch.py ... leanfinder`: “A flat locally finitely presented scheme morphism
   has a flat locally quasi finite regular slice through a closed Cohen Macaulay
   fibre point”. Eight results: universally open flat lfp morphisms, Flat,
   standard smooth charts and smoothness interfaces; no regular-slice existence.
2. `msearch.py ... loogle`: `AlgebraicGeometry.Flat,
   AlgebraicGeometry.LocallyOfFinitePresentation`. Twelve results: universal
   openness, etale criteria, descent, smooth fibres, flat mono open immersion,
   rank and fppf facts; none asserts a regular slice.
3. `msearch.py ... leansearch`: “Flat locally finitely presented morphism admits
   a regular immersion with flat quasi finite singleton fibre through a closed
   Cohen Macaulay point”. Eight results: Flat, finite presentation, immersion
   quasi-finiteness and flat-mono facts; none matches.
4. `msearch.py ... grep` on Mathlib/AlgebraicGeometry:
   `slice.CM|CohenMacaulay|regularSlice|regular_slice`: zero results.
5. `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
   `slice.CM|cmClosedFibre|cm_closed_fibre|regular_slice|regularSlice|Cohen.Macaulay.*slice|slice.*Cohen.Macaulay`
   found `Sheaf.AlgebraicGeometry.Morphisms.CohenMacaulayClosedPointSlice`.
   Its full declaration was read: it explicitly forgets immersion regularity
   and does not even conclude IsImmersion. It cannot serve as an exact match.
6. A definition search for regular immersion found the upstream
   `AlgebraicGeometry.IsRegularImmersion`, whose full signature and docstring
   were read. It demands a globally closed immersion and fixed codimension;
   it does not express the node's general immersion, so no replacement predicate
   was defined. The local clause is written directly using the recorded notions.
7. Search of the item id in `lean/WeilConjectures` gave no match. Search of the
   proposed full theorem name in the source, Sheaf and
   `dag/lean_names_upstream.json` gave no match.

No statement dispute, correction, dependency repair or new definition node.
Server compilation through scompile.py passed without errors or non-sorry warnings.

## Second reading by Q14

A separate second pass by this worker reopened the node and the final module;
no independent agent was started, as the dispatch brief explicitly forbids that.
The maintainer's independent review remains the independent reading.

I checked the full node clause by clause against the signature: X,S,f and both
morphism hypotheses match; s and x live in the actual base and fibre; closedness
is in that fibre; Noetherianity and the depth/dimension equality concern its actual
stalk; Z,i,z are existential; i is an immersion; the point equation uses the fibre
projections; all three composite properties and the whole-fibre singleton clause
appear. For regularity, each t has a source open V and an affine target open U;
j is a closed immersion, the restriction equation uses the actual i, and the
quotient isomorphism is over U by the final equation. The list a may be empty
and its length varies with t. No hypothesis was added, no clause omitted, and
no regularity or point compatibility was replaced by an abstract existence claim.
The alternative chart convention A=Γ(X,U) is equivalent via hU.isoSpec, whose full
type was read. Rechecking the existing CM slice confirmed it omits regularity,
and rechecking the upstream regular-immersion class confirmed its extra global
closedness and fixed-length restrictions. No signature mismatch was found;
the final pass added the private Mathlib flat-transitivity proof import and
removed one stray leading space in the module documentation.
