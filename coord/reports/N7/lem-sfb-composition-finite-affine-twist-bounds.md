## Worker report

The module `Sheaf.AlgebraicGeometry.CompositionFiniteAffineTwistBounds` states
`AlgebraicGeometry.Scheme.Modules.exists_finite_affine_cover_eventually_isAmple_tensorPullback`.
Its only proof is `sorry`, as required for stage 2. No definitions or dependency repairs
are needed. The node copy changes only `lean`.

Hypotheses and objects, clause by clause:

- Schemes and their named morphisms are `{X Y S : Scheme.{u}}`, `f : X ⟶ Y`,
  and `g : Y ⟶ S`, with the universe explicitly bound and arbitrary.
- Finite type of each map is exactly `[LocallyOfFiniteType f] [QuasiCompact f]`
  and `[LocallyOfFiniteType g] [QuasiCompact g]`, per the recorded dependency.
- Quasi-compactness of the base is `[CompactSpace S]`; no separation assumption is added.
- The specified modules are `L : X.Modules` and `M : Y.Modules`, with
  `[L.IsInvertible] [M.IsInvertible]`.
- `hL` quantifies over every `W : Y.Opens` with `IsAffineOpen W` and asserts
  `IsAmple` of `(tensorPullback (f ⁻¹ᵁ W).ι).obj L` on `(f ⁻¹ᵁ W).toScheme`.
- `hM` quantifies over every affine `V : S.Opens` and asserts `IsAmple` of
  `(tensorPullback (g ⁻¹ᵁ V).ι).obj M` on `(g ⁻¹ᵁ V).toScheme`.
- These ampleness statements carry existential proofs of invertibility because the
  recorded `IsAmple` takes invertibility as a proof parameter. This is precisely the
  encoding of the recorded relative-ample-absolute-twist dependency; no module data
  are chosen, and proof irrelevance makes the particular proof immaterial.

Conclusions, clause by clause:

- The first two conjuncts are `LocallyOfFiniteType (f ≫ g)` and
  `QuasiCompact (f ≫ g)`, exactly finite type and quasi-compactness of `h`.
- `∃ (r : ℕ) (V : Fin r → S.Opens)` gives a finite numbered family, allowing `r = 0`.
  `∀ i, IsAffineOpen (V i)` gives its affineness; `(⨆ i, V i) = ⊤` gives coverage.
- For each `i`, `Y_i` is the actual open subscheme `(g ⁻¹ᵁ V i).toScheme`;
  `X_i` is `(f ⁻¹ᵁ (g ⁻¹ᵁ V i)).toScheme`. Its underlying open is exactly
  `((f ≫ g) ⁻¹ᵁ V i)` by inverse images of a composite. Thus this is the specified
  canonical source, rather than an arbitrary scheme with a map to it.
- `f ∣_ (g ⁻¹ᵁ V i)` is Mathlib's canonical restricted morphism from `X_i` to `Y_i`.
  The next two conjuncts give its local finite type and quasi-compactness.
- `((tensorPullback (f ⁻¹ᵁ (g ⁻¹ᵁ V i)).ι).obj L).IsInvertible` gives
  invertibility of the actual restriction `L_i`.
- `∃ hMi : ((tensorPullback (g ⁻¹ᵁ V i).ι).obj M).IsInvertible` gives invertibility
  of the actual restriction `M_i` and supplies the proof parameter for its ampleness.
- The subsequent `∀ W : (g ⁻¹ᵁ V i).toScheme.Opens, IsAffineOpen W → ...` asserts
  ampleness of the restriction of `L_i` along the inclusion of `f_i⁻¹(W)`.
- `@IsAmple (g ⁻¹ᵁ V i).toScheme ... hMi` asserts absolute ampleness of `M_i`.
- `∃ a₀ : ℤ, 0 ≤ a₀ ∧ ∀ a : ℤ, a₀ ≤ a → ...` is the requested nonnegative
  integer bound and the entire eventual tail, including its endpoint.
- Its final `IsAmple` is on `X_i` for exactly
  `tensorObj L_i ((tensorPullback f_i).obj (M_i.tensorPow a.toNat))`.
  Under `0 ≤ a₀ ≤ a`, conversion by `a.toNat` is exact. The existing `tensorPow`
  has zeroth power the tensor unit, which is the structure module. The existential
  invertibility proof there expresses that the ample twist is invertible.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; composition and base-change instances
  `locallyOfFiniteType_comp` and `locallyOfFiniteType_isStableUnderBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`, `quasiCompact_comp`,
  `quasiCompact_isStableUnderBaseChange`, and
  `isCompact_iff_finite_and_eq_biUnion_affineOpens` for the proof plan's finite cover.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through the imports).
- `Mathlib.AlgebraicGeometry.Restrict`: `AlgebraicGeometry.morphismRestrict`,
  its global notation `∣_`, and `isPullback_morphismRestrict`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorObj`, `tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and its nonvanishing-locus definition.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded public
  interface, retaining `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. Its full tensor construction and
  the normalized adjunction signature were read; restrictions use this tensor pullback.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor dependency, retaining the existing sheaf tensor without a second construction.
- Proof-only import `Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist`:
  `AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_tensorPow_of_relative`.
  Its complete signature and eight-step proof docstring were read. The present statement
  supplies precisely its hypotheses on each restricted piece.

Source checked: `literature/stacks-project/morphisms.tex`,
`lemma-ample-composition` (Tag 0C4K) and
`lemma-pullback-ample-tensor-relatively-ample` (Tag 0892(1)), lines 8829 onward.
The latter proof explicitly obtains all sufficiently large exponents. The former
uses a finite affine cover and applies that result on the inverse-image pieces.

Edge cases checked: empty `S` permits `r = 0` and all indexed clauses are vacuous;
empty `X` or `Y` imposes no nonemptiness restriction; empty inverse-image pieces
are permitted. Exponent zero is included if the bound is zero, using the existing
structure-module tensor unit. Negative exponents are not reached because the bound
is nonnegative. No Noetherian, separated, nonempty, or positive-cover-size hypothesis
has been introduced. The rank-one local-trivialization definition of invertibility
and proof-witness encoding of ampleness handle all these cases.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “For finite type morphisms with relatively ample
  invertible modules over a quasi compact base there is a finite affine cover with
  eventual local ample tensor twist bounds”. Eight hits, including
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact` and affine-cover constructions;
  none states the requested local ampleness bounds.
- `msearch.py ... loogle "IsAmple, tensorPow"`: zero hits; unknown identifier
  `IsAmple` in that search index.
- `msearch.py ... grep "Ample.*[Tt]wist|[Tt]wist.*[Aa]mple" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: “A finite affine cover of a quasi compact base gives
  local bounds for eventual ampleness of relatively ample line bundle twists”.
  Eight affine-cover/locality hits, no matching theorem.
- `rg -n` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `finite_affine.*[Tt]wist|[Tt]wist.*[Bb]ounds|isAmple_tensorPullback_tensorPow|` plus
  `[Aa]mple.*[Cc]omposition`: found the reusable absolute-twist theorem and the
  parent `exists_isAmple_on_affineOpens_comp`, neither of which supplies the finite-cover
  data and all the local conclusions of this item. Other twist hits concern weights.
- `grep -rn "lem-sfb-composition-finite-affine-twist-bounds" lean/WeilConjectures`:
  no hit. The chosen full declaration name also has no existing project/upstream hit.

Validation: `scompile.py N7 lem-sfb-composition-finite-affine-twist-bounds` compiled
this file separately in sandbox and library modes against the server's live published
library, with no errors or warnings (1.9 s and 2.1 s respectively).
No statement dispute or correction.

## Second reading by N7

I reread the node and compiled file clause by clause using the mapping above, checking
in particular that `L` and `M` remain fixed input modules, that the restrictions use
the recorded tensor pullback, and that the conclusion retains both the local relative
ampleness condition and the absolute ampleness tail. The canonical source is the
iterated inverse-image open and the canonical morphism is `morphismRestrict`; no extra
map or arbitrary restriction identification is a hypothesis. All integer quantifiers
and the zero-cover case are retained. No mismatch was found and no correction made.
This is the worker's reread; independent review is performed by the maintainer on the
delivery, as specified in the dispatch brief. No independent worker review is claimed.
