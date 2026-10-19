## Worker report

The module `lean/Sheaf/DeligneLaumon/Reduction/Composition.lean` states
`AlgebraicGeometry.WeilSheaf.reductionComposition` for the finite-map reduction.  It
imports the side-project declaration module
`WeilConjectures.DeligneLaumon.Reduction.FiniteMap`, whose canonical operations are
used in the conclusion.

The binders render the node statement as follows.  `k₀` is a finite field and `l` is a
prime different from its characteristic.  `C₀` and `C'₀` are schemes over
`Spec k₀`, with separated, quasi-compact, locally finite-type structure morphisms.
The typeclass binders
`SmoothOfRelativeDimension 1`, `GeometricallyConnected`, and `IsAffine C₀` render
smooth geometrically connected affine `C₀`; the corresponding smooth and
geometrically connected binders render `C'₀`.  `j : C₀ ⟶ C'₀` is an open immersion,
quasi-compact and over the base; `_hj : DenseRange j.base` renders that it is a
dense open, and `_hboundary : (Set.range j.base)ᶜ.Finite` renders the finite
complement.  `g : C'₀ ⟶ affineLine k₀` is finite and over the base.  The explicit
`_hgen` clause gives a dense open `U` on which `U.ι ≫ g` is étale, i.e. the
finite generically étale hypothesis.  `F : WeilSheaf k₀ l C₀`, together with
`_hF : F.IsLisse`, is the lisse Weil sheaf, and
`_hpure : F.IsPunctuallyPureOfWeight ι w` is punctual `ι`-purity of weight `w`.
The conclusion quantifies every `i : ℤ` and gives the canonical Frobenius-module
equivalence
`H_c^i(C₀,F) ≃ H_c^i(𝔸¹,g_*j_!F)` as
`Nonempty ((...).Equiv (...))`.  The project’s Weil-sheaf API represents the
node’s displayed derived comparison by this degreewise cohomology equivalence.

The proof is `sorry` as required for stage 2.  The imported canonical theorem has
exactly this cohomology comparison for arbitrary separated finite-type schemes,
quasi-compact open immersion, finite map, and Weil sheaf; the wrapper retains every
geometric hypothesis from the node while applying that theorem.  The proof docstring
records extension-by-zero, compact-support composition, properness of a finite map,
finite direct-image exactness, and passage to cohomology.

Dependencies used: `def-weil-ordinary-compact-cohomology` supplies the compactly
supported cohomology notation (via the published Weil-sheaf cohomology API), and
`def-weil-punctual-weights` supplies the punctual purity notion.  The direct-image
and extension-by-zero operations are the published declarations
`AlgebraicGeometry.WeilSheaf.lowerStar` and
`AlgebraicGeometry.WeilSheaf.extensionByZero`; their canonical comparison theorem is
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerStar_extensionByZero`
in `WeilConjectures.DeligneLaumon.Reduction.FiniteMap`.

Edge cases checked: `i` ranges over all integers (including negative degrees), the
finite boundary may be empty, and no nonemptiness of the boundary is assumed.  The
finite map may have degree zero on components only insofar as the stated `IsFinite`
hypothesis permits it; no surjectivity or separability assumption was added.  The
purity weight and embedding are retained even though the transport comparison does
not use them.

Searches for an existing exact declaration or duplicate notion were made with:

- `rg -n 'reduction|ReductionComposition|compact.*cohom|ordinaryCompact|punctually|IsPunctuallyPure|WeilSheaf' /home/ubuntu/weil-src-slopmaster2/WeilConjectures`:
  no matching reduction-composition theorem in the read-only slopmaster2 source;
  it did find the canonical weight and cohomology APIs.
- `rg -n 'nonempty_equiv_compactlySupportedCohomology_lowerStar_extensionByZero'`
  over the shared project: exact declaration found only in the side framework
  module `lean/WeilConjectures/DeligneLaumon/Reduction/FiniteMap.lean`; this is
  imported and reused.
- `rg -n 'Finite.*Complement|finite.*complement|GenericallyEtale|Generically.*Etale'`
  in Mathlib and the source: no generic-etale or finite-complement predicate was
  available under a reusable name, so the statement uses the source-level explicit
  dense-open/étale and finite-complement clauses.
- `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q76 lem-a1-reduction-composition leanfinder
  'finite-map compactly supported cohomology extension by zero'`: no exact Mathlib
  match; generic sheaf/direct-image results only.
- `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q76 lem-a1-reduction-composition loogle
  'compactlySupportedCohomology, lowerStar, extensionByZero'`: no exact Mathlib match.
- `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q76 lem-a1-reduction-composition grep
  'compactlySupportedCohomology|lowerStar|extensionByZero' Mathlib`: no matching
  cohomology-transport declaration in Mathlib.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q76

I reread the node and the complete module.  The source hypotheses map one by one:
finite-field coefficient data; smooth geometrically connected affine `C₀`; smooth
geometrically connected `C'₀`; dense open immersion `j` with finite complement;
finite generically étale `g`; and lisse punctual-pure `F`.  The conclusion keeps
all integer degrees and compares compactly supported cohomology with the canonical
`g_*j_!F` object on the affine line.  No hypothesis is silently used to change the
objects, and the unused geometric hypotheses are retained with underscore-prefixed
names solely to keep the compiler warning-free.  Local compilation with `lcompile.py`
completed successfully with no errors or warnings.

## Maintainer review fix (NT-cc reviewer, 2026-10-18)

The node's conclusion has two clauses: the derived comparison
`RΓ_c(C,F) ≃ RΓ_c(𝔸¹,K)` and, hence, `H_c^i(C,F) ≃ H_c^i(𝔸¹,K)` for all `i : ℤ`.
The delivered statement gave only the degreewise clause.  The fix adds the derived
clause as a first conjunct, using the project's `RΓ_c` construction underlying
`compactlySupportedCohomology`: an isomorphism of Weil complexes on `Spec k₀`
`(WeilComplex.derivedLowerShriek k₀ l (C₀ ↘ Spec k₀)).obj (toComplex.obj F) ≅
(WeilComplex.derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec k₀)).obj (toComplex.obj (g_*j_!F))`
(the node's `RΓ_c = Fib_s ∘ Ra_!`, `Fib_s` an equivalence; the Weil-complex
isomorphism is the Frobenius-compatible form, as the degreewise clause already is).
`attribute [local instance 1100] CategoryTheory.instOverClass` is added, as in the side
framework's `WeilConjectures.ZetaFunction.Weights`, so that `Spec k₀` is over itself by
the identity.  Hypotheses unchanged; proof still `sorry`.  Per-file compile with
`tools/nt_compile.py`: rc 0, no errors or warnings.
