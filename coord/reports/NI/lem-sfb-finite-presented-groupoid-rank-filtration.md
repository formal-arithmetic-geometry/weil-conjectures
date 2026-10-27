## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePresentedGroupoidRankFiltration` states
`AlgebraicGeometry.groupoid_exists_finitePresentation_rank_filtration`, with `sorry`
as its entire proof. It adds no definitions. The accepted stage-1 split, statement,
source, dependencies, and eight-step proof are preserved; only `lean` is set.
The former unchanged-node stage-1 failure does not apply to this stage-2 packet.
No released repair note exists for this item.

The source was read in `literature/stacks-project/more-groupoids.tex`, the complete
proof of `lemma-finite-stratify` (Tag 0AB9), and the first proof paragraph of
`lemma-finite-flat-over-almost-dense-subscheme-addendum` (Tag 0ABB). The latter
explicitly states that the former filtration has finitely presented closed immersions.
There are no statement faults or STATEMENT-DISPUTED findings.

Hypothesis and conclusion correspondence:

- The schemes and the five structure maps are `{U R : Scheme.{u}}`, `s`, `t`, `e`,
  `i`, and `c : pullback s t ⟶ R`. `hG : IsGroupoidScheme s t e i c` is precisely
  the recorded groupoid interface; its full signature and all its laws were read.
- Finiteness of both projections is `[IsFinite s] [IsFinite t]`. Finite presentation
  is `[LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]` together
  with the quasi-compactness and quasi-separatedness already implied by finiteness
  (finite implies affine, hence quasi-compact and separated). Thus the full Stacks
  01TP convention is retained without imposing any property on `U`.
- The existential sequence of closed subschemes is `∃ J : ℕ → U.IdealSheafData`:
  `Z_n` is `(J n).subscheme`, with canonical closed immersion `(J n).subschemeι`.
  This is Mathlib's existing ideal/closed-subscheme correspondence, not a newly
  defined notion. `ker_subschemeι` recovers the ideal, and every closed immersion
  is recovered by its kernel, so the representation adds no restriction.
- `J 0 = ⊥` says `Z_0 = U` as a closed subscheme: the zero ideal gives the whole
  scheme. It does not identify a nonreduced scheme with its reduction.
- `Monotone J` says `Z_{n+1} ⊆ Z_n` as closed subschemes: the order on ideals is
  inclusion on every affine open, and `IdealSheafData.inclusion` reverses it.
- `(⋂ n : ℕ, ((J n).support : Set U)) = ∅` is the required empty intersection
  of the underlying closed sets. This is not an assertion of eventual global
  emptiness of the sequence.
- The universally quantified conjunction of `LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated` on `(J n).subschemeι` says exactly that
  every closed immersion in the sequence is of finite presentation.
- `(J n).comap s = (J n).comap t` is equality of the defining ideals of the two
  inverse-image closed subschemes. `IdealSheafData.comapIso` identifies their
  schemes with the two corresponding fibre products over `U`, compatibly with
  their inclusions into `R`. Equality is scheme-theoretic, not just topological.
- For every `n : ℕ`, the open
  `(J n).subschemeι ⁻¹ᵁ (J (n + 1)).support.compl` of `(J n).subscheme` has its
  existing `Scheme.Opens` scheme structure. Its inclusion followed by
  `(J n).subschemeι` is the structure map of `D_{n+1}` into `U`. The canonical
  `pullback.snd s` along precisely that map is asserted to be
  `IsFiniteLocallyFreeOfDegree (n + 1)`. Reindexing `r = n + 1` covers exactly
  every `r ≥ 1`, with `D_r = Z_{r-1} \ Z_r`; it imposes no degree-zero assertion.
- The universe `u` is explicit, every binder is bound, and no Noetherian,
  quasi-compactness, nonemptiness, reducedness, or flatness hypothesis on `U`
  has been introduced. There are no statement-local definitions or `let` binders.

Recorded statement dependency declarations used, read in their source files:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `def-weil-pbc-scheme-conventions` has a convention record, not a declaration:
  its full finite-presentation meaning is the conjunction of Mathlib's
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, including the canonical closed-immersion
  instance on `IdealSheafData.subschemeι`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the strata use the standard open restriction `Scheme.Opens.ι`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.snd`, available for schemes.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`, with the fibre-degree
  equality at every target point.
- Supporting existing Mathlib constructions are `Scheme.IdealSheafData`,
  `support`, `subscheme`, `subschemeι`, and `inclusion` from the ideal-sheaf basic
  and subscheme modules, and `comap` from `IdealSheaf.Functorial`. The latter
  defines the pullback ideal as the kernel of the pullback closed immersion.

Proof dependency imports follow the recorded modules where available:
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
(`Scheme.Modules.quasicoherent_finite_type_affine`),
`WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange`
(`Scheme.Modules.affinePushforward_baseChange` and its algebra clause),
`Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally`
(`Scheme.Modules.fitting_ideal_generate_locally`),
`Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum`
(`specMap_isFiniteLocallyFree_of_basis`),
`WeilConjectures.AlgebraicGeometry.FiniteAffineFibreSections`
(`Spec.exists_ringEquiv_stalk_tensorProduct_fiber`), and
`WeilConjectures.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover`
(`Scheme.Hom.isFiniteLocallyFreeOfDegree_of_etale_cover`). Mathlib proof leaves
include affine permanence (already available through the statement imports),
`LocallyOfFinitePresentation.finitePresentation_appLE` (already available),
`Module.FinitePresentation.of_finite_of_finitePresentation` (module
`Mathlib.RingTheory.Finiteness.ModuleFinitePresentation`), ordinary
`Module.FinitePresentation` (available through that module), and open-immersion
etaleness (`Mathlib.AlgebraicGeometry.Morphisms.Etale`).
The currently unrecorded proof nodes `lem-trf-fitting-ideal-sheaf-pullback`,
`lem-a1-groupoid-source-pullback-translation`,
`lem-sfb-bounded-generators-fitting-pullback-criterion`, and
`lem-trf-closed-immersion-finite-presentation-ideal` have no module to import;
they are named in the complete eight-step proof docstring. They are not notions
needed to type this statement, and no substitute theorem is introduced.

Edge cases checked mathematically before writing:

- Empty `U` and consequently empty `R`: the ideal representation and all
  universal clauses apply, including the degree assertion over empty strata.
- Identity groupoid: take `J 0 = 0` and `J n = 1` for `n ≥ 1`. Only the degree-one
  stratum is nonempty, confirming the index convention.
- Constant finite group of order `d > 0`: the jump at `J d` gives the whole
  base as the degree-`d` stratum and empty strata at the other indices.
- Nonreduced bases: ideals are not radicalized; equality of pulled-back ideals
  retains all nilpotents. Finite nonflat source maps remain allowed.
- Non-quasi-compact disjoint unions with unbounded finite ranks: indexing by all
  natural numbers and requiring only empty intersection permits this case.
- The initial index is zero, while the degree conclusion starts at one.

Searches for reuse, on 2026-10-23:

- `msearch.py leansearch`, query "A finite groupoid scheme admits an invariant
  closed rank filtration": 8 irrelevant matches (stable ideal filtrations,
  Artinian schemes, group rank, etc.); no scheme-groupoid rank-filtration theorem.
- `msearch.py leanfinder`, query "A finite finitely presented groupoid scheme has
  an invariant rank filtration by finitely presented closed subschemes with finite
  locally free degree r strata": 8 matches for finite morphisms, local finite
  presentation, and other foundations, but none for this theorem.
- `msearch.py loogle`, query `IsGroupoidScheme, IsFiniteLocallyFreeOfDegree`:
  zero matches; the service does not know the project's `IsGroupoidScheme`.
- `msearch.py grep`, query
  `groupoid.*filtration|rankFiltration|finite_stratify`, Mathlib subdirectory
  `AlgebraicGeometry`: zero matches.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, query
  `rankFiltration|rank_filtration|groupoid.*filtration` and the item id: no
  theorem for this filtration. The expected new declaration name was also
  searched in both roots and Mathlib, with no matches.
- File search for `Groupoid|RankFiltration` and reading
  `AffineGroupoidInvariantRankStrata.lean` found
  `affineGroupoid_exists_invariant_rank_strata`, but that theorem requires affine
  schemes and already finite locally free maps, and gives finitely many clopen
  strata. It is not this statement for arbitrary finite finitely presented maps.
  The DAG's `lem-sfb-finite-groupoid-invariant-rank-filtration` is the weaker
  0AB9 existential result; it does not assert finite presentation of the closed
  immersions. The reviewed split already distinguishes the two.

Validation: `scompile.py NI lem-sfb-finite-presented-groupoid-rank-filtration`
compiled this file in sandbox and module positions against the published live
library, cleanly. Expected postponed proof: only
`AlgebraicGeometry.groupoid_exists_finitePresentation_rank_filtration`.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
